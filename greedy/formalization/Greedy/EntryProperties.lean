import Greedy.SnapshotStructural
import Greedy.SnapshotPaid

/-! Entry predicates survive splits, conversions, and whole-block transfers.
This interface also transports current membership memories and provenance. -/

namespace Greedy.EntryProperties

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.ActualLinks
open GreedyMerge.HeapAllocation LabelSnapshots

def Held {n : ℕ} (property : Entry → ℕ → Prop) (states : States n) : Prop :=
  ∀ owner side entry creator, (entry, creator) ∈ tagged (states owner side) → property entry creator

variable {n : ℕ} {property : Entry → ℕ → Prop}

theorem tagged_entry (state : SideState) (entry : Entry) (creator : ℕ)
    (member : (entry, creator) ∈ tagged state) : entry ∈ entries state := by
  rcases tagged_cases _ _ _ member with ⟨block, blockMem, entryMem, _⟩ |
    ⟨grower, present, entryMem, _⟩
  · exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨block, blockMem, entryMem⟩)
  · exact List.mem_append_right _ (by simpa only [growerEntries, present] using entryMem)

theorem entry_tagged (state : SideState) (entry : Entry) (member : entry ∈ entries state) :
    ∃ creator, (entry, creator) ∈ tagged state := by
  rcases List.mem_append.mp member with frozen | growing
  · obtain ⟨block, blockMem, entryMem⟩ := List.mem_flatMap.mp frozen
    exact ⟨block.creator, tagged_frozen _ block blockMem entry entryMem⟩
  · cases present : state.grower with
    | none => simp [growerEntries, present] at growing
    | some grower =>
        exact ⟨grower.creator, tagged_growing _ grower present entry
          (by simpa only [growerEntries, present] using growing)⟩

theorem Held.mono {other : Entry → ℕ → Prop} {states : States n}
    (held : Held property states) (weaken : ∀ entry creator, property entry creator → other entry creator) :
    Held other states := fun owner side entry creator member => weaken entry creator (held owner side entry creator member)

theorem restorePort_property (snapshot : Splay.Rank.Snapshot n) (tree : BST 0 n) (names : PaidNames)
    (makeEntry : External n → Entry) (record : External n) (states : States n)
    (held : Held property states) (fresh : ∀ owner, property (makeEntry owner) owner.val) :
    Held property (restorePort snapshot tree names makeEntry record states).1 := by
  intro current side item creator member
  cases parent : canonicalParent snapshot tree record with
  | none => exact held current side item creator (by simpa [restorePort, parent] using member)
  | some owner =>
      simp only [restorePort, parent, replaceSide] at member
      split_ifs at member with selected
      · obtain ⟨sameOwner, sameSide⟩ := selected
        subst current
        subst side
        rcases tagged_installPaid owner.val _ _ _ _ _ _ _ item creator member with old | ⟨rfl, rfl⟩
        · exact held owner _ item creator (by simpa using old)
        · exact fresh owner
      · exact held current side item creator member

theorem Held.descendants {n : ℕ} {property : Entry → ℕ → Prop}
    {before after : States n} (snapshots : Held property before)
    (growers : ∀ owner side, (after owner side).grower = (before owner side).grower)
    (descendants : ∀ owner side block, block ∈ (after owner side).shrinking →
      ∃ oldOwner oldSide old, old ∈ (before oldOwner oldSide).shrinking ∧ Descends block old) :
    Held property after := by
  intro owner side entry creator member
  rcases tagged_cases _ _ _ member with ⟨block, blockMem, entryMem, creatorEq⟩ |
    ⟨grower, present, entryMem, creatorEq⟩
  · obtain ⟨oldOwner, oldSide, old, oldMem, descendant⟩ := descendants owner side block blockMem
    have same : old.creator = creator := descendant.2.1.symm.trans creatorEq
    rw [← same]
    exact snapshots oldOwner oldSide entry old.creator
      (tagged_frozen _ old oldMem entry (descendant.2.2.subset entryMem))
  · rw [growers] at present
    rw [← creatorEq]
    exact snapshots owner side entry grower.creator (tagged_growing _ grower present entry entryMem)

theorem convertHeap_property {n : ℕ} {property : Entry → ℕ → Prop}
    (rank : ℕ → ℕ) (selected : External n → Bool → Bool) (start : ℕ) (states : States n)
    (snapshots : Held property states) :
    Held property (convertHeap rank selected start states).1 := by
  intro owner side entry creator member
  rw [convertHeap_apply] at member
  split_ifs at member
  · exact snapshots owner side entry creator (by simpa using member)
  · exact snapshots owner side entry creator member

theorem linkState_property {n : ℕ} {property : Entry → ℕ → Prop}
    (states : States n) (source winner loser : External n) (sourceSide targetSide : Bool) (entry : Entry)
    (snapshots : Held property states) (creators : GrowthJournal.Creators states)
    (fresh : property entry winner.val) :
    Held property (linkState states source winner loser sourceSide targetSide entry) := by
  intro owner side item creator member
  unfold linkState at member
  split_ifs at member with target selected
  · rcases tagged_append owner.val entry (states owner side) (creators owner side) item creator member with old | ⟨rfl, rfl⟩
    · exact snapshots owner side item creator old
    · simpa only [target.1] using fresh
  · exact snapshots owner side item creator (tagged_erase loser.val _ _ _ member)
  · exact snapshots owner side item creator member

theorem detachAll_property (before : BST 0 n) (key start : ℕ) (states : HeapSides n)
    (snapshots : Held property states) :
    Held property (detachAll before key (conversionNames start) (conversionNames start) states) := by
  have converted := convertHeap_property before.externalDepth
    (fun owner side => growerHasKey key (states owner side)) start states snapshots
  intro owner side entry creator member
  have equal : detachAll before key (conversionNames start) (conversionNames start) states owner side =
      eraseFrozenKey key ((convertHeap before.externalDepth
        (fun owner side => growerHasKey key (states owner side)) start states).1 owner side) := by
    rw [convertHeap_apply]
    rfl
  rw [equal] at member
  exact converted owner side entry creator (tagged_erase key _ _ _ member)

theorem detachPorts_property (before : BST 0 n) (start : ℕ) (ports : List ℕ) (stage : ℕ)
    (states : HeapSides n) (snapshots : Held property states) :
    Held property (detachPorts before (sequenceNames start) (sequenceNames start) ports stage states).1 := by
  induction ports generalizing stage states with
  | nil => exact snapshots
  | cons key rest ih =>
      apply ih (stage+1)
      exact detachAll_property before key (start + Fintype.card (Place n)*stage) states snapshots

theorem allocateCuts_property (cuts : List (ℕ × ℕ)) (start : ℕ) (states : HeapSides n)
    (snapshots : Held property states) :
    Held property (allocateCuts cuts start states).states := by
  apply snapshots.descendants (after := (allocateCuts cuts start states).states)
    (GrowthJournal.allocateCuts_grower cuts start states)
  intro owner side block member
  have exactState := congrArg Prod.fst (allocateCuts_eq cuts start states)
  dsimp only at exactState
  rw [← exactState] at member
  obtain ⟨old, oldMem, descendant⟩ := prepareCuts_descends (allocateCuts cuts start states).names cuts 0 states owner side block member
  exact ⟨owner, side, old, oldMem, descendant⟩

theorem rebase_property (before after : BST 0 n) (states : HeapSides n)
    (snapshots : Held property states) : Held property (rebaseAll before after states) := by
  apply snapshots.descendants (after := rebaseAll before after states) (fun _ _ => rfl)
  intro owner side block member
  obtain ⟨old, oldMem, rfl⟩ := List.mem_map.mp member
  exact ⟨owner, side, old, oldMem, rfl, rfl, List.Sublist.refl _⟩

theorem junction_property (oldOwner newOwner : External n) (lo hi start : ℕ) (states : HeapSides n)
    (snapshots : Held property states) :
    Held property (allocateJunction oldOwner newOwner lo hi start states).states := by
  apply snapshots.descendants (GrowthJournal.junction_grower oldOwner newOwner lo hi start states)
  intro owner side block member
  rw [allocateJunction_eq] at member
  unfold moveJunction at member
  split_ifs at member with old new
  · obtain ⟨original, originalMem, descendant⟩ := separateOuter_descends side (junctionCut side lo hi) _
      (states oldOwner side) block (List.mem_append_left _ member)
    exact ⟨oldOwner, side, original, originalMem, descendant⟩
  · change block ∈ (states newOwner side).shrinking ++ _ at member
    rcases List.mem_append.mp member with previous | moved
    · exact ⟨newOwner, side, block, previous, descends_refl _⟩
    · obtain ⟨original, originalMem, descendant⟩ := separateOuter_descends side (junctionCut side lo hi) _
        (states oldOwner side) block (List.mem_append_right _ moved)
      exact ⟨oldOwner, side, original, originalMem, descendant⟩
  · exact ⟨owner, side, block, member, descends_refl _⟩

theorem preparation_property (before after : BST 0 n) (start : ℕ) (ports : List ℕ)
    (owners : Finset (External n)) (states : HeapSides n) (snapshots : Held property states) :
    Held property (preparedForCuts before after start ports owners states) := by
  classical
  have grown := convertHeap_property before.externalDepth
    (fun owner side => decide (GrowerMismatch before after owner (states owner side))) start states snapshots
  rw [← prepareAllGrowers_fresh_eq] at grown
  have removed := detachPorts_property before start ports 1 _ grown
  have sealed := convertHeap_property before.externalDepth (fun owner _ => decide (owner ∈ owners))
    (start + Fintype.card (Place n)*(ports.length+1)) _ removed
  rw [← sealOwners_fresh_eq] at sealed
  simpa only [preparedForCuts, sequenceNames, Nat.mul_zero, Nat.add_zero] using sealed

theorem allocated_preparation_property {depth : ℕ} {before after : BST 0 n}
    (profile : RotationCutProfile before after depth) (start : ℕ) (ports : List ℕ)
    (owners : Finset (External n)) (states : HeapSides n) (snapshots : Held property states) :
    Held property (allocateComparatorPreparation profile ports owners start states).states :=
  allocateCuts_property profile.entries _ _ (preparation_property before after start ports owners states snapshots)


end Greedy.EntryProperties
