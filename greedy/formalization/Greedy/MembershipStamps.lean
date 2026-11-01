import Greedy.EntryProperties

/-! Literal family and join tickets are preserved by structural block operations. -/

namespace Greedy.MembershipStamps

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.ActualLinks
open GreedyMerge.HeapAllocation

def tagged (state : SideState) : List (Entry × ℕ) :=
  state.shrinking.flatMap (fun block => block.members.map (fun entry => (entry, block.family))) ++
    state.grower.toList.flatMap (fun grower => grower.members.map (fun entry => (entry, grower.family)))

theorem tagged_entry (state : SideState) (entry : Entry) (family : ℕ)
    (member : (entry, family) ∈ tagged state) : entry ∈ entries state := by
  rcases List.mem_append.mp member with frozen | growing
  · obtain ⟨block, blockMem, mapped⟩ := List.mem_flatMap.mp frozen
    obtain ⟨item, itemMem, equal⟩ := List.mem_map.mp mapped
    have entryEq : item = entry := congrArg Prod.fst equal
    subst item
    exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨block, blockMem, itemMem⟩)
  · obtain ⟨grower, growerMem, mapped⟩ := List.mem_flatMap.mp growing
    obtain ⟨item, itemMem, equal⟩ := List.mem_map.mp mapped
    have entryEq : item = entry := congrArg Prod.fst equal
    subst item
    have present : state.grower = some grower := by simpa using growerMem
    apply List.mem_append_right
    simpa [growerEntries, present] using itemMem

theorem tagged_frozen (state : SideState) (block : Frozen) (blockMem : block ∈ state.shrinking)
    (entry : Entry) (member : entry ∈ block.members) : (entry, block.family) ∈ tagged state :=
  List.mem_append_left _ (List.mem_flatMap.mpr ⟨block, blockMem, List.mem_map.mpr ⟨entry, member, rfl⟩⟩)

theorem tagged_growing (state : SideState) (grower : Grower) (present : state.grower = some grower)
    (entry : Entry) (member : entry ∈ grower.members) : (entry, grower.family) ∈ tagged state :=
  List.mem_append_right _ (List.mem_flatMap.mpr
    ⟨grower, by simpa using present, List.mem_map.mpr ⟨entry, member, rfl⟩⟩)

theorem tagged_cases (state : SideState) (entry : Entry) (family : ℕ)
    (member : (entry, family) ∈ tagged state) :
    (∃ block ∈ state.shrinking, entry ∈ block.members ∧ block.family = family) ∨
    (∃ grower, state.grower = some grower ∧ entry ∈ grower.members ∧ grower.family = family) := by
  rcases List.mem_append.mp member with frozen | growing
  · obtain ⟨block, blockMem, mapped⟩ := List.mem_flatMap.mp frozen
    obtain ⟨item, itemMem, equal⟩ := List.mem_map.mp mapped
    have first : item = entry := congrArg Prod.fst equal
    exact Or.inl ⟨block, blockMem, first ▸ itemMem, congrArg Prod.snd equal⟩
  · obtain ⟨grower, growerMem, mapped⟩ := List.mem_flatMap.mp growing
    obtain ⟨item, itemMem, equal⟩ := List.mem_map.mp mapped
    have first : item = entry := congrArg Prod.fst equal
    exact Or.inr ⟨grower, by simpa using growerMem, first ▸ itemMem, congrArg Prod.snd equal⟩

@[simp] theorem tagged_convert (owner family id base : ℕ) (state : SideState) :
    tagged (convert owner family id base state) = tagged state := by
  cases present : state.grower with
  | none => simp [convert, present]
  | some grower =>
      by_cases empty : grower.members = []
      · simp [convert, present, empty]
      · simp [convert, present, empty, tagged, freeze, emptyGrower]

theorem tagged_descends {after before : Frozen} (descendant : Descends after before)
    (entry : Entry) (member : entry ∈ after.members) :
    entry ∈ before.members ∧ after.family = before.family :=
  ⟨descendant.2.2.subset member, descendant.1⟩

theorem tagged_erase (key : ℕ) (state : SideState) (entry : Entry) (family : ℕ)
    (member : (entry, family) ∈ tagged (eraseFrozenKey key state)) :
    (entry, family) ∈ tagged state := by
  rcases tagged_cases _ _ _ member with ⟨block, blockMem, entryMem, familyEq⟩ |
    ⟨grower, present, entryMem, familyEq⟩
  · obtain ⟨old, oldMem, rfl⟩ := List.mem_map.mp blockMem
    rw [← familyEq]
    exact tagged_frozen state old oldMem entry (List.mem_filter.mp entryMem).1
  · rw [← familyEq]
    exact tagged_growing state grower present entry entryMem


def Held {n : ℕ} (property : Entry → ℕ → Prop) (states : States n) : Prop :=
  ∀ owner side entry family, (entry, family) ∈ tagged (states owner side) → property entry family

variable {n : ℕ} {property : Entry → ℕ → Prop}

theorem Held.descendants {n : ℕ} {property : Entry → ℕ → Prop}
    {before after : States n} (snapshots : Held property before)
    (growers : ∀ owner side, (after owner side).grower = (before owner side).grower)
    (descendants : ∀ owner side block, block ∈ (after owner side).shrinking →
      ∃ oldOwner oldSide old, old ∈ (before oldOwner oldSide).shrinking ∧ Descends block old) :
    Held property after := by
  intro owner side entry family member
  rcases tagged_cases _ _ _ member with ⟨block, blockMem, entryMem, familyEq⟩ |
    ⟨grower, present, entryMem, familyEq⟩
  · obtain ⟨oldOwner, oldSide, old, oldMem, descendant⟩ := descendants owner side block blockMem
    have same : old.family = family := descendant.1.symm.trans familyEq
    rw [← same]
    exact snapshots oldOwner oldSide entry old.family
      (tagged_frozen _ old oldMem entry (descendant.2.2.subset entryMem))
  · rw [growers] at present
    rw [← familyEq]
    exact snapshots owner side entry grower.family (tagged_growing _ grower present entry entryMem)

theorem convertHeap_property {n : ℕ} {property : Entry → ℕ → Prop}
    (rank : ℕ → ℕ) (selected : External n → Bool → Bool) (start : ℕ) (states : States n)
    (snapshots : Held property states) :
    Held property (convertHeap rank selected start states).1 := by
  intro owner side entry family member
  rw [convertHeap_apply] at member
  split_ifs at member
  · exact snapshots owner side entry family (by simpa using member)
  · exact snapshots owner side entry family member

theorem detachAll_property (before : BST 0 n) (key start : ℕ) (states : HeapSides n)
    (snapshots : Held property states) :
    Held property (detachAll before key (conversionNames start) (conversionNames start) states) := by
  have converted := convertHeap_property before.externalDepth
    (fun owner side => growerHasKey key (states owner side)) start states snapshots
  intro owner side entry family member
  have equal : detachAll before key (conversionNames start) (conversionNames start) states owner side =
      eraseFrozenKey key ((convertHeap before.externalDepth
        (fun owner side => growerHasKey key (states owner side)) start states).1 owner side) := by
    rw [convertHeap_apply]
    rfl
  rw [equal] at member
  exact converted owner side entry family (tagged_erase key _ _ _ member)

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



end Greedy.MembershipStamps
