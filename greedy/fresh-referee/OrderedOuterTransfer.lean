import OrderedBlockCuts
import ComparatorOuterSegments

/-!
Construct the two lists needed for an outer whole-block transfer from a
concrete ordered side state. Only the at-most-one straddling block is split;
all other blocks move or remain intact with their immutable histories.
-/
namespace GreedyMerge.OrderedBlocks

open GreedyMerge.Primitives (Entry)

/-- Records of a resolved block have the same side of the cut. -/
theorem cutPrefix_eq_of_resolved {goLeft : Bool} {cut : ℕ} {block : Frozen}
    (resolved : ¬ Straddles cut block) {first second : Entry}
    (firstMem : first ∈ block.members) (secondMem : second ∈ block.members) :
    cutPrefix goLeft cut first = cutPrefix goLeft cut second := by
  have same : first.key < cut ↔ second.key < cut := by
    constructor
    · intro before
      by_contra after
      exact resolved ⟨⟨first, firstMem, before⟩, ⟨second, secondMem, by omega⟩⟩
    · intro before
      by_contra after
      exact resolved ⟨⟨second, secondMem, before⟩, ⟨first, firstMem, by omega⟩⟩
  cases goLeft <;> simp only [cutPrefix, Bool.false_eq_true, ↓reduceIte]
  · simp only [same]
  · have same' : cut ≤ first.key ↔ cut ≤ second.key := by omega
    simp only [same']

def blockInside (goLeft : Bool) (cut : ℕ) (block : Frozen) : Bool :=
  block.members.all (cutPrefix goLeft cut)

theorem blockInside_members {goLeft : Bool} {cut : ℕ} {block : Frozen}
    (inside : blockInside goLeft cut block = true) :
    ∀ entry ∈ block.members, cutPrefix goLeft cut entry = true :=
  List.all_eq_true.mp inside

theorem blockOutside_members {goLeft : Bool} {cut : ℕ} {block : Frozen}
    (resolved : ¬ Straddles cut block) (outside : blockInside goLeft cut block = false) :
    ∀ entry ∈ block.members, cutPrefix goLeft cut entry = false := by
  obtain ⟨witness, witnessMem, witnessNot⟩ := List.all_eq_false.mp outside
  intro entry member
  rw [cutPrefix_eq_of_resolved resolved member witnessMem]
  cases value : cutPrefix goLeft cut witness <;> simp_all

theorem filter_cutPrefix_partition {goLeft : Bool} {cut : ℕ} {members : List Entry}
    (ordered : members.Pairwise (outward goLeft)) :
    members.filter (cutPrefix goLeft cut) ++
      members.filter (fun entry => !(cutPrefix goLeft cut entry)) = members := by
  induction members with
  | nil => rfl
  | cons first rest ih =>
      obtain ⟨headOrder, restOrder⟩ := List.pairwise_cons.mp ordered
      by_cases inside : cutPrefix goLeft cut first = true
      · simpa [List.filter_cons, inside] using congrArg (first :: ·) (ih restOrder)
      · have outside : cutPrefix goLeft cut first = false := by
          cases value : cutPrefix goLeft cut first <;> simp_all
        have restEmpty : rest.filter (cutPrefix goLeft cut) = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro entry member entryInside
          exact inside (cutPrefix_order (headOrder entry member) entryInside)
        simpa [List.filter_cons, outside, restEmpty] using congrArg (first :: ·) (ih restOrder)

theorem frozen_filter_inside (goLeft : Bool) (cut : ℕ) (blocks : List Frozen)
    (resolved : ∀ block ∈ blocks, ¬ Straddles cut block) :
    frozenEntries (blocks.filter (blockInside goLeft cut)) =
      (frozenEntries blocks).filter (cutPrefix goLeft cut) := by
  induction blocks with
  | nil => rfl
  | cons block rest ih =>
      have head := resolved block (by simp)
      have tail : ∀ other ∈ rest, ¬ Straddles cut other := fun other member => resolved other (by simp [member])
      cases inside : blockInside goLeft cut block with
      | false =>
          have headEmpty : block.members.filter (cutPrefix goLeft cut) = [] := by
            apply List.filter_eq_nil_iff.mpr
            intro entry member
            rw [blockOutside_members head inside entry member]
            simp
          simpa [List.filter_cons, inside, frozenEntries, headEmpty] using ih tail
      | true =>
          have headFull : block.members.filter (cutPrefix goLeft cut) = block.members :=
            List.filter_eq_self.mpr (blockInside_members inside)
          simpa [List.filter_cons, inside, frozenEntries, headFull] using
            congrArg (block.members ++ ·) (ih tail)

theorem frozen_filter_outside (goLeft : Bool) (cut : ℕ) (blocks : List Frozen)
    (resolved : ∀ block ∈ blocks, ¬ Straddles cut block) :
    frozenEntries (blocks.filter (fun block => !(blockInside goLeft cut block))) =
      (frozenEntries blocks).filter (fun entry => !(cutPrefix goLeft cut entry)) := by
  induction blocks with
  | nil => rfl
  | cons block rest ih =>
      have head := resolved block (by simp)
      have tail : ∀ other ∈ rest, ¬ Straddles cut other := fun other member => resolved other (by simp [member])
      cases inside : blockInside goLeft cut block with
      | false =>
          have headFull : block.members.filter (fun entry => !(cutPrefix goLeft cut entry)) = block.members := by
            apply List.filter_eq_self.mpr
            intro entry member
            simp [blockOutside_members head inside entry member]
          simpa [List.filter_cons, inside, frozenEntries, headFull] using
            congrArg (block.members ++ ·) (ih tail)
      | true =>
          have headEmpty : block.members.filter (fun entry => !(cutPrefix goLeft cut entry)) = [] := by
            apply List.filter_eq_nil_iff.mpr
            intro entry member
            simp [blockInside_members inside entry member]
          simpa [List.filter_cons, inside, frozenEntries, headEmpty] using ih tail

noncomputable def separateOuter (goLeft : Bool) (cut fresh : ℕ) (state : SideState) :
    List Frozen × List Frozen :=
  let pieces := cutList goLeft cut fresh state.shrinking
  (pieces.filter (blockInside goLeft cut), pieces.filter (fun block => !(blockInside goLeft cut block)))

/-- The computed retained/moved lists preserve the complete old flattened
side order. Empty shrinking blocks may be regrouped, but no Entry moves
relative to another Entry and no immutable historical field changes. -/
theorem separateOuter_entries {owner : ℕ} (goLeft : Bool) (cut fresh : ℕ) (state : SideState)
    (valid : Valid owner goLeft state) :
    frozenEntries (separateOuter goLeft cut fresh state).1 ++
      frozenEntries (separateOuter goLeft cut fresh state).2 = frozenEntries state.shrinking := by
  have ordered := (List.pairwise_append.mp valid.1).1
  have resolved := cutList_resolves goLeft cut fresh state.shrinking ordered
  have preserved := cutList_entries goLeft cut fresh state.shrinking
  have newOrder : (frozenEntries (cutList goLeft cut fresh state.shrinking)).Pairwise (outward goLeft) := by
    simpa only [preserved] using ordered
  dsimp [separateOuter]
  rw [frozen_filter_inside _ _ _ resolved, frozen_filter_outside _ _ _ resolved,
    filter_cutPrefix_partition newOrder, preserved]

theorem separateOuter_entries_filter {owner : ℕ} (goLeft : Bool) (cut fresh : ℕ)
    (state : SideState) (valid : Valid owner goLeft state) :
    frozenEntries (separateOuter goLeft cut fresh state).1 =
      (frozenEntries state.shrinking).filter (cutPrefix goLeft cut) ∧
    frozenEntries (separateOuter goLeft cut fresh state).2 =
      (frozenEntries state.shrinking).filter (fun entry => !(cutPrefix goLeft cut entry)) := by
  have resolved := cutList_resolves goLeft cut fresh state.shrinking
    (List.pairwise_append.mp valid.1).1
  dsimp [separateOuter]
  rw [frozen_filter_inside _ _ _ resolved, frozen_filter_outside _ _ _ resolved,
    cutList_entries]
  exact ⟨rfl, rfl⟩

theorem separateOuter_inside (goLeft : Bool) (cut fresh : ℕ) (state : SideState) :
    ∀ entry ∈ frozenEntries (separateOuter goLeft cut fresh state).1,
      cutPrefix goLeft cut entry = true := by
  intro entry member
  obtain ⟨block, blockMem, entryMem⟩ := List.mem_flatMap.mp member
  exact blockInside_members (List.mem_filter.mp blockMem).2 entry entryMem

theorem separateOuter_outside {owner : ℕ} (goLeft : Bool) (cut fresh : ℕ) (state : SideState)
    (valid : Valid owner goLeft state) :
    ∀ entry ∈ frozenEntries (separateOuter goLeft cut fresh state).2,
      cutPrefix goLeft cut entry = false := by
  intro entry member
  obtain ⟨block, blockMem, entryMem⟩ := List.mem_flatMap.mp member
  have inPieces := (List.mem_filter.mp blockMem).1
  have outside : blockInside goLeft cut block = false := by
    simpa using (List.mem_filter.mp blockMem).2
  have resolved := cutList_resolves goLeft cut fresh state.shrinking
    (List.pairwise_append.mp valid.1).1 block inPieces
  exact blockOutside_members resolved outside entry entryMem

theorem separateOuter_descends (goLeft : Bool) (cut fresh : ℕ) (state : SideState) :
    ∀ piece ∈ (separateOuter goLeft cut fresh state).1 ++ (separateOuter goLeft cut fresh state).2,
      ∃ original ∈ state.shrinking, Descends piece original := by
  intro piece member
  rcases List.mem_append.mp member with member | member
  · exact cutList_descends goLeft cut fresh state.shrinking piece (List.mem_filter.mp member).1
  · exact cutList_descends goLeft cut fresh state.shrinking piece (List.mem_filter.mp member).1

/-- A completed outer transfer is constructed, rather than requiring
arbitrary preselected source block lists as inputs. -/
noncomputable def moveOuter (goLeft : Bool) (cut fresh : ℕ)
    (source receiver : SideState) : SideState × SideState :=
  let parts := separateOuter goLeft cut fresh source
  transfer parts.1 parts.2 receiver.shrinking source.grower receiver.grower

theorem moveOuter_valid (sourceOwner receiverOwner : ℕ) (goLeft : Bool) (cut fresh : ℕ)
    (source receiver : SideState)
    (sourceValid : Valid sourceOwner goLeft source)
    (receiverValid : Valid receiverOwner goLeft receiver)
    (sourceEmpty : growerEntries source.grower = [])
    (receiverEmpty : growerEntries receiver.grower = [])
    (receiverOwnerInside : if goLeft then cut ≤ receiverOwner else receiverOwner < cut)
    (receiverInside : ∀ entry ∈ entries receiver, cutPrefix goLeft cut entry = true) :
    Valid sourceOwner goLeft (moveOuter goLeft cut fresh source receiver).1 ∧
    Valid receiverOwner goLeft (moveOuter goLeft cut fresh source receiver).2 := by
  let parts := separateOuter goLeft cut fresh source
  have splitEntries : entries ⟨parts.1 ++ parts.2, source.grower⟩ = entries source := by
    simp only [entries, frozenEntries_append]
    rw [separateOuter_entries goLeft cut fresh source sourceValid]
  have splitValid : Valid sourceOwner goLeft ⟨parts.1 ++ parts.2, source.grower⟩ := by
    exact ⟨by simpa only [splitEntries] using sourceValid.1,
      by simpa only [splitEntries] using sourceValid.2.1, sourceValid.2.2⟩
  apply transfer_valid sourceOwner receiverOwner goLeft parts.1 parts.2 receiver.shrinking
    source.grower receiver.grower sourceEmpty receiverEmpty splitValid receiverValid
  · intro entry member
    have outside := separateOuter_outside goLeft cut fresh source sourceValid entry member
    cases goLeft <;> simp_all [cutPrefix, onSide] <;> omega
  · intro inside insideMem outside outsideMem
    have hInside := receiverInside inside (List.mem_append_left _ insideMem)
    have hOutside := separateOuter_outside goLeft cut fresh source sourceValid outside outsideMem
    cases goLeft <;> simp_all [cutPrefix, outward] <;> omega

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical

/-- Actual junction endpoints determine the physical cut on each side. -/
def junctionCut (goLeft : Bool) (lo hi : ℕ) : ℕ :=
  if goLeft then 2*lo else 2*hi+1

/-- For an actual old/new junction owner change, the receiving side is
confined automatically. The local transfer-validity hypotheses are thus
derived from real canonical parents, not supplied as a block certificate. -/
theorem moveOuter_junction_valid {n lo hi treeDepth : ℕ}
    (oldSnap newSnap : Snapshot n) (tree : BST 0 n) (inner : BST lo hi)
    (occurrence : SubtreeAt inner treeDepth tree) (oldOwner newOwner : External n)
    (oldRoot : subtreeOwner oldSnap inner occurrence.bounds.2 = oldOwner)
    (newRoot : subtreeOwner newSnap inner occurrence.bounds.2 = newOwner)
    (different : oldOwner ≠ newOwner) (side : Bool) (fresh : ℕ)
    (source receiver : SideState)
    (sourceValid : Valid oldOwner.val side source)
    (receiverValid : Valid newOwner.val side receiver)
    (receiverSound : ParentSound oldSnap tree newOwner receiver)
    (sourceEmpty : growerEntries source.grower = [])
    (receiverEmpty : growerEntries receiver.grower = []) :
    Valid oldOwner.val side (moveOuter side (junctionCut side lo hi) fresh source receiver).1 ∧
    Valid newOwner.val side (moveOuter side (junctionCut side lo hi) fresh source receiver).2 := by
  have newMin := subtreeOwner_isMin newSnap inner occurrence.bounds.2
  rw [newRoot] at newMin
  have ownerLo : 2*lo ≤ newOwner.val := newMin.1
  have ownerHi : newOwner.val ≤ 2*hi := newMin.2.1
  apply moveOuter_valid oldOwner.val newOwner.val side (junctionCut side lo hi) fresh
    source receiver sourceValid receiverValid sourceEmpty receiverEmpty
  · cases side <;> simp only [junctionCut, Bool.false_eq_true, ↓reduceIte] <;> omega
  · intro entry member
    obtain ⟨record, sameKey, parent⟩ := receiverSound entry member
    have bounds := (ComparatorOuter.receiver_and_source_confined oldSnap newSnap tree inner
      occurrence oldOwner newOwner oldRoot newRoot different).1 record parent
    cases side <;> simp only [cutPrefix, junctionCut, Bool.false_eq_true, ↓reduceIte,
      decide_eq_true_eq] <;> omega

/-- Every record selected by the constructed outer-block splice really
changes parent from the old junction owner to the new one. -/
theorem moved_entry_actual_parent {n lo hi treeDepth a b rotationDepth : ℕ}
    {before after : BST 0 n} (step : KeyRotationAt a b rotationDepth before after)
    (tree : BST 0 n) (inner : BST lo hi) (occurrence : SubtreeAt inner treeDepth tree)
    (oldOwner newOwner : External n)
    (oldValue : oldOwner.val = 2*a+1) (newValue : newOwner.val = 2*b+1)
    (different : oldOwner ≠ newOwner)
    (oldRoot : subtreeOwner (Snapshot.ofTree before) inner occurrence.bounds.2 = oldOwner)
    (newRoot : subtreeOwner (Snapshot.ofTree after) inner occurrence.bounds.2 = newOwner)
    (side : Bool) (fresh : ℕ) (source : SideState)
    (valid : Valid oldOwner.val side source)
    (sound : ParentSound (Snapshot.ofTree before) tree oldOwner source)
    {entry : Entry}
    (member : entry ∈ frozenEntries (separateOuter side (junctionCut side lo hi) fresh source).2) :
    ∃ record : External n, record.val = entry.key ∧
      canonicalParent (Snapshot.ofTree after) tree record = some newOwner := by
  have partition := separateOuter_entries side (junctionCut side lo hi) fresh source valid
  have oldMember : entry ∈ entries source := by
    apply List.mem_append_left
    rw [←partition]
    exact List.mem_append_right _ member
  obtain ⟨record, sameKey, parent⟩ := sound entry oldMember
  refine ⟨record, sameKey, ?_⟩
  apply ComparatorOuter.outside_source_child_transfers step tree inner occurrence
    oldOwner newOwner record oldValue newValue different oldRoot newRoot parent
  have outside := separateOuter_outside side (junctionCut side lo hi) fresh source valid entry member
  cases side <;> simp only [cutPrefix, junctionCut, Bool.false_eq_true, ↓reduceIte,
    decide_eq_false_iff_not] at outside <;> omega

#print axioms separateOuter_entries
#print axioms separateOuter_descends
#print axioms moveOuter_valid
#print axioms moveOuter_junction_valid
#print axioms moved_entry_actual_parent

end GreedyMerge.OrderedBlocks
