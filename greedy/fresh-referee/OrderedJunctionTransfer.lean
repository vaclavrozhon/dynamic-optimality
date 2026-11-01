import OrderedComparatorPreparation
import OrderedOuterTransfer
import HeapBlockCoverage

/-!
Simultaneous concrete side-state updates for the unique comparator junction.
The paid ports have already been removed. The constructed bulk operation
preserves global side validity and realizes every remaining actual new
parent, using the concrete comparator rotation and separated junction.
-/
namespace GreedyMerge.OrderedBlocks

open GreedyMerge.Primitives (Entry)
open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical

noncomputable def junctionPorts {n : ℕ} (snapshot : Snapshot n) (node : AtNode n) : List ℕ :=
  [(node.branchMin snapshot .left).val, (node.branchMin snapshot .middle).val,
    (node.branchMin snapshot .right).val]

theorem branch_mem_junctionPorts {n : ℕ} (snapshot : Snapshot n) (node : AtNode n)
    (branch : TernaryBranch) : (node.branchMin snapshot branch).val ∈ junctionPorts snapshot node := by
  cases branch <;> simp [junctionPorts]

theorem junction_owner_keys_mem {n a b rotationDepth : ℕ} {before after : BST 0 n}
    (step : KeyRotationAt a b rotationDepth before after) (node : AtNode n)
    (separated : ComparatorOuter.Separated node (2*a+1) (2*b+1))
    (oldOwner newOwner : External n)
    (oldRoot : node.owner (Snapshot.ofTree before) = oldOwner)
    (newRoot : node.owner (Snapshot.ofTree after) = newOwner) :
    oldOwner.val ∈ junctionPorts (Snapshot.ofTree before) node ∧
    newOwner.val ∈ junctionPorts (Snapshot.ofTree before) node := by
  obtain ⟨⟨oldBranch, oldPort⟩, ⟨newBranch, newPort⟩⟩ :=
    ComparatorOuter.junction_owners_are_ports step node separated
  constructor
  · simpa only [oldPort, oldRoot] using branch_mem_junctionPorts (Snapshot.ofTree before) node oldBranch
  · simpa only [newPort, newRoot] using branch_mem_junctionPorts (Snapshot.ofTree before) node newBranch

noncomputable def moveJunction {n : ℕ} (oldOwner newOwner : External n) (lo hi : ℕ)
    (fresh : Bool → ℕ) (states : HeapSides n) : HeapSides n :=
  fun owner side =>
    if owner = oldOwner then
      (moveOuter side (junctionCut side lo hi) (fresh side) (states oldOwner side) (states newOwner side)).1
    else if owner = newOwner then
      (moveOuter side (junctionCut side lo hi) (fresh side) (states oldOwner side) (states newOwner side)).2
    else states owner side

noncomputable def junctionTransferBirths {n : ℕ} (oldOwner : External n) (lo hi : ℕ)
    (states : HeapSides n) : ℕ :=
  cutListBirths (junctionCut false lo hi) (states oldOwner false).shrinking +
    cutListBirths (junctionCut true lo hi) (states oldOwner true).shrinking

theorem junctionTransferBirths_le_four {n : ℕ} (oldOwner : External n) (lo hi : ℕ)
    (states : HeapSides n)
    (valid : ∀ side, Valid oldOwner.val side (states oldOwner side)) :
    junctionTransferBirths oldOwner lo hi states ≤ 4 := by
  have left := cutState_births_le_two false (junctionCut false lo hi) _ (valid false)
  have right := cutState_births_le_two true (junctionCut true lo hi) _ (valid true)
  unfold junctionTransferBirths
  omega

theorem moveJunction_valid {n lo hi treeDepth : ℕ}
    (oldSnap newSnap : Snapshot n) (tree : BST 0 n) (inner : BST lo hi)
    (occurrence : SubtreeAt inner treeDepth tree) (oldOwner newOwner : External n)
    (oldRoot : subtreeOwner oldSnap inner occurrence.bounds.2 = oldOwner)
    (newRoot : subtreeOwner newSnap inner occurrence.bounds.2 = newOwner)
    (different : oldOwner ≠ newOwner) (fresh : Bool → ℕ) (states : HeapSides n)
    (valid : ∀ owner side, Valid owner.val side (states owner side))
    (sound : ∀ owner side, ParentSound oldSnap tree owner (states owner side))
    (oldEmpty : ∀ side, growerEntries (states oldOwner side).grower = [])
    (newEmpty : ∀ side, growerEntries (states newOwner side).grower = []) :
    ∀ owner side, Valid owner.val side (moveJunction oldOwner newOwner lo hi fresh states owner side) := by
  intro owner side
  have localValid := moveOuter_junction_valid oldSnap newSnap tree inner occurrence oldOwner newOwner
    oldRoot newRoot different side (fresh side) (states oldOwner side) (states newOwner side)
    (valid oldOwner side) (valid newOwner side) (sound newOwner side) (oldEmpty side) (newEmpty side)
  unfold moveJunction
  split_ifs with old new
  · subst owner
    exact localValid.1
  · subst owner
    exact localValid.2
  · exact valid owner side

/-- The exact parent relation outside the paid ports is realized by the
constructed two outer-side moves. The new-parent assertion is derived from
actual rotation and junction theorems, not supplied by the state contract. -/
theorem moveJunction_sound {n a b rotationDepth treeDepth : ℕ} {before after : BST 0 n}
    (step : KeyRotationAt a b rotationDepth before after) (tree : BST 0 n) (node : AtNode n)
    (occurrence : SubtreeAt (.node node.left node.right) treeDepth tree)
    (separated : ComparatorOuter.Separated node (2*a+1) (2*b+1))
    (oldOwner newOwner : External n)
    (oldValue : oldOwner.val = 2*a+1) (newValue : newOwner.val = 2*b+1)
    (oldRoot : subtreeOwner (Snapshot.ofTree before) (.node node.left node.right) occurrence.bounds.2 = oldOwner)
    (newRoot : subtreeOwner (Snapshot.ofTree after) (.node node.left node.right) occurrence.bounds.2 = newOwner)
    (different : oldOwner ≠ newOwner) (fresh : Bool → ℕ) (states : HeapSides n)
    (valid : ∀ owner side, Valid owner.val side (states owner side))
    (sound : ∀ owner side, ParentSound (Snapshot.ofTree before) tree owner (states owner side))
    (avoids : ∀ owner side entry, entry ∈ entries (states owner side) →
      entry.key ∉ junctionPorts (Snapshot.ofTree before) node)
    (oldEmpty : ∀ side, growerEntries (states oldOwner side).grower = [])
    (newEmpty : ∀ side, growerEntries (states newOwner side).grower = []) :
    ∀ owner side, ParentSound (Snapshot.ofTree after) tree owner
      (moveJunction oldOwner newOwner node.lower node.upper fresh states owner side) := by
  have portKeys := junction_owner_keys_mem step node separated oldOwner newOwner oldRoot newRoot
  have nonports {owner : External n} {side : Bool} {entry : Entry}
      (member : entry ∈ entries (states owner side)) {record : External n}
      (sameKey : record.val = entry.key) :
      record.val ≠ 2*a+1 ∧ record.val ≠ 2*b+1 ∧
        ∀ branch, record ≠ node.branchMin (Snapshot.ofTree before) branch := by
    have excluded := avoids owner side entry member
    refine ⟨?_, ?_, ?_⟩
    · intro equal
      apply excluded
      simpa only [←sameKey, equal, oldValue] using portKeys.1
    · intro equal
      apply excluded
      simpa only [←sameKey, equal, newValue] using portKeys.2
    · intro branch equal
      apply excluded
      rw [←sameKey, equal]
      exact branch_mem_junctionPorts (Snapshot.ofTree before) node branch
  have stable {owner : External n} {side : Bool} {entry : Entry}
      (member : entry ∈ entries (states owner side)) (notSource : owner ≠ oldOwner) :
      ∃ record : External n, record.val = entry.key ∧
        canonicalParent (Snapshot.ofTree after) tree record = some owner := by
    obtain ⟨record, sameKey, parent⟩ := sound owner side entry member
    obtain ⟨notA, notB, _⟩ := nonports member sameKey
    obtain ⟨newParent, newEdge, unchanged | changed⟩ :=
      ComparatorHeap.nonport_parent_some step tree record owner parent notA notB
    · exact ⟨record, sameKey, by simpa only [unchanged] using newEdge⟩
    · exact False.elim (notSource (Fin.ext (changed.1.trans oldValue.symm)))
  intro owner side entry member
  by_cases isSource : owner = oldOwner
  · subst owner
    have innerMember : entry ∈ frozenEntries
        (separateOuter side (junctionCut side node.lower node.upper) (fresh side) (states oldOwner side)).1 := by
      simpa [moveJunction, moveOuter, transfer, entries, oldEmpty side] using member
    have partition := separateOuter_entries side (junctionCut side node.lower node.upper) (fresh side)
      (states oldOwner side) (valid oldOwner side)
    have originalMem : entry ∈ entries (states oldOwner side) := by
      apply List.mem_append_left
      rw [←partition]
      exact List.mem_append_left _ innerMember
    obtain ⟨record, sameKey, parent⟩ := sound oldOwner side entry originalMem
    obtain ⟨notA, notB, notPorts⟩ := nonports originalMem sameKey
    have prefixSide := separateOuter_inside side (junctionCut side node.lower node.upper) (fresh side)
      (states oldOwner side) entry innerMember
    have onSideFact := (valid oldOwner side).2.1 entry originalMem
    have oldMin := subtreeOwner_isMin (Snapshot.ofTree before) (.node node.left node.right) occurrence.bounds.2
    rw [oldRoot] at oldMin
    have oldLo : 2*node.lower ≤ oldOwner.val := oldMin.1
    have oldHi : oldOwner.val ≤ 2*node.upper := oldMin.2.1
    have inside : 2*node.lower ≤ record.val ∧ record.val ≤ 2*node.upper := by
      cases side <;> simp only [cutPrefix, junctionCut, onSide, Bool.false_eq_true,
        ↓reduceIte, decide_eq_true_eq] at prefixSide onSideFact <;> omega
    exact ⟨record, sameKey, (ComparatorOuter.inside_junction_nonport_preserved step tree node
      occurrence separated record inside.1 inside.2 notPorts notA notB).trans parent⟩
  · by_cases isReceiver : owner = newOwner
    · subst owner
      have choices : entry ∈ entries (states newOwner side) ∨ entry ∈ frozenEntries
          (separateOuter side (junctionCut side node.lower node.upper) (fresh side) (states oldOwner side)).2 := by
        simpa [moveJunction, isSource, moveOuter, transfer, entries, newEmpty side] using member
      rcases choices with previous | moved
      · exact stable previous different.symm
      · exact moved_entry_actual_parent step tree (.node node.left node.right) occurrence oldOwner newOwner
          oldValue newValue different oldRoot newRoot side (fresh side) (states oldOwner side)
          (valid oldOwner side) (sound oldOwner side) moved
    · have previous : entry ∈ entries (states owner side) := by
        simpa [moveJunction, isSource, isReceiver] using member
      exact stable previous isSource

/-- Whole-block relocation changes ownership but neither loses nor adds
a represented key. This is the global coverage bridge for bulk transfer. -/
theorem moveJunction_represented {n : ℕ} (oldOwner newOwner : External n) (lo hi : ℕ)
    (different : oldOwner ≠ newOwner) (fresh : Bool → ℕ) (states : HeapSides n)
    (valid : ∀ owner side, Valid owner.val side (states owner side))
    (oldEmpty : ∀ side, growerEntries (states oldOwner side).grower = [])
    (newEmpty : ∀ side, growerEntries (states newOwner side).grower = []) (key : ℕ) :
    BlockCoverage.Represented (moveJunction oldOwner newOwner lo hi fresh states) key ↔
      BlockCoverage.Represented states key := by
  have partition (side : Bool) := separateOuter_entries side (junctionCut side lo hi) (fresh side)
    (states oldOwner side) (valid oldOwner side)
  have sourceEntries (side : Bool) : entries (states oldOwner side) =
      frozenEntries (separateOuter side (junctionCut side lo hi) (fresh side) (states oldOwner side)).1 ++
      frozenEntries (separateOuter side (junctionCut side lo hi) (fresh side) (states oldOwner side)).2 := by
    simp only [entries, oldEmpty side, List.append_nil]
    exact (partition side).symm
  constructor
  · rintro ⟨owner, side, entry, member, equal⟩
    by_cases source : owner = oldOwner
    · subst owner
      have inside : entry ∈ frozenEntries
          (separateOuter side (junctionCut side lo hi) (fresh side) (states oldOwner side)).1 := by
        simpa [moveJunction, moveOuter, transfer, entries, oldEmpty side] using member
      refine ⟨oldOwner, side, entry, ?_, equal⟩
      rw [sourceEntries]
      exact List.mem_append_left _ inside
    · by_cases receiver : owner = newOwner
      · subst owner
        have choices : entry ∈ entries (states newOwner side) ∨ entry ∈ frozenEntries
            (separateOuter side (junctionCut side lo hi) (fresh side) (states oldOwner side)).2 := by
          simpa [moveJunction, source, moveOuter, transfer, entries, newEmpty side] using member
        rcases choices with previous | moved
        · exact ⟨newOwner, side, entry, previous, equal⟩
        · refine ⟨oldOwner, side, entry, ?_, equal⟩
          rw [sourceEntries]
          exact List.mem_append_right _ moved
      · exact ⟨owner, side, entry, by simpa [moveJunction, source, receiver] using member, equal⟩
  · rintro ⟨owner, side, entry, member, equal⟩
    by_cases source : owner = oldOwner
    · subst owner
      rw [sourceEntries] at member
      rcases List.mem_append.mp member with inside | moved
      · refine ⟨oldOwner, side, entry, ?_, equal⟩
        simpa [moveJunction, moveOuter, transfer, entries, oldEmpty side] using inside
      · refine ⟨newOwner, side, entry, ?_, equal⟩
        have target : entry ∈ frozenEntries (states newOwner side).shrinking ++
            frozenEntries (separateOuter side (junctionCut side lo hi) (fresh side) (states oldOwner side)).2 :=
          List.mem_append_right _ moved
        simpa [moveJunction, different.symm, moveOuter, transfer, entries, newEmpty side] using target
    · by_cases receiver : owner = newOwner
      · subst owner
        refine ⟨newOwner, side, entry, ?_, equal⟩
        have previous : entry ∈ frozenEntries (states newOwner side).shrinking := by
          simpa [entries, newEmpty side] using member
        have target : entry ∈ frozenEntries (states newOwner side).shrinking ++
            frozenEntries (separateOuter side (junctionCut side lo hi) (fresh side) (states oldOwner side)).2 :=
          List.mem_append_left _ previous
        simpa [moveJunction, different.symm, moveOuter, transfer, entries, newEmpty side] using target
      · exact ⟨owner, side, entry, by simpa [moveJunction, source, receiver] using member, equal⟩

#print axioms moveJunction_valid
#print axioms moveJunction_sound
#print axioms junctionTransferBirths_le_four
#print axioms moveJunction_represented

end GreedyMerge.OrderedBlocks
