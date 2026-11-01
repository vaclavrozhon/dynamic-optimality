import Splay.Accounting.CanonicalSubtreeEdges

namespace Splay.Accounting

open Splay.Rank Splay.Tree Splay.Tree.BST Splay.Lazy Splay.Lazy.Canonical

/-- Moving an unchanged subtree to a new context cannot break an interval
whose children are all internal edges of that subtree. Any new edge owned
there but attached outside it lies strictly above the whole interval. -/
theorem canonicalBlockCrossSideUnbroken_of_shared_subtree
    {n innerLower innerUpper beforeDepth afterDepth : ℕ} (snapshot : Snapshot n)
    {inner : BST innerLower innerUpper} {before after : BST 0 n}
    (oldOccurrence : SubtreeAt inner beforeDepth before) (newOccurrence : SubtreeAt inner afterDepth after)
    (block : Block n) (unbroken : canonicalBlockCrossSideUnbroken snapshot before block)
    (localChildren : ∀ element ∈ block.elements,
      ∃ edge ∈ treeEdges snapshot inner oldOccurrence.bounds.2 0,
        edge.child = element ∧ edge.owner = block.owner) :
    canonicalBlockCrossSideUnbroken snapshot after block := by
  have oldSubset : ∀ edge ∈ treeEdges snapshot inner oldOccurrence.bounds.2 beforeDepth,
      edge ∈ fullEdges snapshot before := by
    simpa only [Nat.zero_add, fullEdges] using subtreeAt_treeEdges_subset oldOccurrence snapshot (Nat.le_refl n) 0
  have newSubset : ∀ edge ∈ treeEdges snapshot inner oldOccurrence.bounds.2 afterDepth,
      edge ∈ fullEdges snapshot after := by
    simpa only [Nat.zero_add, fullEdges] using subtreeAt_treeEdges_subset newOccurrence snapshot (Nat.le_refl n) 0
  have oldCore : EdgeBlockUnbroken (treeEdges snapshot inner oldOccurrence.bounds.2 beforeDepth) block :=
    ((edgeBlockUnbroken_iff_canonical snapshot before block).mpr unbroken).mono oldSubset
  have core : EdgeBlockUnbroken (treeEdges snapshot inner oldOccurrence.bounds.2 0) block := by
    apply EdgeBlockUnbroken.of_shift_depth beforeDepth
    rw [← treeEdges_shift_depth]
    simpa only [Nat.zero_add] using oldCore
  have newCore : EdgeBlockUnbroken (treeEdges snapshot inner oldOccurrence.bounds.2 afterDepth) block := by
    have shifted := core.shift_depth afterDepth
    rw [← treeEdges_shift_depth] at shifted
    simpa only [Nat.zero_add] using shifted
  have childrenInternal : ∀ edge ∈ fullEdges snapshot after, edge.child ∈ block.elements →
      edge ∈ treeEdges snapshot inner oldOccurrence.bounds.2 afterDepth := by
    intro edge member inside
    obtain ⟨old, oldMember, childEq, _ownerEq⟩ := localChildren edge.child inside
    have shiftedMember : shiftEdgeDepth afterDepth old ∈ treeEdges snapshot inner oldOccurrence.bounds.2 afterDepth := by
      rw [← Nat.zero_add afterDepth, treeEdges_shift_depth, Nat.zero_add]
      exact List.mem_map.mpr ⟨old, oldMember, rfl⟩
    have shiftedLookup := incomingEdge_eq_some_of_mem_fullEdges snapshot after (newSubset _ shiftedMember)
    have edgeLookup := incomingEdge_eq_some_of_mem_fullEdges snapshot after member
    change incomingEdge? snapshot after old.child = some (shiftEdgeDepth afterDepth old) at shiftedLookup
    rw [childEq] at shiftedLookup
    have equal : shiftEdgeDepth afterDepth old = edge := Option.some.inj (shiftedLookup.symm.trans edgeLookup)
    exact equal ▸ shiftedMember
  apply (edgeBlockUnbroken_iff_canonical snapshot after block).mp
  intro first firstMember firstIn last lastMember lastIn middle middleMember owner opposite between
  have firstLocal := childrenInternal first firstMember firstIn
  have lastLocal := childrenInternal last lastMember lastIn
  obtain ⟨old, oldMember, _, oldOwner⟩ := localChildren first.child firstIn
  have inside := mem_treeEdges_inside snapshot inner oldOccurrence.bounds.2 oldMember
  have ownerLow : 2 * innerLower ≤ middle.owner.val := by rw [owner, ← oldOwner]; exact inside.1
  have ownerHigh : middle.owner.val ≤ 2 * innerUpper := by rw [owner, ← oldOwner]; exact inside.2.1
  have middleCases := subtreeAt_edge_mem_or_above newOccurrence snapshot (Nat.le_refl n) 0 middleMember ownerLow ownerHigh
  simp only [Nat.zero_add] at middleCases
  rcases middleCases with internal | above
  · exact newCore first firstLocal firstIn last lastLocal lastIn middle internal owner opposite between
  · have firstDepth := JunctionBendReduction.treeEdge_depth_le snapshot inner oldOccurrence.bounds.2 afterDepth firstLocal
    have lastDepth := JunctionBendReduction.treeEdge_depth_le snapshot inner oldOccurrence.bounds.2 afterDepth lastLocal
    rcases between with ⟨ordered, _⟩ | ⟨ordered, _⟩ <;>
      rcases ordered with lower | ⟨equal, _, _⟩ <;> omega

end Splay.Accounting
