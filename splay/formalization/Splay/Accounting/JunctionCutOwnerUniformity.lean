import Splay.Accounting.JunctionCutRootOwner

namespace Splay.Accounting.JunctionBendReduction

open Splay.Rank Splay.Tree Splay.Lazy.Canonical

private theorem edge_owner_eq_of_local_reference {n lower root upper : ℕ}
    (before after : Snapshot n) (left : BST lower root) (right : BST (root + 1) upper)
    (upper_le_n : upper ≤ n) (depth : ℕ) {reference old next : Edge n}
    (localReference : reference ∈ edgesAtNode before ⟨lower, root, upper, left, right, upper_le_n⟩ depth)
    (oldMember : old ∈ treeEdges before (.node left right) upper_le_n depth)
    (nextMember : next ∈ treeEdges after (.node left right) upper_le_n depth)
    (sameAttachment : next.attachmentKey = old.attachmentKey)
    (sameOwner : old.owner = reference.owner)
    (sameCell : SameCutCell (junctionCutsFrom before after (.node left right) upper_le_n) reference.child old.child) :
    next.owner = AtNode.owner after ⟨lower, root, upper, left, right, upper_le_n⟩ := by
  classical
  let node : AtNode n := ⟨lower, root, upper, left, right, upper_le_n⟩
  have leftBound : root ≤ n := by have := right.lower_le_upper; omega
  have referenceValid := mem_edgesAtNode_valid before node depth localReference
  have oldOwner : old.owner = node.owner before := sameOwner.trans referenceValid.2.1
  have nextLocation := treeEdge_location_iff after left right upper_le_n depth nextMember
  have localCuts (junction : node.heavyBranch before ≠ node.heavyBranch after) :
      ({2 * lower, 2 * root + 1, 2 * root + 2, 2 * upper + 1} : Finset ℕ) ⊆
        junctionCutsFrom before after (.node left right) upper_le_n := by
    intro cut member
    apply Finset.mem_union_left
    apply Finset.mem_union_left
    change cut ∈ (if node.heavyBranch before = node.heavyBranch after then ∅ else _)
    rw [if_neg junction]
    exact member
  rcases List.mem_append.mp oldMember with localOrLeft | rightEdge
  · rcases List.mem_append.mp localOrLeft with localOld | leftEdge
    · have localNew := nextLocation.1.mpr (sameAttachment.trans (mem_edgesAtNode_attachmentKey before node depth localOld))
      exact (mem_edgesAtNode_valid after node depth localNew).2.1
    · have oldInside := mem_treeEdges_inside before left leftBound leftEdge
      have heavyLeft := node.heavyBranch_eq_left_of_owner_le_root before
        (by rw [← oldOwner]; exact oldInside.2.1)
      have referenceOutside := referenceValid.child_gt_root_of_heavy_left heavyLeft
      change 2 * root < reference.child.val at referenceOutside
      have sameBranch : node.heavyBranch before = node.heavyBranch after := by
        by_contra junction
        have separates := sameCell (2 * root + 1) (localCuts junction (by simp))
        have childUpper : old.child.val ≤ 2 * root := oldInside.2.2.2
        omega
      have oldRoot := node.owner_eq_branchMin_heavy before
      rw [heavyLeft] at oldRoot
      have newRoot := node.owner_eq_branchMin_heavy after
      rw [sameBranch.symm.trans heavyLeft] at newRoot
      have nextLeft := nextLocation.2.1.mpr (by
        rw [sameAttachment]
        exact (mem_treeEdges_attachmentKey_bounds before left leftBound leftEdge).2)
      have sameLeft : SameCutCell (junctionCutsFrom before after left leftBound) reference.child old.child :=
        sameCell.mono (by intro cut inside; exact Finset.mem_union_left _ (Finset.mem_union_right _ inside))
      exact (edge_owner_eq_subtreeOwner_of_sameCutCell_outside before after left leftBound (depth + 1)
        leftEdge nextLeft sameAttachment (oldOwner.trans oldRoot) (Or.inr referenceOutside) sameLeft).trans newRoot.symm
  · have oldInside := mem_treeEdges_inside before right upper_le_n rightEdge
    have heavyRight := node.heavyBranch_eq_right_of_root_lt_owner before
      (by rw [← oldOwner]; exact oldInside.1)
    have referenceOutside := referenceValid.child_lt_root_of_heavy_right heavyRight
    change reference.child.val < 2 * root + 2 at referenceOutside
    have sameBranch : node.heavyBranch before = node.heavyBranch after := by
      by_contra junction
      have separates := sameCell (2 * root + 2) (localCuts junction (by simp))
      have childLower : 2 * root + 2 ≤ old.child.val := oldInside.2.2.1
      omega
    have oldRoot := node.owner_eq_branchMin_heavy before
    rw [heavyRight] at oldRoot
    have newRoot := node.owner_eq_branchMin_heavy after
    rw [sameBranch.symm.trans heavyRight] at newRoot
    have nextRight := nextLocation.2.2.mpr (by
      rw [sameAttachment]
      have lowerBound := (mem_treeEdges_attachmentKey_bounds before right upper_le_n rightEdge).1
      omega)
    have sameRight : SameCutCell (junctionCutsFrom before after right upper_le_n) reference.child old.child :=
      sameCell.mono (by intro cut inside; exact Finset.mem_union_right _ inside)
    exact (edge_owner_eq_subtreeOwner_of_sameCutCell_outside before after right upper_le_n (depth + 1)
      rightEdge nextRight sameAttachment (oldOwner.trans oldRoot) (Or.inl referenceOutside) sameRight).trans newRoot.symm

/-- Between the four numerical cuts of each junction, all old children of
one owner have a common new owner, provided their attachment nodes persist.
This is the bounded-cut geometric fact needed for whole-block relocation. -/
theorem edge_owners_eq_of_sameCutCell {n lower upper : ℕ}
    (before after : Snapshot n) (tree : BST lower upper) (upper_le_n : upper ≤ n) (depth : ℕ)
    {first second firstNext secondNext : Edge n}
    (firstMember : first ∈ treeEdges before tree upper_le_n depth)
    (secondMember : second ∈ treeEdges before tree upper_le_n depth)
    (firstNextMember : firstNext ∈ treeEdges after tree upper_le_n depth)
    (secondNextMember : secondNext ∈ treeEdges after tree upper_le_n depth)
    (firstAttachment : firstNext.attachmentKey = first.attachmentKey)
    (secondAttachment : secondNext.attachmentKey = second.attachmentKey)
    (sameOwner : first.owner = second.owner)
    (sameCell : SameCutCell (junctionCutsFrom before after tree upper_le_n) first.child second.child) :
    firstNext.owner = secondNext.owner := by
  classical
  induction tree generalizing depth with
  | empty => simp [treeEdges] at firstMember
  | @node lower root upper left right ihLeft ihRight =>
      let node : AtNode n := ⟨lower, root, upper, left, right, upper_le_n⟩
      have leftBound : root ≤ n := by have := right.lower_le_upper; omega
      have firstLocation := treeEdge_location_iff after left right upper_le_n depth firstNextMember
      have secondLocation := treeEdge_location_iff after left right upper_le_n depth secondNextMember
      have localFirst (localEdge : first ∈ edgesAtNode before node depth) : firstNext.owner = node.owner after :=
        (mem_edgesAtNode_valid after node depth (firstLocation.1.mpr
          (firstAttachment.trans (mem_edgesAtNode_attachmentKey before node depth localEdge)))).2.1
      have localSecond (localEdge : second ∈ edgesAtNode before node depth) : secondNext.owner = node.owner after :=
        (mem_edgesAtNode_valid after node depth (secondLocation.1.mpr
          (secondAttachment.trans (mem_edgesAtNode_attachmentKey before node depth localEdge)))).2.1
      by_cases firstLocal : first ∈ edgesAtNode before node depth
      · exact (localFirst firstLocal).trans
          (edge_owner_eq_of_local_reference before after left right upper_le_n depth firstLocal
            secondMember secondNextMember secondAttachment sameOwner.symm sameCell).symm
      by_cases secondLocal : second ∈ edgesAtNode before node depth
      · exact (edge_owner_eq_of_local_reference before after left right upper_le_n depth secondLocal
          firstMember firstNextMember firstAttachment sameOwner sameCell.symm).trans (localSecond secondLocal).symm
      have firstCases : first ∈ treeEdges before left leftBound (depth + 1) ∨
          first ∈ treeEdges before right upper_le_n (depth + 1) := by
        rcases List.mem_append.mp firstMember with prefixMember | inRight
        · exact Or.inl ((List.mem_append.mp prefixMember).resolve_left firstLocal)
        · exact Or.inr inRight
      have secondCases : second ∈ treeEdges before left leftBound (depth + 1) ∨
          second ∈ treeEdges before right upper_le_n (depth + 1) := by
        rcases List.mem_append.mp secondMember with prefixMember | inRight
        · exact Or.inl ((List.mem_append.mp prefixMember).resolve_left secondLocal)
        · exact Or.inr inRight
      rcases firstCases with firstLeft | firstRight
      · rcases secondCases with secondLeft | secondRight
        · have nextFirst := firstLocation.2.1.mpr (by rw [firstAttachment]; exact
            (mem_treeEdges_attachmentKey_bounds before left leftBound firstLeft).2)
          have nextSecond := secondLocation.2.1.mpr (by rw [secondAttachment]; exact
            (mem_treeEdges_attachmentKey_bounds before left leftBound secondLeft).2)
          exact ihLeft leftBound (depth + 1) firstLeft secondLeft nextFirst nextSecond
            (sameCell.mono (by intro cut inside; exact Finset.mem_union_left _ (Finset.mem_union_right _ inside)))
        · have firstUpper : first.owner.val ≤ 2 * root := (mem_treeEdges_inside before left leftBound firstLeft).2.1
          have secondLower : 2 * root + 2 ≤ second.owner.val := (mem_treeEdges_inside before right upper_le_n secondRight).1
          have equal := congrArg Fin.val sameOwner
          omega
      · rcases secondCases with secondLeft | secondRight
        · have firstLower : 2 * root + 2 ≤ first.owner.val := (mem_treeEdges_inside before right upper_le_n firstRight).1
          have secondUpper : second.owner.val ≤ 2 * root := (mem_treeEdges_inside before left leftBound secondLeft).2.1
          have equal := congrArg Fin.val sameOwner
          omega
        · have nextFirst := firstLocation.2.2.mpr (by
            rw [firstAttachment]
            have lowerBound := (mem_treeEdges_attachmentKey_bounds before right upper_le_n firstRight).1
            omega)
          have nextSecond := secondLocation.2.2.mpr (by
            rw [secondAttachment]
            have lowerBound := (mem_treeEdges_attachmentKey_bounds before right upper_le_n secondRight).1
            omega)
          exact ihRight upper_le_n (depth + 1) firstRight secondRight nextFirst nextSecond
            (sameCell.mono (by intro cut inside; exact Finset.mem_union_right _ inside))

end Splay.Accounting.JunctionBendReduction
