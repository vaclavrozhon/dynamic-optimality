import Splay.Accounting.JunctionCuts

namespace Splay.Accounting.JunctionBendReduction

open Splay.Rank Splay.Tree Splay.Lazy.Canonical

/-- A root-owned child that is not separated from an outside reference by
any junction cut stays root-owned. This treats arbitrarily long common
heavy-path pieces without charging their lengths. -/
theorem edge_owner_eq_subtreeOwner_of_sameCutCell_outside {n lower upper : ℕ}
    (before after : Snapshot n) (tree : BST lower upper) (upper_le_n : upper ≤ n) (depth : ℕ)
    {old next : Edge n} {reference : External n}
    (oldMember : old ∈ treeEdges before tree upper_le_n depth)
    (nextMember : next ∈ treeEdges after tree upper_le_n depth)
    (sameAttachment : next.attachmentKey = old.attachmentKey)
    (oldOwner : old.owner = subtreeOwner before tree upper_le_n)
    (outside : reference.val < 2 * lower ∨ 2 * upper < reference.val)
    (sameCell : SameCutCell (junctionCutsFrom before after tree upper_le_n) reference old.child) :
    next.owner = subtreeOwner after tree upper_le_n := by
  classical
  induction tree generalizing depth with
  | empty => simp [treeEdges] at oldMember
  | @node lower root upper left right ihLeft ihRight =>
      let node : AtNode n := ⟨lower, root, upper, left, right, upper_le_n⟩
      have leftBound : root ≤ n := by have := right.lower_le_upper; omega
      have childBounds := (mem_treeEdges_inside before (.node left right) upper_le_n oldMember).2.2
      have sameBranch : node.heavyBranch before = node.heavyBranch after :=
        heavyBranch_eq_of_sameCutCell_outside before after left right upper_le_n outside childBounds sameCell
      have newLocation := treeEdge_location_iff after left right upper_le_n depth nextMember
      change old.owner = node.owner before at oldOwner
      change next.owner = node.owner after
      rcases List.mem_append.mp oldMember with localOrLeft | rightEdge
      · rcases List.mem_append.mp localOrLeft with localEdge | leftEdge
        · have atRoot := mem_edgesAtNode_attachmentKey before node depth localEdge
          have localNew := newLocation.1.mpr (sameAttachment.trans atRoot)
          exact (mem_edgesAtNode_valid after node depth localNew).2.1
        · have oldInside := mem_treeEdges_inside before left leftBound leftEdge
          have rootInside : (node.owner before).val ≤ 2 * root := by
            rw [← oldOwner]
            exact oldInside.2.1
          have oldHeavy := node.heavyBranch_eq_left_of_owner_le_root before rootInside
          have newHeavy : node.heavyBranch after = .left := sameBranch.symm.trans oldHeavy
          have oldRootEq := node.owner_eq_branchMin_heavy before
          rw [oldHeavy] at oldRootEq
          change node.owner before = subtreeOwner before left leftBound at oldRootEq
          have newRootEq := node.owner_eq_branchMin_heavy after
          rw [newHeavy] at newRootEq
          change node.owner after = subtreeOwner after left leftBound at newRootEq
          have localNext := newLocation.2.1.mpr (by
            rw [sameAttachment]
            exact (mem_treeEdges_attachmentKey_bounds before left leftBound leftEdge).2)
          have outsideLeft : reference.val < 2 * lower ∨ 2 * root < reference.val := by
            have upper := right.lower_le_upper
            omega
          have sameLeft : SameCutCell (junctionCutsFrom before after left leftBound) reference old.child :=
            sameCell.mono (by intro cut member; exact Finset.mem_union_left _ (Finset.mem_union_right _ member))
          exact (ihLeft leftBound (depth + 1) leftEdge localNext
            (oldOwner.trans oldRootEq) outsideLeft sameLeft).trans newRootEq.symm
      · have oldInside := mem_treeEdges_inside before right upper_le_n rightEdge
        have rootInside : 2 * root + 2 ≤ (node.owner before).val := by
          rw [← oldOwner]
          exact oldInside.1
        have oldHeavy := node.heavyBranch_eq_right_of_root_lt_owner before rootInside
        have newHeavy : node.heavyBranch after = .right := sameBranch.symm.trans oldHeavy
        have oldRootEq := node.owner_eq_branchMin_heavy before
        rw [oldHeavy] at oldRootEq
        change node.owner before = subtreeOwner before right upper_le_n at oldRootEq
        have newRootEq := node.owner_eq_branchMin_heavy after
        rw [newHeavy] at newRootEq
        change node.owner after = subtreeOwner after right upper_le_n at newRootEq
        have localNext := newLocation.2.2.mpr (by
          rw [sameAttachment]
          have lowerBound := (mem_treeEdges_attachmentKey_bounds before right upper_le_n rightEdge).1
          omega)
        have outsideRight : reference.val < 2 * (root + 1) ∨ 2 * upper < reference.val := by
          have lowerBound := left.lower_le_upper
          omega
        have sameRight : SameCutCell (junctionCutsFrom before after right upper_le_n) reference old.child :=
          sameCell.mono (by intro cut member; exact Finset.mem_union_right _ member)
        exact (ihRight upper_le_n (depth + 1) rightEdge localNext
          (oldOwner.trans oldRootEq) outsideRight sameRight).trans newRootEq.symm

end Splay.Accounting.JunctionBendReduction
