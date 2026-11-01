import Splay.Accounting.JunctionEdgeCorrespondence
import Splay.Lazy.CanonicalAttachmentLocation

namespace Splay.Accounting.JunctionBendReduction

open Splay.Rank Splay.Tree Splay.Lazy.Canonical

/-- Old and new light children attached directly at junction nodes. The
third branch may change side even though its incoming attachment persists. -/
noncomputable def junctionChildrenFrom {n lower upper : ℕ} (before after : Snapshot n)
    (tree : BST lower upper) (upper_le_n : upper ≤ n) : Finset (External n) := by
  classical
  exact match tree with
  | .empty _ => ∅
  | .node (root := root) left right =>
      let node : AtNode n := ⟨lower, root, upper, left, right, upper_le_n⟩
      (if node.heavyBranch before = node.heavyBranch after then ∅ else
        ((edgesAtNode before node 0).map Edge.child).toFinset ∪ ((edgesAtNode after node 0).map Edge.child).toFinset) ∪
        junctionChildrenFrom before after left (by have := right.lower_le_upper; omega) ∪
        junctionChildrenFrom before after right upper_le_n

theorem junctionChildrenFrom_card_le {n lower upper : ℕ} (before after : Snapshot n)
    (tree : BST lower upper) (upper_le_n : upper ≤ n) :
    (junctionChildrenFrom before after tree upper_le_n).card ≤ 4 * junctionCountFrom before after tree upper_le_n := by
  classical
  induction tree with
  | empty => simp [junctionChildrenFrom, junctionCountFrom]
  | @node lower root upper left right ihLeft ihRight =>
      let node : AtNode n := ⟨lower, root, upper, left, right, upper_le_n⟩
      have leftBound : root ≤ n := by have := right.lower_le_upper; omega
      let localChildren := if node.heavyBranch before = node.heavyBranch after then ∅ else
        ((edgesAtNode before node 0).map Edge.child).toFinset ∪ ((edgesAtNode after node 0).map Edge.child).toFinset
      have localBound : localChildren.card ≤ 4 * (if node.heavyBranch before = node.heavyBranch after then 0 else 1) := by
        unfold localChildren
        split
        · simp
        · have first : ((edgesAtNode before node 0).map Edge.child).toFinset.card ≤ 2 := by
            simpa using List.toFinset_card_le ((edgesAtNode before node 0).map Edge.child)
          have second : ((edgesAtNode after node 0).map Edge.child).toFinset.card ≤ 2 := by
            simpa using List.toFinset_card_le ((edgesAtNode after node 0).map Edge.child)
          exact (Finset.card_union_le _ _).trans (by omega)
      have unionBound := Finset.card_union_le (localChildren ∪ junctionChildrenFrom before after left leftBound)
        (junctionChildrenFrom before after right upper_le_n)
      have prefixBound := Finset.card_union_le localChildren (junctionChildrenFrom before after left leftBound)
      have l := ihLeft leftBound
      have r := ihRight upper_le_n
      rw [junctionCountFrom]
      change (localChildren ∪ junctionChildrenFrom before after left leftBound ∪ junctionChildrenFrom before after right upper_le_n).card ≤
        4 * ((if node.heavyBranch before = node.heavyBranch after then 0 else 1) +
          junctionCountFrom before after left leftBound + junctionCountFrom before after right upper_le_n)
      omega

theorem junctionChildrenFrom_comm {n lower upper : ℕ} (before after : Snapshot n)
    (tree : BST lower upper) (upper_le_n : upper ≤ n) :
    junctionChildrenFrom before after tree upper_le_n = junctionChildrenFrom after before tree upper_le_n := by
  classical
  induction tree with
  | empty => rfl
  | @node lower root upper left right ihLeft ihRight =>
      simp only [junctionChildrenFrom, ihLeft, ihRight]
      split_ifs <;> simp_all [Finset.union_comm]

/-- With the same outgoing heavy branch, a preserved local child also has
the same side. This is independent of changes to numeric priorities. -/
theorem edge_side_eq_of_same_heavyBranch {n : ℕ} {before after : Snapshot n}
    (node : AtNode n) (depth : ℕ) {old next : Edge n}
    (oldValid : old.Valid before node depth) (nextValid : next.Valid after node depth)
    (sameBranch : node.heavyBranch before = node.heavyBranch after) (sameChild : next.child = old.child) :
    next.side = old.side := by
  have oldOwner := node.owner_in_heavyBranch before
  have nextOwner := node.owner_in_heavyBranch after
  have oldSide := oldValid.side_order
  have nextSide := nextValid.side_order
  rw [← oldValid.2.1] at oldOwner
  rw [← nextValid.2.1] at nextOwner
  rw [← sameBranch] at nextOwner
  cases branch : node.heavyBranch before with
  | left =>
      rw [branch] at oldOwner nextOwner
      have oldChild := oldValid.child_gt_root_of_heavy_left branch
      have nextChild := nextValid.child_gt_root_of_heavy_left (sameBranch.symm.trans branch)
      change old.owner.val ≤ 2 * node.root at oldOwner
      change next.owner.val ≤ 2 * node.root at nextOwner
      cases os : old.side <;> cases ns : next.side <;>
        simp only [os, ns] at oldSide nextSide ⊢ <;> omega
  | right =>
      rw [branch] at oldOwner nextOwner
      have oldChild := oldValid.child_lt_root_of_heavy_right branch
      have nextChild := nextValid.child_lt_root_of_heavy_right (sameBranch.symm.trans branch)
      change 2 * node.root + 2 ≤ old.owner.val at oldOwner
      change 2 * node.root + 2 ≤ next.owner.val at nextOwner
      cases os : old.side <;> cases ns : next.side <;>
        simp only [os, ns] at oldSide nextSide ⊢ <;> omega
  | middle =>
      rw [branch] at oldOwner nextOwner
      have ownerEq : next.owner = old.owner := Fin.ext (nextOwner.trans oldOwner.symm)
      rw [nextValid.2.2.2.1, oldValid.2.2.2.1, ownerEq, sameChild]

/-- Outside the direct junction children, preserved attachments preserve
their side as well. -/
theorem edge_side_eq_of_not_mem_junctionChildren {n lower upper : ℕ}
    (before after : Snapshot n) (tree : BST lower upper) (upper_le_n : upper ≤ n) (depth : ℕ)
    {old next : Edge n} (oldMember : old ∈ treeEdges before tree upper_le_n depth)
    (nextMember : next ∈ treeEdges after tree upper_le_n depth)
    (sameAttachment : next.attachmentKey = old.attachmentKey) (sameChild : next.child = old.child)
    (ordinary : old.child ∉ junctionChildrenFrom before after tree upper_le_n) : next.side = old.side := by
  classical
  induction tree generalizing depth with
  | empty => simp [treeEdges] at oldMember
  | @node lower root upper left right ihLeft ihRight =>
      let node : AtNode n := ⟨lower, root, upper, left, right, upper_le_n⟩
      have leftBound : root ≤ n := by have := right.lower_le_upper; omega
      have location := treeEdge_location_iff after left right upper_le_n depth nextMember
      rcases List.mem_append.mp oldMember with localOrLeft | rightEdge
      · rcases List.mem_append.mp localOrLeft with localEdge | leftEdge
        · have localNext := location.1.mpr (sameAttachment.trans (mem_edgesAtNode_attachmentKey before node depth localEdge))
          have sameBranch : node.heavyBranch before = node.heavyBranch after := by
            by_contra junction
            apply ordinary
            apply Finset.mem_union_left
            apply Finset.mem_union_left
            change old.child ∈ (if node.heavyBranch before = node.heavyBranch after then ∅ else _)
            rw [if_neg junction]
            apply Finset.mem_union_left
            obtain ⟨branch, member, rfl⟩ := List.mem_map.mp localEdge
            exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨edgeFor before node 0 branch,
              List.mem_map.mpr ⟨branch, member, rfl⟩, rfl⟩)
          exact edge_side_eq_of_same_heavyBranch node depth (mem_edgesAtNode_valid before node depth localEdge)
            (mem_edgesAtNode_valid after node depth localNext) sameBranch sameChild
        · have nextLeft := location.2.1.mpr (by
            rw [sameAttachment]
            exact (mem_treeEdges_attachmentKey_bounds before left leftBound leftEdge).2)
          exact ihLeft leftBound (depth + 1) leftEdge nextLeft (by
            intro inside; exact ordinary (Finset.mem_union_left _ (Finset.mem_union_right _ inside)))
      · have nextRight := location.2.2.mpr (by
          rw [sameAttachment]
          have lowerBound := (mem_treeEdges_attachmentKey_bounds before right upper_le_n rightEdge).1
          omega)
        exact ihRight upper_le_n (depth + 1) rightEdge nextRight (by
          intro inside; exact ordinary (Finset.mem_union_right _ inside))

/-- A symmetric exception set sufficient for both attachment and side
preservation, of size at most six times the actual junction count. -/
noncomputable def junctionExceptionsFrom {n lower upper : ℕ} (before after : Snapshot n)
    (tree : BST lower upper) (upper_le_n : upper ≤ n) : Finset (External n) :=
  junctionVerticesFrom before after tree upper_le_n ∪ junctionChildrenFrom before after tree upper_le_n

theorem junctionExceptionsFrom_card_le {n lower upper : ℕ} (before after : Snapshot n)
    (tree : BST lower upper) (upper_le_n : upper ≤ n) :
    (junctionExceptionsFrom before after tree upper_le_n).card ≤ 6 * junctionCountFrom before after tree upper_le_n := by
  have unionBound := Finset.card_union_le (junctionVerticesFrom before after tree upper_le_n)
    (junctionChildrenFrom before after tree upper_le_n)
  have vertices := junctionVerticesFrom_card_le before after tree upper_le_n
  have children := junctionChildrenFrom_card_le before after tree upper_le_n
  unfold junctionExceptionsFrom
  omega

theorem junctionExceptionsFrom_comm {n lower upper : ℕ} (before after : Snapshot n)
    (tree : BST lower upper) (upper_le_n : upper ≤ n) :
    junctionExceptionsFrom before after tree upper_le_n = junctionExceptionsFrom after before tree upper_le_n := by
  rw [junctionExceptionsFrom, junctionExceptionsFrom, junctionVerticesFrom_comm before after,
    junctionChildrenFrom_comm before after]

/-- Actual edge correspondence after isolating the finite exception set. -/
theorem exists_edge_same_attachment_side_of_not_mem_exceptions {n lower upper : ℕ}
    (before after : Snapshot n) (tree : BST lower upper) (upper_le_n : upper ≤ n) (depth : ℕ)
    {old : Edge n} (member : old ∈ treeEdges before tree upper_le_n depth)
    (ordinary : old.child ∉ junctionExceptionsFrom before after tree upper_le_n) :
    ∃ next ∈ treeEdges after tree upper_le_n depth, next.child = old.child ∧ next.branch = old.branch ∧
      next.attachmentKey = old.attachmentKey ∧ next.attachmentDepth = old.attachmentDepth ∧ next.side = old.side := by
  obtain ⟨next, nextMember, child, branch, key, depthEq⟩ :=
    exists_edge_same_attachment_of_not_mem_junctionVertices before after tree upper_le_n depth member
      (fun inside => ordinary (Finset.mem_union_left _ inside))
  exact ⟨next, nextMember, child, branch, key, depthEq,
    edge_side_eq_of_not_mem_junctionChildren before after tree upper_le_n depth member nextMember key child
      (fun inside => ordinary (Finset.mem_union_right _ inside))⟩

end Splay.Accounting.JunctionBendReduction
