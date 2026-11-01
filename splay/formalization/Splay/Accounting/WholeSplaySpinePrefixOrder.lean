import Splay.Accounting.WholeSplayPersistentHeapLinks
import Splay.Accounting.CanonicalSubtreeEdges

namespace Splay.Accounting

open Splay.Rank Splay.Tree Splay.Tree.BST Splay.Lazy Splay.Lazy.Canonical
open WholeSplayTemporarySpineGeometry

private theorem local_side_right_of_heavy_left {n : ℕ} (snapshot : Snapshot n) (node : AtNode n)
    (depth : ℕ) (heavy : node.heavyBranch snapshot = .left) {edge : Edge n}
    (member : edge ∈ edgesAtNode snapshot node depth) : edge.side = .right := by
  have valid := mem_edgesAtNode_valid snapshot node depth member
  have ownerLow := node.owner_in_heavyBranch snapshot
  rw [heavy, ← valid.2.1] at ownerLow
  have childHigh := valid.child_gt_root_of_heavy_left heavy
  change edge.owner.val ≤ 2 * node.root at ownerLow
  have order := valid.side_order
  cases side : edge.side with
  | right => rfl
  | left => rw [side] at order; omega

private theorem local_side_left_of_heavy_right {n : ℕ} (snapshot : Snapshot n) (node : AtNode n)
    (depth : ℕ) (heavy : node.heavyBranch snapshot = .right) {edge : Edge n}
    (member : edge ∈ edgesAtNode snapshot node depth) : edge.side = .left := by
  have valid := mem_edgesAtNode_valid snapshot node depth member
  have ownerHigh := node.owner_in_heavyBranch snapshot
  rw [heavy, ← valid.2.1] at ownerHigh
  have childLow := valid.child_lt_root_of_heavy_right heavy
  change 2 * node.root + 2 ≤ edge.owner.val at ownerHigh
  have order := valid.side_order
  cases side : edge.side with
  | left => rfl
  | right => rw [side] at order; omega

/-- Every new right-spine child is attached above every opposite-side child
of its fixed boundary owner. The opposite children all lie in the base. -/
theorem RightSpine.prefix_above_opposite {n key baseUpper upper : ℕ} {snapshot : Snapshot n}
    {base : BST (key + 1) baseUpper} {tree : BST (key + 1) upper}
    (spine : RightSpine snapshot base tree) (depth : ℕ) {first second : Edge n}
    (firstMember : first ∈ treeEdges snapshot tree spine.upper_le_n depth)
    (secondMember : second ∈ treeEdges snapshot tree spine.upper_le_n depth)
    (firstOwner : first.owner = subtreeOwner snapshot base spine.base_le_n)
    (secondOwner : second.owner = subtreeOwner snapshot base spine.base_le_n)
    (outside : 2 * baseUpper < first.child.val) (opposite : second.side = .left) :
    first.attachmentDepth < second.attachmentDepth := by
  induction spine generalizing depth with
  | base bound =>
      have inside : first.child.val ≤ 2 * baseUpper := (mem_treeEdges_inside snapshot base bound firstMember).2.2.2
      omega
  | @grow root upper inner innerSpine hanging bound heavy ih =>
      let node : AtNode n := ⟨key + 1, root, upper, inner, hanging, bound⟩
      change node.heavyBranch snapshot = .left at heavy
      have rootOwner := rightSpine_owner_eq_base (RightSpine.grow innerSpine hanging bound heavy)
      change node.owner snapshot = subtreeOwner snapshot base innerSpine.base_le_n at rootOwner
      have ownerLow := node.owner_in_heavyBranch snapshot
      rw [heavy, rootOwner] at ownerLow
      change (subtreeOwner snapshot base innerSpine.base_le_n).val ≤ 2 * root at ownerLow
      have location : ∀ edge ∈ treeEdges snapshot (.node inner hanging) bound depth,
          edge.owner = subtreeOwner snapshot base innerSpine.base_le_n →
            edge ∈ edgesAtNode snapshot node depth ∨ edge ∈ treeEdges snapshot inner innerSpine.upper_le_n (depth + 1) := by
        intro edge member ownerEq
        rcases List.mem_append.mp member with localOrInner | inHanging
        · exact List.mem_append.mp localOrInner
        · have high : 2 * (root + 1) ≤ edge.owner.val := (mem_treeEdges_inside snapshot hanging bound inHanging).1
          rw [ownerEq] at high
          omega
      have secondInner : second ∈ treeEdges snapshot inner innerSpine.upper_le_n (depth + 1) := by
        rcases location second secondMember secondOwner with localEdge | inInner
        · have side := local_side_right_of_heavy_left snapshot node depth heavy localEdge
          rw [opposite] at side
          contradiction
        · exact inInner
      rcases location first firstMember firstOwner with firstLocal | firstInner
      · have firstDepth := (mem_edgesAtNode_valid snapshot node depth firstLocal).2.2.2.2.2.1
        have secondDepth := JunctionBendReduction.treeEdge_depth_le snapshot inner innerSpine.upper_le_n (depth + 1) secondInner
        omega
      · exact ih (depth + 1) firstInner secondInner firstOwner secondOwner

/-- The symmetric order fact for the new left-spine prefix. -/
theorem LeftSpine.prefix_above_opposite {n key baseLower lower : ℕ} {snapshot : Snapshot n}
    {base : BST baseLower key} {tree : BST lower key}
    (spine : LeftSpine snapshot base tree) (depth : ℕ) {first second : Edge n}
    (firstMember : first ∈ treeEdges snapshot tree spine.upper_le_n depth)
    (secondMember : second ∈ treeEdges snapshot tree spine.upper_le_n depth)
    (firstOwner : first.owner = subtreeOwner snapshot base spine.base_le_n)
    (secondOwner : second.owner = subtreeOwner snapshot base spine.base_le_n)
    (outside : first.child.val < 2 * baseLower) (opposite : second.side = .right) :
    first.attachmentDepth < second.attachmentDepth := by
  induction spine generalizing depth with
  | base bound =>
      have inside : 2 * baseLower ≤ first.child.val := (mem_treeEdges_inside snapshot base bound firstMember).2.2.1
      omega
  | @grow lower root inner innerSpine hanging bound keyBound heavy ih =>
      let node : AtNode n := ⟨lower, root, key, hanging, inner, keyBound⟩
      change node.heavyBranch snapshot = .right at heavy
      have rootOwner := leftSpine_owner_eq_base (LeftSpine.grow innerSpine hanging bound keyBound heavy)
      change node.owner snapshot = subtreeOwner snapshot base innerSpine.base_le_n at rootOwner
      have ownerHigh := node.owner_in_heavyBranch snapshot
      rw [heavy, rootOwner] at ownerHigh
      change 2 * root + 2 ≤ (subtreeOwner snapshot base innerSpine.base_le_n).val at ownerHigh
      have location : ∀ edge ∈ treeEdges snapshot (.node hanging inner) keyBound depth,
          edge.owner = subtreeOwner snapshot base innerSpine.base_le_n →
            edge ∈ edgesAtNode snapshot node depth ∨ edge ∈ treeEdges snapshot inner innerSpine.upper_le_n (depth + 1) := by
        intro edge member ownerEq
        rcases List.mem_append.mp member with localOrHanging | inInner
        · rcases List.mem_append.mp localOrHanging with localEdge | inHanging
          · exact Or.inl localEdge
          · have low : edge.owner.val ≤ 2 * root := (mem_treeEdges_inside snapshot hanging bound inHanging).2.1
            rw [ownerEq] at low
            omega
        · exact Or.inr inInner
      have secondInner : second ∈ treeEdges snapshot inner innerSpine.upper_le_n (depth + 1) := by
        rcases location second secondMember secondOwner with localEdge | inInner
        · have side := local_side_left_of_heavy_right snapshot node depth heavy localEdge
          rw [opposite] at side
          contradiction
        · exact inInner
      rcases location first firstMember firstOwner with firstLocal | firstInner
      · have firstDepth := (mem_edgesAtNode_valid snapshot node depth firstLocal).2.2.2.2.2.1
        have secondDepth := JunctionBendReduction.treeEdge_depth_le snapshot inner innerSpine.upper_le_n (depth + 1) secondInner
        omega
      · exact ih (depth + 1) firstInner secondInner firstOwner secondOwner

end Splay.Accounting
