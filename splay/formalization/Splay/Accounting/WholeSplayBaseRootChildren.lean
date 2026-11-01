import Splay.Accounting.WholeSplaySpinePrefixOrder
import Splay.Accounting.WholeSplayInitialProtectedLinks

namespace Splay.Accounting.WholeSplayTemporaryFocusedSpines.BaseFocus

open Splay.Rank Splay.Tree Splay.Tree.BST Splay.Lazy Splay.Lazy.Canonical

theorem lower_le_leftLower {n lower upper : ℕ} {key : Fin n}
    {leftBoundary rightBoundary : External n} {base : SpineBase key leftBoundary rightBoundary}
    {tree : BST lower upper} (focus : BaseFocus key leftBoundary rightBoundary base tree) :
    lower ≤ base.leftLower := by
  induction focus with
  | root => exact Nat.le_refl _
  | leftContext focus right ih => exact ih
  | rightContext left focus ih => have := left.lower_le_upper; omega

/-- Apart from the two fixed base minima, all original children of the
accessed owner lie numerically outside both of its original child subtrees. -/
theorem root_child_outside_base {n lower upper : ℕ} {key : Fin n}
    {leftBoundary rightBoundary : External n} {base : SpineBase key leftBoundary rightBoundary}
    {tree : BST lower upper} (focus : BaseFocus key leftBoundary rightBoundary base tree)
    (snapshot : Snapshot n) (bound : upper ≤ n) (depth : ℕ)
    (rankZero : snapshot.rank (valuePos key) = 0) {edge : Edge n}
    (member : edge ∈ treeEdges snapshot tree bound depth) (owner : edge.owner = valuePos key)
    (notLeft : edge.child ≠ subtreeOwner snapshot base.leftTree (Nat.le_of_lt key.isLt))
    (notRight : edge.child ≠ subtreeOwner snapshot base.rightTree (focus.rightUpper_le_upper.trans bound)) :
    edge.child.val < 2 * base.leftLower ∨ 2 * base.rightUpper < edge.child.val := by
  induction focus generalizing depth with
  | root =>
      let node : AtNode n := ⟨base.leftLower, key.val, base.rightUpper, base.leftTree, base.rightTree, bound⟩
      have heavy : node.heavyBranch snapshot = .middle := by
        apply node.heavyBranch_eq_of_rank_eq_zero snapshot .middle (valuePos key) rankZero
        · change 2 * base.leftLower ≤ 2 * key.val + 1 ∧ 2 * key.val + 1 ≤ 2 * base.rightUpper
          have leftBound := base.leftTree.lower_le_upper
          have rightBound := base.rightTree.lower_le_upper
          constructor <;> omega
        · rfl
      rcases List.mem_append.mp member with localOrLeft | inRight
      · rcases List.mem_append.mp localOrLeft with localEdge | inLeft
        · have valid := mem_edgesAtNode_valid snapshot node depth localEdge
          cases branch : edge.branch with
          | left => exact (notLeft (by have child := valid.2.2.1; rw [branch] at child; exact child)).elim
          | right => exact (notRight (by have child := valid.2.2.1; rw [branch] at child; exact child)).elim
          | middle => exact (valid.1 (branch.trans heavy.symm)).elim
        · have high : edge.owner.val ≤ 2 * key.val := (mem_treeEdges_inside snapshot base.leftTree (Nat.le_of_lt key.isLt) inLeft).2.1
          rw [owner] at high
          change 2 * key.val + 1 ≤ 2 * key.val at high
          omega
      · have low : 2 * (key.val + 1) ≤ edge.owner.val := (mem_treeEdges_inside snapshot base.rightTree bound inRight).1
        rw [owner] at low
        change 2 * (key.val + 1) ≤ 2 * key.val + 1 at low
        omega
  | @leftContext lower root upper inner focus right ih =>
      have innerBound : root ≤ n := by have := right.lower_le_upper; omega
      have keyBounds := (focus.initialFocused snapshot innerBound).key_bounds
      let node : AtNode n := ⟨lower, root, upper, inner, right, bound⟩
      have rootOwner : node.owner snapshot = valuePos key := atNode_owner_eq_accessed snapshot node key.val
        keyBounds.1 (by change key.val < upper; have := right.lower_le_upper; omega) key.isLt rankZero
      have heavy : node.heavyBranch snapshot = .left := node.heavyBranch_eq_left_of_owner_le_root snapshot
        (by rw [rootOwner]; change 2 * key.val + 1 ≤ 2 * root; omega)
      rcases List.mem_append.mp member with localOrInner | inRight
      · rcases List.mem_append.mp localOrInner with localEdge | inInner
        · have childHigh := (mem_edgesAtNode_valid snapshot node depth localEdge).child_gt_root_of_heavy_left heavy
          have baseBound := focus.rightUpper_le_upper
          exact Or.inr (by change 2 * root < edge.child.val at childHigh; omega)
        · exact ih innerBound (depth + 1) inInner notRight
      · have low : 2 * (root + 1) ≤ edge.owner.val := (mem_treeEdges_inside snapshot right bound inRight).1
        rw [owner] at low
        change 2 * (root + 1) ≤ 2 * key.val + 1 at low
        omega
  | @rightContext lower root upper left inner focus ih =>
      have keyBounds := (focus.initialFocused snapshot bound).key_bounds
      let node : AtNode n := ⟨lower, root, upper, left, inner, bound⟩
      have rootOwner : node.owner snapshot = valuePos key := atNode_owner_eq_accessed snapshot node key.val
        (by change lower ≤ key.val; have := left.lower_le_upper; omega) keyBounds.2 key.isLt rankZero
      have heavy : node.heavyBranch snapshot = .right := node.heavyBranch_eq_right_of_root_lt_owner snapshot
        (by rw [rootOwner]; change 2 * root + 2 ≤ 2 * key.val + 1; omega)
      rcases List.mem_append.mp member with localOrLeft | inInner
      · rcases List.mem_append.mp localOrLeft with localEdge | inLeft
        · have childLow := (mem_edgesAtNode_valid snapshot node depth localEdge).child_lt_root_of_heavy_right heavy
          have baseBound := focus.lower_le_leftLower
          exact Or.inl (by change edge.child.val < 2 * root + 2 at childLow; omega)
        · have high : edge.owner.val ≤ 2 * root := (mem_treeEdges_inside snapshot left (by have := left.lower_le_upper; have := inner.lower_le_upper; omega) inLeft).2.1
          rw [owner] at high
          change 2 * key.val + 1 ≤ 2 * root at high
          omega
      · exact ih bound (depth + 1) inInner notRight

end Splay.Accounting.WholeSplayTemporaryFocusedSpines.BaseFocus
