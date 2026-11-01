import Splay.Tree.Basic

namespace Splay.Tree.BST

/--
Depth of an external inorder position.

For a BST on `[lower, upper)`, positions range from `2 * lower` through
`2 * upper`. Even positions are null leaves and the odd position
`2 * root + 1` is the value stored at a node.
-/
def externalDepth {lower upper : ℕ} : BST lower upper → ℕ → ℕ
  | .empty _, _ => 0
  | .node (root := root) left right, position =>
      if position < 2 * root + 1 then
        (externalDepth left position).succ
      else if position = 2 * root + 1 then
        0
      else
        (externalDepth right position).succ

@[simp]
theorem externalDepth_root {lower root upper : ℕ}
    (left : BST lower root) (right : BST (root + 1) upper) :
    externalDepth (.node left right) (2 * root + 1) = 0 := by
  simp [externalDepth]

theorem externalDepth_node_of_lt_root {lower root upper position : ℕ}
    (left : BST lower root) (right : BST (root + 1) upper)
    (hPosition : position < 2 * root + 1) :
    externalDepth (.node left right) position =
      (externalDepth left position).succ := by
  simp [externalDepth, hPosition]

theorem externalDepth_node_of_root_lt {lower root upper position : ℕ}
    (left : BST lower root) (right : BST (root + 1) upper)
    (hPosition : 2 * root + 1 < position) :
    externalDepth (.node left right) position =
      (externalDepth right position).succ := by
  have hNotLt : ¬position < 2 * root + 1 := by omega
  have hNe : position ≠ 2 * root + 1 := by omega
  simp [externalDepth, hNotLt, hNe]

/-- External-node depth is bounded by the number of value nodes. -/
theorem externalDepth_le_size {lower upper : ℕ}
    (tree : BST lower upper) (position : ℕ) :
    externalDepth tree position ≤ tree.size := by
  induction tree with
  | empty =>
      simp [externalDepth, size]
  | node left right ihLeft ihRight =>
      simp only [externalDepth, size]
      split
      · omega
      · split
        · omega
        · omega

/-- External-node depth is bounded by the comparison tree's height. -/
theorem externalDepth_le_height {lower upper : ℕ}
    (tree : BST lower upper) (position : ℕ) :
    externalDepth tree position ≤ tree.height := by
  induction tree with
  | empty =>
      simp [externalDepth, height]
  | node left right ihLeft ihRight =>
      simp only [externalDepth, height]
      split
      · omega
      · split
        · omega
        · omega

/-- Every BST, including an empty one, has an external position at depth zero. -/
theorem exists_externalDepth_eq_zero {lower upper : ℕ}
    (tree : BST lower upper) :
    ∃ position,
      2 * lower ≤ position ∧ position ≤ 2 * upper ∧
        externalDepth tree position = 0 := by
  cases tree with
  | empty =>
      exact ⟨2 * lower, le_rfl, le_rfl, rfl⟩
  | @node lower root upper left right =>
      refine ⟨2 * root + 1, ?_, ?_, externalDepth_root left right⟩
      · have := left.lower_le_upper
        omega
      · have := right.lower_le_upper
        omega

end Splay.Tree.BST
