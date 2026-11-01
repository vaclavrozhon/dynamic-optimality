import Mathlib.Data.Nat.Basic
import Lean.Elab.Tactic.Omega

namespace Splay.Tree

/--
A binary search tree containing exactly the natural keys in the half-open
interval `[lower, upper)`.

The indices enforce the search-order invariant by construction. In a node with
key `root`, the left tree contains `[lower, root)` and the right tree contains
`[root + 1, upper)`. This representation also makes rotations type-correct
without rebuilding an inorder-sortedness proof.
-/
inductive BST : ℕ → ℕ → Type
  | empty (boundary : ℕ) : BST boundary boundary
  | node {lower root upper : ℕ} :
      BST lower root → BST (root + 1) upper → BST lower upper

namespace BST

/-- Number of keys stored in the tree. -/
def size {lower upper : ℕ} : BST lower upper → ℕ
  | .empty _ => 0
  | .node left right => size left + 1 + size right

/--
Maximum depth of an external/null leaf. An empty tree has height zero; a node
adds one to the larger child height.
-/
def height {lower upper : ℕ} : BST lower upper → ℕ
  | .empty _ => 0
  | .node left right => max (height left) (height right) + 1

/--
Search depth of a natural key. Later uses supply a key inside the tree's
interval; defining this for every natural keeps recursion and rewriting simple.
-/
def depth {lower upper : ℕ} : BST lower upper → ℕ → ℕ
  | .empty _, _ => 0
  | .node (root := root) left right, key =>
      if key = root then
        0
      else if key < root then
        (depth left key).succ
      else
        (depth right key).succ

@[simp]
theorem depth_root {lower root upper : ℕ}
    (left : BST lower root) (right : BST (root + 1) upper) :
    depth (.node left right) root = 0 := by
  simp [depth]

theorem depth_node_of_lt_root {lower root upper key : ℕ}
    (left : BST lower root) (right : BST (root + 1) upper)
    (hKey : key < root) :
    depth (.node left right) key = (depth left key).succ := by
  have hNe : key ≠ root := by omega
  simp [depth, hNe, hKey]

theorem depth_node_of_root_lt {lower root upper key : ℕ}
    (left : BST lower root) (right : BST (root + 1) upper)
    (hKey : root < key) :
    depth (.node left right) key = (depth right key).succ := by
  have hNe : key ≠ root := by omega
  have hNotLt : ¬key < root := by omega
  simp [depth, hNe, hNotLt]

/-- Every indexed interval admitted by `BST` is well formed. -/
theorem lower_le_upper {lower upper : ℕ} (tree : BST lower upper) :
    lower ≤ upper := by
  induction tree with
  | empty => rfl
  | node left right ihLeft ihRight => omega

/-- The type indices determine the number of stored value keys exactly. -/
theorem size_add_lower_eq_upper {lower upper : ℕ} (tree : BST lower upper) :
    tree.size + lower = upper := by
  induction tree with
  | empty =>
      simp [size]
  | node left right ihLeft ihRight =>
      simp only [size]
      omega

@[simp]
theorem size_eq_upper {upper : ℕ} (tree : BST 0 upper) :
    tree.size = upper := by
  have := tree.size_add_lower_eq_upper
  omega

/-- Search depth is bounded by the number of stored keys. -/
theorem depth_le_size {lower upper : ℕ} (tree : BST lower upper) (key : ℕ) :
    depth tree key ≤ size tree := by
  induction tree with
  | empty =>
      simp [depth, size]
  | node left right ihLeft ihRight =>
      simp only [depth, size]
      split
      · omega
      · split <;> omega

/-- Tree height is at most the number of stored value keys. -/
theorem height_le_size {lower upper : ℕ} (tree : BST lower upper) :
    tree.height ≤ tree.size := by
  induction tree with
  | empty =>
      simp [height, size]
  | node left right ihLeft ihRight =>
      simp only [height, size]
      omega

/-- Every nonempty indexed tree has a key at depth zero. -/
theorem exists_depth_eq_zero {lower upper : ℕ} (tree : BST lower upper)
    (hNonempty : lower < upper) :
    ∃ key, lower ≤ key ∧ key < upper ∧ depth tree key = 0 := by
  cases tree with
  | empty =>
      omega
  | @node lower root upper left right =>
      refine ⟨root, left.lower_le_upper, ?_, depth_root left right⟩
      have := right.lower_le_upper
      omega

end BST

end Splay.Tree
