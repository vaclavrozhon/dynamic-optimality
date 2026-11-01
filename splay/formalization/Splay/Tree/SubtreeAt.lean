import Splay.Tree.SplayExecution

namespace Splay.Tree.BST

/-- A literal occurrence of a fixed subtree, retaining its exact depth.
Its internal structure and interval are unchanged by the outer context. -/
inductive SubtreeAt {innerLower innerUpper : ℕ} (inner : BST innerLower innerUpper) :
    {lower upper : ℕ} → ℕ → BST lower upper → Prop
  | here : SubtreeAt inner 0 inner
  | left {lower root upper depth : ℕ} {leftTree : BST lower root}
      (occurrence : SubtreeAt inner depth leftTree) (rightTree : BST (root + 1) upper) :
      SubtreeAt inner (depth + 1) (.node leftTree rightTree)
  | right {lower root upper depth : ℕ} (leftTree : BST lower root) {rightTree : BST (root + 1) upper}
      (occurrence : SubtreeAt inner depth rightTree) :
      SubtreeAt inner (depth + 1) (.node leftTree rightTree)

namespace SubtreeAt

theorem bounds {innerLower innerUpper lower upper depth : ℕ}
    {inner : BST innerLower innerUpper} {tree : BST lower upper} (occurrence : SubtreeAt inner depth tree) :
    lower ≤ innerLower ∧ innerUpper ≤ upper := by
  induction occurrence with
  | here => exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  | left occurrence right ih => have := right.lower_le_upper; omega
  | right left occurrence ih => have := left.lower_le_upper; omega

theorem trans {innerLower innerUpper middleLower middleUpper lower upper firstDepth secondDepth : ℕ}
    {inner : BST innerLower innerUpper} {middle : BST middleLower middleUpper} {tree : BST lower upper}
    (inside : SubtreeAt inner firstDepth middle) (outside : SubtreeAt middle secondDepth tree) :
    SubtreeAt inner (firstDepth + secondDepth) tree := by
  induction outside with
  | here => simpa using inside
  | left occurrence right ih => simpa only [Nat.add_assoc] using ih.left right
  | right left occurrence ih => simpa only [Nat.add_assoc] using SubtreeAt.right left ih

end SubtreeAt
end Splay.Tree.BST
