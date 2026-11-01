import Splay.Tree.SubtreeAt

namespace Splay.Tree.BST

/-- A zig leaves every literal subtree outside the accessed key intact. -/
theorem Zig.preserves_subtree {innerLower innerUpper lower upper key depth : ℕ}
    {inner : BST innerLower innerUpper} {before after : BST lower upper}
    (step : Zig key before after) (occurrence : SubtreeAt inner depth before)
    (outside : key < innerLower ∨ innerUpper ≤ key) : ∃ nextDepth, SubtreeAt inner nextDepth after := by
  cases step with
  | fromLeft a b c =>
      have aBound := a.lower_le_upper
      have bBound := b.lower_le_upper
      have cBound := c.lower_le_upper
      cases occurrence with
      | here => omega
      | left occurrence _ =>
          cases occurrence with
          | here => omega
          | left occurrence _ => exact ⟨_, occurrence.left (.node b c)⟩
          | right _ occurrence => exact ⟨_, SubtreeAt.right a (occurrence.left c)⟩
      | right _ occurrence => exact ⟨_, SubtreeAt.right a (SubtreeAt.right b occurrence)⟩
  | fromRight a b c =>
      have aBound := a.lower_le_upper
      have bBound := b.lower_le_upper
      have cBound := c.lower_le_upper
      cases occurrence with
      | here => omega
      | left occurrence _ => exact ⟨_, (occurrence.left b).left c⟩
      | right _ occurrence =>
          cases occurrence with
          | here => omega
          | left occurrence _ => exact ⟨_, (SubtreeAt.right a occurrence).left c⟩
          | right _ occurrence => exact ⟨_, SubtreeAt.right (.node a b) occurrence⟩

/-- All four double rotations preserve the untouched off-path subtrees.
Only their depths and their outer contexts may change. -/
theorem DoubleRotation.preserves_subtree {innerLower innerUpper lower upper key depth : ℕ}
    {inner : BST innerLower innerUpper} {before after : BST lower upper}
    (step : DoubleRotation key before after) (occurrence : SubtreeAt inner depth before)
    (outside : key < innerLower ∨ innerUpper ≤ key) : ∃ nextDepth, SubtreeAt inner nextDepth after := by
  cases step with
  | zigZigLeft a b c d =>
      have aBound := a.lower_le_upper
      have bBound := b.lower_le_upper
      have cBound := c.lower_le_upper
      have dBound := d.lower_le_upper
      cases occurrence with
      | here => omega
      | left occurrence _ =>
          cases occurrence with
          | here => omega
          | left occurrence _ =>
              cases occurrence with
              | here => omega
              | left occurrence _ => exact ⟨_, occurrence.left (.node b (.node c d))⟩
              | right _ occurrence => exact ⟨_, SubtreeAt.right a (occurrence.left (.node c d))⟩
          | right _ occurrence => exact ⟨_, SubtreeAt.right a (SubtreeAt.right b (occurrence.left d))⟩
      | right _ occurrence => exact ⟨_, SubtreeAt.right a (SubtreeAt.right b (SubtreeAt.right c occurrence))⟩
  | zigZigRight a b c d =>
      have aBound := a.lower_le_upper
      have bBound := b.lower_le_upper
      have cBound := c.lower_le_upper
      have dBound := d.lower_le_upper
      cases occurrence with
      | here => omega
      | left occurrence _ => exact ⟨_, ((occurrence.left b).left c).left d⟩
      | right _ occurrence =>
          cases occurrence with
          | here => omega
          | left occurrence _ => exact ⟨_, ((SubtreeAt.right a occurrence).left c).left d⟩
          | right _ occurrence =>
              cases occurrence with
              | here => omega
              | left occurrence _ => exact ⟨_, (SubtreeAt.right (.node a b) occurrence).left d⟩
              | right _ occurrence => exact ⟨_, SubtreeAt.right (.node (.node a b) c) occurrence⟩
  | zigZagLeftRight a b c d =>
      have aBound := a.lower_le_upper
      have bBound := b.lower_le_upper
      have cBound := c.lower_le_upper
      have dBound := d.lower_le_upper
      cases occurrence with
      | here => omega
      | left occurrence _ =>
          cases occurrence with
          | here => omega
          | left occurrence _ => exact ⟨_, (occurrence.left b).left (.node c d)⟩
          | right _ occurrence =>
              cases occurrence with
              | here => omega
              | left occurrence _ => exact ⟨_, (SubtreeAt.right a occurrence).left (.node c d)⟩
              | right _ occurrence => exact ⟨_, SubtreeAt.right (.node a b) (occurrence.left d)⟩
      | right _ occurrence => exact ⟨_, SubtreeAt.right (.node a b) (SubtreeAt.right c occurrence)⟩
  | zigZagRightLeft a b c d =>
      have aBound := a.lower_le_upper
      have bBound := b.lower_le_upper
      have cBound := c.lower_le_upper
      have dBound := d.lower_le_upper
      cases occurrence with
      | here => omega
      | left occurrence _ => exact ⟨_, (occurrence.left b).left (.node c d)⟩
      | right _ occurrence =>
          cases occurrence with
          | here => omega
          | left occurrence _ =>
              cases occurrence with
              | here => omega
              | left occurrence _ => exact ⟨_, (SubtreeAt.right a occurrence).left (.node c d)⟩
              | right _ occurrence => exact ⟨_, SubtreeAt.right (.node a b) (occurrence.left d)⟩
          | right _ occurrence => exact ⟨_, SubtreeAt.right (.node a b) (SubtreeAt.right c occurrence)⟩

theorem DoubleRotationAt.preserves_subtree {innerLower innerUpper lower upper key depth rotationDepth : ℕ}
    {inner : BST innerLower innerUpper} {before after : BST lower upper}
    (step : DoubleRotationAt rotationDepth key before after) (occurrence : SubtreeAt inner depth before)
    (outside : key < innerLower ∨ innerUpper ≤ key) : ∃ nextDepth, SubtreeAt inner nextDepth after := by
  induction step generalizing depth with
  | root step => exact step.preserves_subtree occurrence outside
  | leftContext step right ih =>
      have keyBounds := step.key_bounds
      have rightBound := right.lower_le_upper
      cases occurrence with
      | here => omega
      | left occurrence _ =>
          obtain ⟨nextDepth, next⟩ := ih occurrence outside
          exact ⟨_, next.left right⟩
      | right _ occurrence => exact ⟨_, SubtreeAt.right _ occurrence⟩
  | rightContext left step ih =>
      have keyBounds := step.key_bounds
      have leftBound := left.lower_le_upper
      cases occurrence with
      | here => omega
      | left occurrence _ => exact ⟨_, occurrence.left _⟩
      | right _ occurrence =>
          obtain ⟨nextDepth, next⟩ := ih occurrence outside
          exact ⟨_, SubtreeAt.right left next⟩

theorem SplayStep.preserves_subtree {innerLower innerUpper lower upper key depth : ℕ}
    {inner : BST innerLower innerUpper} {before after : BST lower upper}
    (step : SplayStep key before after) (occurrence : SubtreeAt inner depth before)
    (outside : key < innerLower ∨ innerUpper ≤ key) : ∃ nextDepth, SubtreeAt inner nextDepth after := by
  cases step with
  | zig step => exact step.preserves_subtree occurrence outside
  | double step => exact step.preserves_subtree occurrence outside

theorem SplayExecution.preserves_subtree {innerLower innerUpper lower upper key depth : ℕ}
    {inner : BST innerLower innerUpper} {before after : BST lower upper}
    (execution : SplayExecution key before after) (occurrence : SubtreeAt inner depth before)
    (outside : key < innerLower ∨ innerUpper ≤ key) : ∃ nextDepth, SubtreeAt inner nextDepth after := by
  induction execution generalizing depth with
  | done _ => exact ⟨_, occurrence⟩
  | next step tail ih =>
      obtain ⟨middleDepth, middle⟩ := step.preserves_subtree occurrence outside
      exact ih middle

end Splay.Tree.BST
