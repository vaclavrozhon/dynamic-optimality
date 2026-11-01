import Splay.Tree.Rotation

namespace Splay.Tree.BST

/-- A tree has `key` at its root, with the indexed BST invariant in the type. -/
def HasRoot {lower upper : ℕ} (tree : BST lower upper) (key : ℕ) : Prop :=
  ∃ (left : BST lower key) (right : BST (key + 1) upper),
    tree = .node left right

/-- A final one-level splay step that promotes a child to the root. -/
inductive Zig :
    ℕ → {lower upper : ℕ} → BST lower upper → BST lower upper → Prop
  | fromLeft {lower promoted demoted upper : ℕ}
      (a : BST lower promoted)
      (b : BST (promoted + 1) demoted)
      (c : BST (demoted + 1) upper) :
      Zig promoted
        (.node (.node a b) c)
        (.node a (.node b c))
  | fromRight {lower demoted promoted upper : ℕ}
      (a : BST lower demoted)
      (b : BST (demoted + 1) promoted)
      (c : BST (promoted + 1) upper) :
      Zig promoted
        (.node a (.node b c))
        (.node (.node a b) c)

namespace Zig

/-- A zig is exactly one root rotation. -/
theorem toRootRotation {key lower upper : ℕ}
    {before after : BST lower upper} (step : Zig key before after) :
    RootRotation before after := by
  cases step with
  | fromLeft a b c => exact .right a b c
  | fromRight a b c => exact .left a b c

/-- The key named by a zig is at the root afterwards. -/
theorem hasRoot_after {key lower upper : ℕ}
    {before after : BST lower upper} (step : Zig key before after) :
    after.HasRoot key := by
  cases step with
  | fromLeft a b c =>
      exact ⟨a, .node b c, rfl⟩
  | fromRight a b c =>
      exact ⟨.node a b, c, rfl⟩

/-- A zig preserves the set, and hence the number, of value keys. -/
theorem size_eq {key lower upper : ℕ}
    {before after : BST lower upper} (step : Zig key before after) :
    before.size = after.size :=
  step.toRootRotation.size_eq

end Zig

/--
A standard two-level splay step. The four constructors are the two zig-zig
and the two zig-zag orientations.
-/
inductive DoubleRotation :
    ℕ → {lower upper : ℕ} → BST lower upper → BST lower upper → Prop
  | zigZigLeft
      {lower first second third upper : ℕ}
      (a : BST lower first)
      (b : BST (first + 1) second)
      (c : BST (second + 1) third)
      (d : BST (third + 1) upper) :
      DoubleRotation first
        (.node (.node (.node a b) c) d)
        (.node a (.node b (.node c d)))
  | zigZigRight
      {lower first second third upper : ℕ}
      (a : BST lower first)
      (b : BST (first + 1) second)
      (c : BST (second + 1) third)
      (d : BST (third + 1) upper) :
      DoubleRotation third
        (.node a (.node b (.node c d)))
        (.node (.node (.node a b) c) d)
  | zigZagLeftRight
      {lower first second third upper : ℕ}
      (a : BST lower first)
      (b : BST (first + 1) second)
      (c : BST (second + 1) third)
      (d : BST (third + 1) upper) :
      DoubleRotation second
        (.node (.node a (.node b c)) d)
        (.node (.node a b) (.node c d))
  | zigZagRightLeft
      {lower first second third upper : ℕ}
      (a : BST lower first)
      (b : BST (first + 1) second)
      (c : BST (second + 1) third)
      (d : BST (third + 1) upper) :
      DoubleRotation second
        (.node a (.node (.node b c) d))
        (.node (.node a b) (.node c d))

namespace DoubleRotation

/--
Operational content of a double splay step: its first rotation is at depth
zero or one, and its second rotation is at the root.
-/
theorem toTwoRotations {key lower upper : ℕ}
    {before after : BST lower upper}
    (step : DoubleRotation key before after) :
    ∃ (middle : BST lower upper) (firstDepth : ℕ),
      firstDepth ≤ 1 ∧
        RotationAt firstDepth before middle ∧
        RotationAt 0 middle after := by
  cases step with
  | zigZigLeft a b c d =>
      refine ⟨.node (.node a b) (.node c d), 0, by omega, ?_, ?_⟩
      · exact .root (.right (.node a b) c d)
      · exact .root (.right a b (.node c d))
  | zigZigRight a b c d =>
      refine ⟨.node (.node a b) (.node c d), 0, by omega, ?_, ?_⟩
      · exact .root (.left a b (.node c d))
      · exact .root (.left (.node a b) c d)
  | zigZagLeftRight a b c d =>
      refine ⟨.node (.node (.node a b) c) d, 1, by omega, ?_, ?_⟩
      · exact .leftContext (.root (.left a b c)) d
      · exact .root (.right (.node a b) c d)
  | zigZagRightLeft a b c d =>
      refine ⟨.node a (.node b (.node c d)), 1, by omega, ?_, ?_⟩
      · exact .rightContext a (.root (.right b c d))
      · exact .root (.left a b (.node c d))

/-- The accessed key named by a double rotation is at the root afterwards. -/
theorem hasRoot_after {key lower upper : ℕ}
    {before after : BST lower upper}
    (step : DoubleRotation key before after) :
    after.HasRoot key := by
  cases step with
  | zigZigLeft a b c d =>
      exact ⟨a, .node b (.node c d), rfl⟩
  | zigZigRight a b c d =>
      exact ⟨.node (.node a b) c, d, rfl⟩
  | zigZagLeftRight a b c d =>
      exact ⟨.node a b, .node c d, rfl⟩
  | zigZagRightLeft a b c d =>
      exact ⟨.node a b, .node c d, rfl⟩

/-- A double rotation preserves the number of value keys. -/
theorem size_eq {key lower upper : ℕ}
    {before after : BST lower upper}
    (step : DoubleRotation key before after) :
    before.size = after.size := by
  obtain ⟨middle, _, _, hFirst, hSecond⟩ := step.toTwoRotations
  exact hFirst.size_eq.trans hSecond.size_eq

end DoubleRotation

end Splay.Tree.BST
