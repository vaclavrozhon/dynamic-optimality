import Splay.Tree.Basic

namespace Splay.Tree

namespace BST

/--
A single rotation at the root of an indexed BST.

The interval indices make both sides definitionally inhabit the same type:
`a`, `b`, and `c` contain the three consecutive key intervals separated by
the two rotated keys.
-/
inductive RootRotation :
    {lower upper : ℕ} → BST lower upper → BST lower upper → Prop
  | right {lower promoted demoted upper : ℕ}
      (a : BST lower promoted)
      (b : BST (promoted + 1) demoted)
      (c : BST (demoted + 1) upper) :
      RootRotation
        (.node (.node a b) c)
        (.node a (.node b c))
  | left {lower promoted demoted upper : ℕ}
      (a : BST lower promoted)
      (b : BST (promoted + 1) demoted)
      (c : BST (demoted + 1) upper) :
      RootRotation
        (.node a (.node b c))
        (.node (.node a b) c)

/--
A rotation inside a tree, together with its depth.

Depth zero means a root rotation. Passing through one enclosing node increments
the depth, so `depth` is the depth of the root of the smallest subtree on which
`RootRotation` is applied (equivalently, the shallower endpoint of the rotated
edge).
-/
inductive RotationAt :
    ℕ → {lower upper : ℕ} → BST lower upper → BST lower upper → Prop
  | root {lower upper : ℕ} {before after : BST lower upper}
      (step : RootRotation before after) :
      RotationAt 0 before after
  | leftContext {depth lower root upper : ℕ}
      {before after : BST lower root}
      (step : RotationAt depth before after)
      (right : BST (root + 1) upper) :
      RotationAt depth.succ (.node before right) (.node after right)
  | rightContext {depth lower root upper : ℕ}
      (left : BST lower root)
      {before after : BST (root + 1) upper}
      (step : RotationAt depth before after) :
      RotationAt depth.succ (.node left before) (.node left after)

namespace RootRotation

/-- Reversing a root rotation is again a root rotation. -/
protected theorem symm {lower upper : ℕ} {before after : BST lower upper}
    (step : RootRotation before after) :
    RootRotation after before := by
  cases step with
  | right a b c => exact .left a b c
  | left a b c => exact .right a b c

/-- A root rotation preserves the number of keys. -/
theorem size_eq {lower upper : ℕ} {before after : BST lower upper}
    (step : RootRotation before after) :
    before.size = after.size := by
  cases step <;> simp only [size] <;> omega

end RootRotation

namespace RotationAt

/-- Reversing a rotation preserves both validity and its depth. -/
protected theorem symm {depth lower upper : ℕ}
    {before after : BST lower upper}
    (step : RotationAt depth before after) :
    RotationAt depth after before := by
  induction step with
  | root rootStep =>
      exact .root rootStep.symm
  | leftContext step right ih =>
      exact .leftContext ih right
  | rightContext left step ih =>
      exact .rightContext left ih

/-- A rotation at any depth preserves the number of keys. -/
theorem size_eq {depth lower upper : ℕ}
    {before after : BST lower upper}
    (step : RotationAt depth before after) :
    before.size = after.size := by
  induction step with
  | root rootStep =>
      exact rootStep.size_eq
  | leftContext step right ih =>
      simp only [size]
      omega
  | rightContext left step ih =>
      simp only [size]
      omega

end RotationAt

end BST

end Splay.Tree
