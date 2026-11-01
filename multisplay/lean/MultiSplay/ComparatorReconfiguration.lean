import MultiSplay.ForestProgram
import TangoSquared.RestrictedRotations

/-!
# Concrete comparator preparation on a rooted skeleton

The common forest comparator charges a rotation at depth `d` by `d + 1`.
The existing shallow reconfiguration uses only root and child rotations,
so it gives a linear preparation in precisely that metric. Arbitrary
subtrees hanging in the skeleton's gaps are retained literally.
-/

namespace MultiSplay.CommonForest

open DynamicOptimality (RawTree)
open TangoSquared.MTR.Tree

variable {α : Type*}

theorem restrictedStep_preparation {before after : RawTree α}
    (step : RestrictedStep before after) :
    ∃ work ≤ 2, RotationPreparation before after work := by
  cases step with
  | rootRight a b c x y => exact ⟨1, by omega, 0, .right a b c x y, rfl⟩
  | rootLeft a b c x y => exact ⟨1, by omega, 0, .left a b c x y, rfl⟩
  | rightRight a b c d x y z =>
      exact ⟨2, le_rfl, 1, .rightContext a x (.right b c d y z), rfl⟩
  | rightLeft a b c d x y z =>
      exact ⟨2, le_rfl, 1, .rightContext a x (.left b c d y z), rfl⟩
  | leftRight a b c d x y z =>
      exact ⟨2, le_rfl, 1, .leftContext (.right a b c x y) z d, rfl⟩
  | leftLeft a b c d x y z =>
      exact ⟨2, le_rfl, 1, .leftContext (.left a b c x y) z d, rfl⟩

theorem restrictedSteps_program {before after : RawTree α} {count : Nat}
    (steps : RestrictedSteps count before after) :
    ∃ work ≤ 2 * count, Program [before] [] [after] work := by
  induction steps with
  | refl => exact ⟨0, le_rfl, .nil _⟩
  | cons step rest ih =>
      obtain ⟨first, firstBound, preparation⟩ := restrictedStep_preparation step
      obtain ⟨remaining, remainingBound, program⟩ := ih
      exact ⟨first + remaining, by omega, .cons (.prepare preparation) program⟩

/-- Reconfigure only the displayed skeleton; none of its gap payloads is
traversed or reinitialized, and the event word remains empty. -/
theorem rooted_hull_program (before after : RawTree α)
    (same : inorder before = inorder after) (gaps : Nat → RawTree α) (offset : Nat) :
    ∃ work ≤ 6 * size before + 6 * size after,
      Program [plug gaps offset before] [] [plug gaps offset after] work := by
  obtain ⟨count, countBound, steps⟩ := rooted_hull_rotation_linear before after same gaps offset
  obtain ⟨work, workBound, program⟩ := restrictedSteps_program steps
  exact ⟨work, by omega, program⟩

/-- Full initialization is charged once to the actual component size. -/
theorem initialize_program (before after : RawTree α)
    (same : inorder before = inorder after) :
    ∃ work ≤ 12 * size before, Program [before] [] [after] work := by
  obtain ⟨count, countBound, steps⟩ := restricted_rotation_linear before after same
  obtain ⟨work, workBound, program⟩ := restrictedSteps_program steps
  have sizes := steps.size_eq
  exact ⟨work, by omega, program⟩

end MultiSplay.CommonForest
