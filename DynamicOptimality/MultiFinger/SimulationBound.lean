import DynamicOptimality.MultiFinger.Static
import DynamicOptimality.SearchRotationModel

/-! Statement interface for static multifinger simulation.
This module defines the proposition consumed by the colored-walk reduction.
`Simulation.lean` proves its unconditional witness using the actual
persistent hand, physical tendon deques, and ordinary rotations.
-/

namespace DynamicOptimality.MultiFinger

open ChaCha.MTR

variable {α : Type*}

/-- Every maintained finger is at an actual key, never at a null child. -/
def Configuration.Live {reference : RawTree α} {count : Nat}
    (state : Configuration reference count) : Prop :=
  ∀ index, (state.finger index).focus ≠ .empty

private theorem step_target_nonempty {before after : Pointer.Cursor α}
    (step : Pointer.Step before after) : after.focus ≠ .empty := by
  cases step <;> simp

theorem Step.live {reference : RawTree α} {count : Nat}
    {before after : Configuration reference count} (step : Step before after)
    (live : before.Live) : after.Live := by
  cases step with
  | move index next actual same =>
    intro other
    by_cases equal : other = index
    · subst other
      simpa only [Configuration.update,Function.update_self] using step_target_nonempty actual
    · simpa only [Configuration.update,Function.update_of_ne equal] using live other

theorem Execution.live {reference : RawTree α} {count : Nat}
    {before after : Configuration reference count} {word : List α} {cost : Nat}
    (run : Execution before word after cost) (live : before.Live) : after.Live := by
  induction run with
  | done => exact live
  | move step rest ih => exact ih (step.live live)
  | serve index key found rest ih => exact ih live

def logarithmicFactor (fingers : Nat) : Nat := 1+Nat.log 2 (fingers+1)

/-- An actual static persistent-finger execution can be served by the shared
search-plus-ordinary-rotations model. The starting ordinary BST may be
chosen by the simulator. A supplied initial BST is handled separately by
the already proved shared initialization theorem. -/
def SimulationBound (constant : Nat) : Prop :=
  ∀ (reference : RawTree Nat) (fingers : Nat)
    (initial final : Configuration reference fingers) (word : List Nat) (fingerCost : Nat),
    reference.Ordered → 0 < fingers → initial.Live →
    Execution initial word final fingerCost →
    ∃ (before after : RawTree Nat) (cost : Nat),
      before.Ordered ∧ before.inorder = reference.inorder ∧
      SearchRotation.Execution before word after cost ∧
      cost ≤ constant*((fingerCost+fingers)*logarithmicFactor fingers+reference.size)

end DynamicOptimality.MultiFinger
