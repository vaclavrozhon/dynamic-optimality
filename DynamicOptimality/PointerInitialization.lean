import DynamicOptimality.HullPointer

/-! Linear root-returning initialization in the shared ordinary BST model.
This reuses the existing restricted-rotation flattening theorem. No
ordering hypothesis or additional keys are needed for the transformation. -/

namespace DynamicOptimality

open TangoSquared TangoSquared.MTR TangoSquared.MTR.Pointer
open TangoSquared.Paper20261030.Auxiliary

variable {α : Type*}

theorem restricted_steps_pointer {before after : RawTree α} {count : Nat}
    (steps : MTR.Tree.RestrictedSteps count before after) : Rearranges before after (3*count) := by
  induction steps with
  | refl => exact rearranges_refl _ _
  | cons step rest ih =>
    have run := (restricted_pointer step).trans ih
    simpa only [Nat.mul_add,Nat.mul_one,Nat.add_comm] using run

theorem initialize_pointer (before after : RawTree α) (word : before.inorder = after.inorder) :
    Rearranges before after (18*before.size) := by
  obtain ⟨count,bound,steps⟩ := MTR.Tree.restricted_rotation_linear before after word
  have sizes := steps.size_eq
  exact (restricted_steps_pointer steps).mono (by omega)

theorem prepend_pointer_initialization {before middle after : RawTree α} {requests : List α}
    {initialCost runCost : Nat} (initialization : Trace (.atRoot before) [] (.atRoot middle) initialCost)
    (execution : Pointer.Execution middle requests after runCost) (nonempty : requests ≠ []) :
    Pointer.Execution before requests after (initialCost+runCost) := by
  cases execution with
  | nil => exact False.elim (nonempty rfl)
  | @cons middle next after key requests firstCost lastCost first rest =>
    obtain ⟨final,tree,run⟩ := first
    have combined : Pointer.Access key before next (initialCost+firstCost) :=
      ⟨final,tree,trace_append initialization run⟩
    simpa only [Nat.add_assoc] using Pointer.Execution.cons combined rest

end DynamicOptimality
