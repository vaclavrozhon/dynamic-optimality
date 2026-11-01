import TangoSquared.Paper20261030.MultiSourceScalarInvariant
import TangoSquared.Paper20261030.MultiSourceStationaryRegisters
import TangoSquared.Paper20261030.MultiSourceRegisterExtension
import TangoSquared.Paper20261030.MultiSourceDownward

set_option autoImplicit false

/-! The masked component-entry walk changes no presence bits and does
not move any additional register. -/

namespace TangoSquared.Paper20261030.MultiSourceDownward

open MultiSourceProgram

variable {ρ F G : Type*} [DecidableEq F] [DecidableEq G]

theorem extended_keeps_copy (finger : Sum F G) (schedule : Schedule F) :
    KeepsCopy finger (MultiSourceRegisterExtension.program (ρ := ρ) program schedule) := by
  cases schedule with
  | nil => trivial
  | cons first rest => obtain ⟨finger,right⟩ := first; trivial

theorem masked_stationary (extra : G) (state : MultiSourceMask.State (Schedule F) (Sum F G)) :
    (MultiSourceMask.program (MultiSourceRegisterExtension.program (ρ := ρ) program) state).EdgeOnly ∧
      KeepsFinger (.inr extra) (MultiSourceMask.program (MultiSourceRegisterExtension.program (ρ := ρ) program) state) := by
  obtain ⟨bits,schedule⟩ := state
  cases schedule with
  | nil => trivial
  | cons first rest =>
    obtain ⟨finger,right⟩ := first
    cases right <;> simp [MultiSourceMask.program,MultiSourceRegisterExtension.program,
      MultiSourceRegisterExtension.instruction,program,Instruction.EdgeOnly,KeepsFinger]

end TangoSquared.Paper20261030.MultiSourceDownward
