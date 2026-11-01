import TangoSquared.Paper20261030.ForestWriteLabels
import TangoSquared.Paper20261030.PhysicalRecordFinder

set_option autoImplicit false

/-! Neighborhood lookup only reads records and follows edges. Its
existing runs therefore preserve every physical-id label at writes,
without changing their states, observations, or cost. -/

namespace TangoSquared.Paper20261030.PhysicalRecordFinder

open ColoredStorage SourcePointer ForestLocalProgram Structural PhysicalForestMetadata

variable {α ρ ι η C : Type*} [DecidableEq ι] [DecidableEq η] [LinearOrder C]

theorem parent_no_write (q : C) (state : ParentState ρ ι) (other : C) (fresh : List (Record ρ ι)) (next) :
    parentProgram q state ≠ .write other fresh next := by
  cases state with
  | error => simp only [parentProgram,SourceForestLift.program,ne_eq,reduceCtorEq,not_false_eq_true]
  | running phase => cases phase <;>
    simp only [parentProgram,SourceForestLift.program,ParentObservationController.program,ne_eq,reduceCtorEq,not_false_eq_true]

theorem no_write (identifier : ρ → η) (wanted : η) (state : State ρ ι C)
    (q : C) (fresh : List (Record ρ ι)) (next : State ρ ι C) :
    program identifier wanted state ≠ .write q fresh next := by
  cases state with
  | found | current => simp only [program,ne_eq,reduceCtorEq,not_false_eq_true]
  | scan colors => cases colors with
    | nil => simp only [program,ne_eq,reduceCtorEq,not_false_eq_true]
    | cons first rest =>
      simp only [program]
      generalize h : parentProgram (ρ := ρ) (ι := ι) first (.running .start) = command
      cases command <;> simp only [Instruction.mapState,ne_eq,reduceCtorEq,not_false_eq_true]
      exact False.elim (parent_no_write first (.running .start) _ _ _ h)
  | parent first rest phase =>
    simp only [program]
    generalize h : parentProgram first phase = command
    cases command <;> simp only [Instruction.mapState,ne_eq,reduceCtorEq,not_false_eq_true]
    exact False.elim (parent_no_write first phase _ _ _ h)

theorem write_labels (identifier : ρ → η) (wanted : η) {state last : State ρ ι C}
    {before after : ProjectionForest.State C α (Record ρ ι)} {reads cost}
    (run : Run (program identifier wanted) state before last after reads cost) :
    ForestWriteLabels.Run (fun record => record.1.1) (program identifier wanted) state before last after reads cost :=
  ForestWriteLabels.of_no_writes _ (no_write identifier wanted) run

end TangoSquared.Paper20261030.PhysicalRecordFinder
