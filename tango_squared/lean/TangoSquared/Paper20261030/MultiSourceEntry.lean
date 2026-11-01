import TangoSquared.Paper20261030.MultiSourceDownward
import TangoSquared.Paper20261030.MultiSourceService

/-! A charged entry schedule followed by a running local program.
The schedule is stored explicitly; component callers use at most five
directions acquired from their header's two wing-presence bits.
-/

namespace TangoSquared.Paper20261030.MultiSourceEntry

open MultiSourceProgram

variable {α ρ F σ : Type*} [DecidableEq F]

inductive State (σ F : Type*) where
  | entering (finger : F) (right : Bool) (rest : MultiSourceDownward.Schedule F) (next : σ)
  | running (phase : σ)

def enter (next : σ) : MultiSourceDownward.Schedule F → State σ F
  | [] => .running next
  | (finger,right)::rest => .entering finger right rest next

def program (source : Program σ F ρ) : Program (State σ F) F ρ
  | .entering finger right rest next => .nav finger (if right then .right else .left) (enter next rest)
  | .running phase => (source phase).mapState State.running

theorem entry_code (source : Program σ F ρ) (next : σ) (schedule : MultiSourceDownward.Schedule F)
    (active : MultiSourceDownward.program (ρ := ρ) schedule ≠ .halt) :
    program source (enter next schedule) =
      (MultiSourceDownward.program schedule).mapState (enter next) := by
  cases schedule with
  | nil => exact False.elim (active rfl)
  | cons first rest => rcases first with ⟨finger,right⟩; rfl

theorem entry_run {source : Program σ F ρ} {state last : σ}
    (schedule : MultiSourceDownward.Schedule F) (before middle after : Configuration F α ρ)
    (evaluated : MultiSourceDownward.execute before schedule = some middle) {reads cost}
    (run : Run source state middle last after reads cost) :
    Run (program source) (enter state schedule) before (.running last) after reads (schedule.length+cost) := by
  have steps := (MultiSourceDownward.execute_run schedule before middle evaluated).map_prefix
    (target := program source) (enter state) (entry_code source state)
  have rest := run.map_prefix (target := program source) State.running (fun _ _ => rfl)
  have stopped : program source (.running last) = .halt := by
    simp only [program,run.halted,Instruction.mapState]
  exact steps.then_run (rest.run stopped)

end TangoSquared.Paper20261030.MultiSourceEntry
