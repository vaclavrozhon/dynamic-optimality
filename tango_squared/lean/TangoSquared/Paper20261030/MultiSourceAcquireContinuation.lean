import TangoSquared.Paper20261030.MultiSourceParkContinuation

set_option autoImplicit false

/-! Park one reached root, acquire a second pointer by an actual local
program, and then run a continuation. The acquisition contributes its
reads and full cost; it is never a semantic pointer assignment. -/

namespace TangoSquared.Paper20261030.MultiSourceAcquireContinuation

open MultiSourceProgram

variable {α ρ F σ τ : Type*} [DecidableEq F]

inductive State (σ τ : Type*) where
  | none
  | acquiring (state : τ)
  | some (state : σ)

def enter (acquire : Program τ F ρ) (initial : σ) (state : τ) : State σ τ :=
  match acquire state with
  | .halt => .some initial
  | _ => .acquiring state

def program (destination origin : F) (acquire : Program τ F ρ) (acquireInitial : τ)
    (body : Program σ F ρ) (initial : σ) : Program (State σ τ) F ρ
  | .none => .copy destination origin (enter acquire initial acquireInitial)
  | .acquiring state => (acquire state).mapState (enter acquire initial)
  | .some state => (body state).mapState State.some

theorem enter_code (destination origin : F) (acquire : Program τ F ρ) (acquireInitial : τ)
    (body : Program σ F ρ) (initial : σ) (state : τ) (running : acquire state ≠ .halt) :
    program destination origin acquire acquireInitial body initial (enter acquire initial state) =
      (acquire state).mapState (enter acquire initial) := by
  cases instruction : acquire state <;> simp_all [enter,program]

theorem execute (destination origin : F) (acquire : Program τ F ρ) (acquireInitial acquireLast : τ)
    (body : Program σ F ρ) (initial last : σ)
    (before middle after : Configuration F α ρ) {routeReads bodyReads routeCost bodyCost}
    (route : Run acquire acquireInitial (copyResult before destination origin) acquireLast middle routeReads routeCost)
    (continuation : Run body initial middle last after bodyReads bodyCost) :
    Run (program destination origin acquire acquireInitial body initial) .none before (.some last) after
      (routeReads ++ bodyReads) (routeCost + bodyCost + 1) := by
  have first := route.map_prefix
    (target := program destination origin acquire acquireInitial body initial)
    (enter acquire initial) (enter_code destination origin acquire acquireInitial body initial)
  have second := continuation.map_prefix
    (target := program destination origin acquire acquireInitial body initial)
    State.some (fun _ _ => rfl)
  have stopped : enter acquire initial acquireLast = .some initial := by
    simp only [enter,route.halted]
  rw [stopped] at first
  have combined := (first.append second).run
    (by simp only [program,continuation.halted,Instruction.mapState])
  exact .next (Step.copy
    (program := program destination origin acquire acquireInitial body initial)
    (state := .none) rfl) combined

end TangoSquared.Paper20261030.MultiSourceAcquireContinuation
