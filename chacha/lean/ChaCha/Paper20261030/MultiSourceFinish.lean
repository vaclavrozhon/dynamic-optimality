import ChaCha.Paper20261030.MultiSourceComposition
import ChaCha.Paper20261030.MultiSourceService

/-! A local continuation selected from a halted controller's registers.
Only the selected finite data are retained. The last source instruction
enters the continuation directly, so no free observation or pointer move
is introduced at the boundary.
-/

namespace ChaCha.Paper20261030.MultiSourceFinish

open MultiSourceProgram

variable {α ρ F σ τ π : Type*} [DecidableEq F]

inductive State (σ τ π : Type*) where
  | first (phase : σ)
  | second (parameters : π) (phase : τ)

def enter (source : Program σ F ρ) (select : σ → π) (initial : π → τ) (state : σ) : State σ τ π :=
  match source state with
  | .halt => .second (select state) (initial (select state))
  | _ => .first state

def program (source : Program σ F ρ) (select : σ → π) (initial : π → τ)
    (target : π → Program τ F ρ) : Program (State σ τ π) F ρ
  | .first state => (source state).mapState (enter source select initial)
  | .second parameters state => (target parameters state).mapState (State.second parameters)

theorem enter_code (source : Program σ F ρ) (select : σ → π) (initial : π → τ)
    (target : π → Program τ F ρ) (state : σ) (active : source state ≠ .halt) :
    program source select initial target (enter source select initial state) =
      (source state).mapState (enter source select initial) := by
  cases instruction : source state <;> simp_all [enter,program]

theorem finish {source : Program σ F ρ} (select : σ → π) (initial : π → τ)
    (target : π → Program τ F ρ) {state last : σ} {final : τ}
    {before middle after : Configuration F α ρ} {firstReads lastReads firstCost lastCost}
    (front : Run source state before last middle firstReads firstCost)
    (back : Run (target (select last)) (initial (select last)) middle final after lastReads lastCost) :
    Run (program source select initial target) (enter source select initial state) before
      (.second (select last) final) after (firstReads++lastReads) (firstCost+lastCost) := by
  have first := front.map_prefix (target := program source select initial target) (enter source select initial)
    (enter_code source select initial target)
  have second := back.map_prefix (target := program source select initial target) (State.second (select last)) (fun _ _ => rfl)
  have boundary : enter source select initial last = .second (select last) (initial (select last)) := by
    simp only [enter,front.halted]
  rw [boundary] at first
  exact (first.append second).run (by simp only [program,back.halted,Instruction.mapState])

end ChaCha.Paper20261030.MultiSourceFinish
