import ChaCha.Paper20261030.MultiSourceWriteLabels
import ChaCha.Paper20261030.MultiSourceFinish

set_option autoImplicit false

/-! Label preservation composes across a continuation selected from
actual controller registers, without adding instructions. -/

namespace ChaCha.Paper20261030.MultiSourceWriteLabels

open MultiSourceProgram

variable {α ρ ι F σ τ : Type*} [DecidableEq F]

theorem stable_mapState (label : ρ → ι) (f : σ → τ) (instruction : Instruction σ F ρ)
    (config : Configuration F α ρ) :
    Stable label (instruction.mapState f) config ↔ Stable label instruction config := by
  cases instruction <;> rfl

theorem Run.map_then {label : ρ → ι} {source : Program σ F ρ} {target : Program τ F ρ} (f : σ → τ)
    (correct : ∀ state, source state ≠ .halt → target (f state) = (source state).mapState f)
    {state last : σ} {final : τ} {before middle after : Configuration F α ρ}
    {firstReads lastReads firstCost lastCost}
    (front : Run label source state before last middle firstReads firstCost)
    (back : Run label target (f last) middle final after lastReads lastCost) :
    Run label target (f state) before final after (firstReads++lastReads) (firstCost+lastCost) := by
  induction front with
  | halt => simpa only [List.nil_append,Nat.zero_add] using back
  | next first stable rest ih =>
    have safe := (stable_mapState label f _ _).mpr stable
    rw [← correct _ first.not_halted] at safe
    simpa only [List.append_assoc,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using
      Run.next (first.mapState f correct) safe (ih back)

theorem Run.map_run {label : ρ → ι} {source : Program σ F ρ} {target : Program τ F ρ} (f : σ → τ)
    (correct : ∀ state, source state ≠ .halt → target (f state) = (source state).mapState f)
    {state last : σ} {before after : Configuration F α ρ} {reads cost}
    (run : Run label source state before last after reads cost) (stopped : target (f last) = .halt) :
    Run label target (f state) before (f last) after reads cost := by
  simpa only [List.append_nil,Nat.add_zero] using run.map_then f correct (.halt stopped)

end ChaCha.Paper20261030.MultiSourceWriteLabels

namespace ChaCha.Paper20261030.MultiSourceFinish

open MultiSourceProgram

variable {α ρ ι F σ τ π : Type*} [DecidableEq F]

theorem finish_labels {label : ρ → ι} {source : Program σ F ρ} (select : σ → π) (initial : π → τ)
    (target : π → Program τ F ρ) {state last : σ} {final : τ}
    {before middle after : Configuration F α ρ} {firstReads lastReads firstCost lastCost}
    (front : MultiSourceWriteLabels.Run label source state before last middle firstReads firstCost)
    (back : MultiSourceWriteLabels.Run label (target (select last)) (initial (select last)) middle final after lastReads lastCost) :
    MultiSourceWriteLabels.Run label (program source select initial target) (enter source select initial state) before
      (.second (select last) final) after (firstReads++lastReads) (firstCost+lastCost) := by
  have second := back.map_run (target := program source select initial target)
    (State.second (select last)) (fun _ _ => rfl)
    (by simp only [program,back.run.halted,Instruction.mapState])
  have boundary : enter source select initial last = .second (select last) (initial (select last)) := by
    simp only [enter,front.run.halted]
  apply front.map_then (enter source select initial) (enter_code source select initial target)
  rw [boundary]
  exact second

end ChaCha.Paper20261030.MultiSourceFinish
