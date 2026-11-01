import TangoSquared.Paper20261030.MultiSourceValidity

/-! Finite prefixes and state translation for the shared-tree local
program language. Helper calls compose without free pointer operations.
-/

namespace TangoSquared.Paper20261030.MultiSourceProgram

variable {α ρ F σ τ : Type*} [DecidableEq F]

def Instruction.mapState (f : σ → τ) : Instruction σ F ρ → Instruction τ F ρ
  | .halt => .halt
  | .read finger next => .read finger (fun observed => f (next observed))
  | .nav finger action next => .nav finger action (f next)
  | .write finger fresh next => .write finger fresh (f next)
  | .copy destination origin next => .copy destination origin (f next)

inductive Steps (program : Program σ F ρ) :
    σ → Configuration F α ρ → σ → Configuration F α ρ → List (F × ρ) → Nat → Prop
  | nil (state config) : Steps program state config state config [] 0
  | next {state middle last before current after entry reads cost}
      (first : Step program state before middle current entry)
      (rest : Steps program middle current last after reads cost) :
      Steps program state before last after (entry.toList++reads) (cost+1)

theorem Step.prefix {program : Program σ F ρ} {state next : σ} {before after : Configuration F α ρ} {entry}
    (step : Step program state before next after entry) : Steps program state before next after entry.toList 1 := by
  simpa using Steps.next step (Steps.nil next after)

theorem Step.not_halted {program : Program σ F ρ} {state next : σ} {before after : Configuration F α ρ} {entry}
    (step : Step program state before next after entry) : program state ≠ .halt := by
  cases step <;> simp_all

theorem Steps.append {program : Program σ F ρ} {state middle last : σ} {before current after : Configuration F α ρ}
    {firstReads lastReads firstCost lastCost} (first : Steps program state before middle current firstReads firstCost)
    (tailRun : Steps program middle current last after lastReads lastCost) :
    Steps program state before last after (firstReads++lastReads) (firstCost+lastCost) := by
  induction first with
  | nil => simpa using tailRun
  | next step rest ih =>
    simpa only [List.append_assoc,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using Steps.next step (ih tailRun)

theorem Steps.run {program : Program σ F ρ} {state last : σ} {before after : Configuration F α ρ} {reads cost}
    (steps : Steps program state before last after reads cost) (stopped : program last = .halt) :
    Run program state before last after reads cost := by
  induction steps with
  | nil => exact .halt stopped
  | next first rest ih => exact .next first (ih stopped)

theorem Steps.then_run {program : Program σ F ρ} {state middle last : σ} {before current after : Configuration F α ρ}
    {firstReads lastReads firstCost lastCost} (first : Steps program state before middle current firstReads firstCost)
    (tailRun : Run program middle current last after lastReads lastCost) :
    Run program state before last after (firstReads++lastReads) (firstCost+lastCost) := by
  induction first with
  | nil => simpa using tailRun
  | next step rest ih =>
    simpa only [List.append_assoc,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using Run.next step (ih tailRun)

theorem Step.mapState {source : Program σ F ρ} {target : Program τ F ρ} (f : σ → τ)
    (correct : ∀ state, source state ≠ .halt → target (f state) = (source state).mapState f)
    {state next : σ} {before after : Configuration F α ρ} {entry}
    (step : Step source state before next after entry) : Step target (f state) before (f next) after entry := by
  have code := correct state step.not_halted
  cases step with
  | readNone instruction absent => exact .readNone (by simpa only [instruction,Instruction.mapState] using code) absent
  | readSome instruction present reached => exact .readSome (by simpa only [instruction,Instruction.mapState] using code) present reached
  | nav instruction present reached moved => exact .nav (by simpa only [instruction,Instruction.mapState] using code) present reached moved
  | write instruction present reached => exact .write (by simpa only [instruction,Instruction.mapState] using code) present reached
  | copy instruction => exact .copy (by simpa only [instruction,Instruction.mapState] using code)

theorem Run.map_prefix {source : Program σ F ρ} {target : Program τ F ρ} (f : σ → τ)
    (correct : ∀ state, source state ≠ .halt → target (f state) = (source state).mapState f)
    {state last : σ} {before after : Configuration F α ρ} {reads cost}
    (run : Run source state before last after reads cost) : Steps target (f state) before (f last) after reads cost := by
  induction run with
  | halt => exact .nil _ _
  | next first rest ih => exact .next (first.mapState f correct) ih

theorem Steps.wellFormed {source : Program σ F ρ} {state last : σ} {before after : Configuration F α ρ} {reads cost}
    (steps : Steps source state before last after reads cost) (valid : WellFormed before) : WellFormed after := by
  induction steps with
  | nil => exact valid
  | next first rest ih => exact ih (first.wellFormed valid)

end TangoSquared.Paper20261030.MultiSourceProgram
