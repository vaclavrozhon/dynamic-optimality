import ChaCha.Paper20261030.SourceLocalProgram

/-! Finite prefixes and composition for the existing source-controller
language. A helper's final state can be replaced by its caller's next
instruction without introducing a free move or record observation. -/

namespace ChaCha.Paper20261030.SourceLocalProgram

open ColoredStorage SourcePointer

variable {α ρ σ τ : Type*}

def Instruction.mapState (f : σ → τ) : Instruction σ ρ → Instruction τ ρ
  | .halt => .halt
  | .read next => .read (fun entry leaf => f (next entry leaf))
  | .nav action next => .nav action (f next)
  | .write fresh next => .write fresh (f next)

inductive Steps (program : Program σ ρ) : σ → Cursor α ρ → σ → Cursor α ρ → List ρ → Nat → Prop
  | nil (state cursor) : Steps program state cursor state cursor [] 0
  | next {state middle last before current after entry reads cost}
      (first : Step program state before middle current entry)
      (rest : Steps program middle current last after reads cost) :
      Steps program state before last after (entry.toList++reads) (cost+1)

theorem Step.prefix {program : Program σ ρ} {state next : σ} {before after : Cursor α ρ} {entry}
    (step : Step program state before next after entry) : Steps program state before next after entry.toList 1 := by
  simpa using Steps.next step (Steps.nil next after)

theorem Step.not_halted {program : Program σ ρ} {state next : σ} {before after : Cursor α ρ} {entry}
    (step : Step program state before next after entry) : program state ≠ .halt := by
  cases step <;> simp_all

theorem Step.change_start {program : Program σ ρ} {state replacement next : σ}
    {before after : Cursor α ρ} {entry} (step : Step program state before next after entry)
    (same : program replacement = program state) : Step program replacement before next after entry := by
  cases step with
  | read instruction => exact .read (same.trans instruction)
  | nav instruction moved => exact .nav (same.trans instruction) moved
  | write instruction => exact .write (same.trans instruction)

theorem Steps.change_start {program : Program σ ρ} {state replacement last : σ}
    {before after : Cursor α ρ} {reads cost} (steps : Steps program state before last after reads cost)
    (positive : 0 < cost) (same : program replacement = program state) :
    Steps program replacement before last after reads cost := by
  cases steps with
  | nil => omega
  | next first rest => exact .next (first.change_start same) rest

theorem Steps.append {program : Program σ ρ} {state middle last : σ} {before current after : Cursor α ρ}
    {firstReads lastReads firstCost lastCost} (first : Steps program state before middle current firstReads firstCost)
    (tailRun : Steps program middle current last after lastReads lastCost) :
    Steps program state before last after (firstReads++lastReads) (firstCost+lastCost) := by
  induction first with
  | nil => simpa using tailRun
  | next step rest ih =>
    simpa only [List.append_assoc,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using Steps.next step (ih tailRun)

theorem Steps.run {program : Program σ ρ} {state last : σ} {before after : Cursor α ρ} {reads cost}
    (steps : Steps program state before last after reads cost) (stopped : program last = .halt) :
    Run program state before last after reads cost := by
  induction steps with
  | nil => exact .halt stopped
  | next first rest ih => exact .next first (ih stopped)

theorem Steps.then_run {program : Program σ ρ} {state middle last : σ} {before current after : Cursor α ρ}
    {firstReads lastReads firstCost lastCost} (first : Steps program state before middle current firstReads firstCost)
    (tailRun : Run program middle current last after lastReads lastCost) :
    Run program state before last after (firstReads++lastReads) (firstCost+lastCost) := by
  induction first with
  | nil => simpa using tailRun
  | next step rest ih =>
    simpa only [List.append_assoc,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using Run.next step (ih tailRun)

theorem Step.mapState {source : Program σ ρ} {target : Program τ ρ} (f : σ → τ)
    (correct : ∀ state, source state ≠ .halt → target (f state) = (source state).mapState f)
    {state next : σ} {before after : Cursor α ρ} {entry}
    (step : Step source state before next after entry) : Step target (f state) before (f next) after entry := by
  have code := correct state step.not_halted
  cases step with
  | read instruction => exact .read (by simpa only [instruction,Instruction.mapState] using code)
  | nav instruction moved => exact .nav (by simpa only [instruction,Instruction.mapState] using code) moved
  | write instruction => exact .write (by simpa only [instruction,Instruction.mapState] using code)

theorem Run.map_prefix {source : Program σ ρ} {target : Program τ ρ} (f : σ → τ)
    (correct : ∀ state, source state ≠ .halt → target (f state) = (source state).mapState f)
    {state last : σ} {before after : Cursor α ρ} {reads cost}
    (run : Run source state before last after reads cost) : Steps target (f state) before (f last) after reads cost := by
  induction run with
  | halt => exact .nil _ _
  | next first rest ih => exact .next (first.mapState f correct) ih

end ChaCha.Paper20261030.SourceLocalProgram
