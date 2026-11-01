import TangoSquared.Paper20261030.PackedOperationReadiness

/-! Composition for executions whose inspected fields are ready. These
lemmas preserve the readiness of every primitive instruction when a
helper is embedded in its caller, including its nonhalting continuation.
-/

namespace TangoSquared.Paper20261030.PackedReadiness

open ColoredStorage SourcePointer SourceLocalProgram Structural

variable {α ρ η C σ τ : Type*} [DecidableEq η] [LinearOrder C] [Fintype C]

theorem ready_mapState (identifier : ρ → η) (color : α → C) (f : σ → τ)
    (instruction : Instruction σ (Record ρ η C)) (current : Cursor α (Record ρ η C)) :
    Ready identifier color (instruction.mapState f) current ↔ Ready identifier color instruction current := by
  cases instruction <;> rfl

inductive CheckedSteps (identifier : ρ → η) (color : α → C) (program : Program σ (Record ρ η C)) :
    σ → Cursor α (Record ρ η C) → σ → Cursor α (Record ρ η C) → List (Record ρ η C) → Nat → Prop
  | nil (state current) : CheckedSteps identifier color program state current state current [] 0
  | next {state middle last before current after entry reads cost}
      (step : Step program state before middle current entry)
      (ready : Ready identifier color (program state) before)
      (rest : CheckedSteps identifier color program middle current last after reads cost) :
      CheckedSteps identifier color program state before last after (entry.toList++reads) (cost+1)

theorem step_prefix {identifier : ρ → η} {color : α → C} {program : Program σ (Record ρ η C)}
    {state next : σ} {before after : Cursor α (Record ρ η C)} {entry}
    (step : Step program state before next after entry) (ready : Ready identifier color (program state) before) :
    CheckedSteps identifier color program state before next after entry.toList 1 := by
  simpa using CheckedSteps.next step ready (CheckedSteps.nil next after)

theorem CheckedSteps.append {identifier : ρ → η} {color : α → C} {program : Program σ (Record ρ η C)}
    {state middle last : σ} {before current after : Cursor α (Record ρ η C)}
    {firstReads lastReads firstCost lastCost}
    (first : CheckedSteps identifier color program state before middle current firstReads firstCost)
    (rest : CheckedSteps identifier color program middle current last after lastReads lastCost) :
    CheckedSteps identifier color program state before last after (firstReads++lastReads) (firstCost+lastCost) := by
  induction first with
  | nil => simpa using rest
  | next step ready tail ih =>
    simpa only [List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using CheckedSteps.next step ready (ih rest)

theorem CheckedSteps.run {identifier : ρ → η} {color : α → C} {program : Program σ (Record ρ η C)}
    {state last : σ} {before after : Cursor α (Record ρ η C)} {reads cost}
    (steps : CheckedSteps identifier color program state before last after reads cost) (stopped : program last = .halt) :
    CheckedRun identifier color program state before last after reads cost := by
  induction steps with
  | nil => exact .halt stopped
  | next step ready rest ih => exact .next step ready (ih stopped)

theorem CheckedSteps.then_run {identifier : ρ → η} {color : α → C} {program : Program σ (Record ρ η C)}
    {state middle last : σ} {before current after : Cursor α (Record ρ η C)}
    {firstReads lastReads firstCost lastCost}
    (first : CheckedSteps identifier color program state before middle current firstReads firstCost)
    (rest : CheckedRun identifier color program middle current last after lastReads lastCost) :
    CheckedRun identifier color program state before last after (firstReads++lastReads) (firstCost+lastCost) := by
  induction first with
  | nil => simpa using rest
  | next step ready tail ih =>
    simpa only [List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using CheckedRun.next step ready (ih rest)

theorem CheckedSteps.change_start {identifier : ρ → η} {color : α → C} {program : Program σ (Record ρ η C)}
    {state replacement last : σ} {before after : Cursor α (Record ρ η C)} {reads cost}
    (steps : CheckedSteps identifier color program state before last after reads cost)
    (positive : 0 < cost) (same : program replacement = program state) :
    CheckedSteps identifier color program replacement before last after reads cost := by
  cases steps with
  | nil => omega
  | next step ready rest => exact .next (step.change_start same) (same.symm ▸ ready) rest

theorem CheckedRun.map_prefix {identifier : ρ → η} {color : α → C}
    {source : Program σ (Record ρ η C)} {target : Program τ (Record ρ η C)} (f : σ → τ)
    (correct : ∀ state, source state ≠ .halt → target (f state) = (source state).mapState f)
    {state last : σ} {before after : Cursor α (Record ρ η C)} {reads cost}
    (run : CheckedRun identifier color source state before last after reads cost) :
    CheckedSteps identifier color target (f state) before (f last) after reads cost := by
  induction run with
  | halt => exact .nil _ _
  | next step ready rest ih =>
    refine .next (step.mapState f correct) ?_ ih
    rw [correct _ step.not_halted,ready_mapState]
    exact ready

end TangoSquared.Paper20261030.PackedReadiness
