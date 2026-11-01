import TangoSquared.Paper20261030.ForestProgramComposition

set_option autoImplicit false

/-! Executions whose writes preserve the labels of records at the
reached physical vertex. This is stronger than preserving a global
inventory: a write cannot exchange labels between different vertices.
The label may ignore virtual-header contents. State translation and
helper-call composition retain this property without changing costs. -/

namespace TangoSquared.Paper20261030.ForestWriteLabels

open ColoredStorage SourcePointer ForestLocalProgram

variable {α ρ ι C σ τ : Type*} [DecidableEq C]

def Stable (label : ρ → ι) (instruction : Instruction σ C ρ) (forest : ProjectionForest.State C α ρ) : Prop :=
  match instruction with
  | .write q fresh _ => ∀ current, forest q = some current →
      fresh.map label = current.focus.rootRecord.map label
  | _ => True

theorem stable_mapState (label : ρ → ι) (f : σ → τ) (instruction : Instruction σ C ρ)
    (forest : ProjectionForest.State C α ρ) : Stable label (instruction.mapState f) forest ↔ Stable label instruction forest := by
  cases instruction <;> rfl

inductive Steps (label : ρ → ι) (program : Program σ C ρ) :
    σ → ProjectionForest.State C α ρ → σ → ProjectionForest.State C α ρ → List (C × List ρ) → Nat → Prop
  | nil (state forest) : Steps label program state forest state forest [] 0
  | next {state middle last before current after entry reads cost}
      (first : Step program state before middle current entry)
      (stable : Stable label (program state) before)
      (rest : Steps label program middle current last after reads cost) :
      Steps label program state before last after (entry.toList++reads) (cost+1)

inductive Run (label : ρ → ι) (program : Program σ C ρ) :
    σ → ProjectionForest.State C α ρ → σ → ProjectionForest.State C α ρ → List (C × List ρ) → Nat → Prop
  | halt {state forest} (stopped : program state = .halt) : Run label program state forest state forest [] 0
  | next {state middle last before current after entry reads cost}
      (first : Step program state before middle current entry)
      (stable : Stable label (program state) before)
      (rest : Run label program middle current last after reads cost) :
      Run label program state before last after (entry.toList++reads) (cost+1)

theorem Steps.steps {label : ρ → ι} {source : Program σ C ρ} {state last : σ}
    {before after : ProjectionForest.State C α ρ} {reads cost}
    (checked : Steps label source state before last after reads cost) :
    ForestLocalProgram.Steps source state before last after reads cost := by
  induction checked with
  | nil => exact .nil _ _
  | next first stable rest ih => exact .next first ih

theorem Run.run {label : ρ → ι} {source : Program σ C ρ} {state last : σ}
    {before after : ProjectionForest.State C α ρ} {reads cost}
    (checked : Run label source state before last after reads cost) :
    ForestLocalProgram.Run source state before last after reads cost := by
  induction checked with
  | halt stopped => exact .halt stopped
  | next first stable rest ih => exact .next first ih

theorem step_prefix {label : ρ → ι} {source : Program σ C ρ} {state next : σ}
    {before after : ProjectionForest.State C α ρ} {entry}
    (first : Step source state before next after entry) (stable : Stable label (source state) before) :
    Steps label source state before next after entry.toList 1 := by
  simpa using Steps.next first stable (Steps.nil next after)

theorem Steps.append {label : ρ → ι} {source : Program σ C ρ} {state middle last : σ}
    {before current after : ProjectionForest.State C α ρ} {firstReads lastReads firstCost lastCost}
    (first : Steps label source state before middle current firstReads firstCost)
    (rest : Steps label source middle current last after lastReads lastCost) :
    Steps label source state before last after (firstReads++lastReads) (firstCost+lastCost) := by
  induction first with
  | nil => simpa using rest
  | next step stable tail ih =>
    simpa only [List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using Steps.next step stable (ih rest)

theorem Steps.then_run {label : ρ → ι} {source : Program σ C ρ} {state middle last : σ}
    {before current after : ProjectionForest.State C α ρ} {firstReads lastReads firstCost lastCost}
    (first : Steps label source state before middle current firstReads firstCost)
    (rest : Run label source middle current last after lastReads lastCost) :
    Run label source state before last after (firstReads++lastReads) (firstCost+lastCost) := by
  induction first with
  | nil => simpa using rest
  | next step stable tail ih =>
    simpa only [List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using Run.next step stable (ih rest)

theorem Steps.run {label : ρ → ι} {source : Program σ C ρ} {state last : σ}
    {before after : ProjectionForest.State C α ρ} {reads cost}
    (steps : Steps label source state before last after reads cost) (stopped : source last = .halt) :
    Run label source state before last after reads cost := by
  induction steps with
  | nil => exact .halt stopped
  | next first stable rest ih => exact .next first stable (ih stopped)

theorem Steps.change_start {label : ρ → ι} {source : Program σ C ρ} {state replacement last : σ}
    {before after : ProjectionForest.State C α ρ} {reads cost}
    (steps : Steps label source state before last after reads cost)
    (positive : 0 < cost) (same : source replacement = source state) :
    Steps label source replacement before last after reads cost := by
  cases steps with
  | nil => omega
  | next first stable rest => exact .next (first.change_start same) (same ▸ stable) rest

theorem Run.map_prefix {label : ρ → ι} {source : Program σ C ρ} {target : Program τ C ρ}
    (f : σ → τ) (correct : ∀ state, source state ≠ .halt → target (f state) = (source state).mapState f)
    {state last : σ} {before after : ProjectionForest.State C α ρ} {reads cost}
    (run : Run label source state before last after reads cost) :
    Steps label target (f state) before (f last) after reads cost := by
  induction run with
  | halt => exact .nil _ _
  | next first stable rest ih =>
    exact .next (first.mapState f correct)
      (by rw [correct _ first.not_halted]; exact (stable_mapState _ _ _ _).mpr stable) ih

theorem of_no_writes (label : ρ → ι) {source : Program σ C ρ}
    (readonly : ∀ state q fresh next, source state ≠ .write q fresh next)
    {state last : σ} {before after : ProjectionForest.State C α ρ} {reads cost}
    (actual : ForestLocalProgram.Run source state before last after reads cost) :
    Run label source state before last after reads cost := by
  induction actual with
  | halt stopped => exact .halt stopped
  | next first rest ih =>
    refine .next first ?_ ih
    cases code : source _ with
    | write q fresh next => exact False.elim (readonly _ q fresh next code)
    | halt | read | nav => trivial

end TangoSquared.Paper20261030.ForestWriteLabels
