import DynamicOptimality.LocalProgram

/-! Composition and register-state relabeling of local programs. A finite
prefix may stop at a continuation without executing it. A completed helper
program can therefore be embedded into a caller without a free cursor move
or an uncharged data read. -/

namespace DynamicOptimality.LocalProgram

variable {α ρ σ τ : Type*}

def Instruction.mapState (f : σ → τ) : Instruction σ α ρ → Instruction τ α ρ
  | .halt => .halt
  | .read next => .read (fun view => f (next view))
  | .nav move next => .nav move (f next)
  | .write fresh next => .write fresh (f next)
  | .writeSize fresh next => .writeSize fresh (f next)

inductive Steps (program : Program σ α ρ) : σ → TangoSquared.Paper20261030.Auxiliary.Metadata.Cursor α (fun _ => ρ) →
    σ → TangoSquared.Paper20261030.Auxiliary.Metadata.Cursor α (fun _ => ρ) →
    List (TangoSquared.Paper20261030.Auxiliary.NodeRecord α (fun _ => ρ)) → Nat → Prop
  | nil (state cursor) : Steps program state cursor state cursor [] 0
  | next {state middle last before current after entry reads cost}
      (first : Step program state before middle current entry)
      (rest : Steps program middle current last after reads cost) :
      Steps program state before last after (entry.toList++reads) (cost+1)

open TangoSquared.Paper20261030.Auxiliary

theorem Step.prefix {program : Program σ α ρ} {state next : σ}
    {before after : Metadata.Cursor α (fun _ => ρ)} {entry}
    (step : Step program state before next after entry) :
    Steps program state before next after entry.toList 1 := by
  simpa using Steps.next step (Steps.nil next after)

theorem Step.change_start {program : Program σ α ρ} {state replacement next : σ}
    {before after : Metadata.Cursor α (fun _ => ρ)} {entry}
    (step : Step program state before next after entry) (same : program replacement = program state) :
    Step program replacement before next after entry := by
  cases step with
  | read instruction observed => exact .read (same.trans instruction) observed
  | nav instruction moved => exact .nav (same.trans instruction) moved
  | write instruction => exact .write (same.trans instruction)
  | writeSize instruction => exact .writeSize (same.trans instruction)

theorem Steps.change_start {program : Program σ α ρ} {state replacement last : σ}
    {before after : Metadata.Cursor α (fun _ => ρ)} {reads cost}
    (steps : Steps program state before last after reads cost) (positive : 0 < cost)
    (same : program replacement = program state) : Steps program replacement before last after reads cost := by
  cases steps with
  | nil => omega
  | next first rest => exact .next (first.change_start same) rest

theorem Steps.append {program : Program σ α ρ} {state middle last : σ}
    {before current after : Metadata.Cursor α (fun _ => ρ)} {firstReads lastReads firstCost lastCost}
    (first : Steps program state before middle current firstReads firstCost)
    (tailRun : Steps program middle current last after lastReads lastCost) :
    Steps program state before last after (firstReads++lastReads) (firstCost+lastCost) := by
  induction first with
  | nil => simpa using tailRun
  | next step rest ih =>
    simpa only [List.append_assoc,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using
      (Steps.next step (ih tailRun))

theorem Steps.run {program : Program σ α ρ} {state last : σ} {before after : Metadata.Cursor α (fun _ => ρ)}
    {reads cost} (steps : Steps program state before last after reads cost) (stopped : program last = .halt) :
    Run program state before last after reads cost := by
  induction steps with
  | nil => exact .halt stopped
  | next first rest ih => exact .next first (ih stopped)

theorem Run.positive {program : Program σ α ρ} {state last : σ} {before after : Metadata.Cursor α (fun _ => ρ)}
    {reads cost} (run : Run program state before last after reads cost) (active : program state ≠ .halt) :
    0 < cost := by
  cases run with
  | halt stopped => exact False.elim (active stopped)
  | next => omega

theorem Steps.then_run {program : Program σ α ρ} {state middle last : σ}
    {before current after : Metadata.Cursor α (fun _ => ρ)} {firstReads lastReads firstCost lastCost}
    (first : Steps program state before middle current firstReads firstCost)
    (tailRun : Run program middle current last after lastReads lastCost) :
    Run program state before last after (firstReads++lastReads) (firstCost+lastCost) := by
  induction first with
  | nil => simpa using tailRun
  | next step rest ih =>
    simpa only [List.append_assoc,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using
      (Run.next step (ih tailRun))

theorem Step.mapState {source : Program σ α ρ} {target : Program τ α ρ} (f : σ → τ)
    (correct : ∀ state, source state ≠ .halt → target (f state) = (source state).mapState f)
    {state next : σ} {before after : Metadata.Cursor α (fun _ => ρ)} {entry}
    (step : Step source state before next after entry) : Step target (f state) before (f next) after entry := by
  have code := correct state step.not_halted
  cases step with
  | read instruction observed =>
    exact .read (by simpa only [instruction,Instruction.mapState] using code) observed
  | nav instruction moved =>
    exact .nav (by simpa only [instruction,Instruction.mapState] using code) moved
  | write instruction => exact .write (by simpa only [instruction,Instruction.mapState] using code)
  | writeSize instruction => exact .writeSize (by simpa only [instruction,Instruction.mapState] using code)

theorem Run.map_prefix {source : Program σ α ρ} {target : Program τ α ρ} (f : σ → τ)
    (correct : ∀ state, source state ≠ .halt → target (f state) = (source state).mapState f)
    {state last : σ} {before after : Metadata.Cursor α (fun _ => ρ)} {reads cost}
    (run : Run source state before last after reads cost) : Steps target (f state) before (f last) after reads cost := by
  induction run with
  | halt => exact .nil _ _
  | next first rest ih => exact .next (first.mapState f correct) ih

theorem Steps.agrees_run {program : Program σ α ρ} {state middle last : σ}
    {before current after : Metadata.Cursor α (fun _ => ρ)}
    {frontReads fullReads frontCost fullCost}
    (front : Steps program state before middle current frontReads frontCost)
    (full : Run program state before last after fullReads fullCost) :
    ∃ tailReads tailCost, Run program middle current last after tailReads tailCost ∧
      fullReads = frontReads++tailReads ∧ fullCost = frontCost+tailCost := by
  induction front generalizing last after fullReads fullCost with
  | nil => exact ⟨fullReads,fullCost,full,by simp,by simp⟩
  | next first rest ih =>
    cases full with
    | halt stopped => exact False.elim (first.not_halted stopped)
    | next other more =>
      obtain ⟨rfl,rfl,rfl⟩ := first.deterministic other
      obtain ⟨tailReads,tailCost,tailRun,readEq,costEq⟩ := ih more
      exact ⟨tailReads,tailCost,tailRun,by simp only [readEq,List.append_assoc],by omega⟩

end DynamicOptimality.LocalProgram
