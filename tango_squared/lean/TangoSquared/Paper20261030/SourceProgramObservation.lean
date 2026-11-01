import TangoSquared.Paper20261030.SourceProgramExtension
import TangoSquared.Paper20261030.LeafVisit

/-! Observations made by an actual source program. `ReachesLeafRead`
exhibits a program prefix ending at a specified physical leaf with a read
as its next instruction. Determinism makes this read part of every
completed run from the same initial state and cursor. -/

namespace TangoSquared.Paper20261030.SourceLocalProgram

open ColoredStorage SourcePointer

variable {α ρ σ τ : Type*}

theorem Steps.trace {program : Program σ ρ} {state last : σ} {before after : Cursor α ρ} {reads cost}
    (steps : Steps program state before last after reads cost) : Trace before reads after cost := by
  induction steps with
  | nil => exact .nil _
  | next first rest ih => simpa only [Nat.add_comm] using first.trace.append ih

theorem Steps.mapState {source : Program σ ρ} {target : Program τ ρ} (f : σ → τ)
    (correct : ∀ state, source state ≠ .halt → target (f state) = (source state).mapState f)
    {state last : σ} {before after : Cursor α ρ} {reads cost}
    (steps : Steps source state before last after reads cost) : Steps target (f state) before (f last) after reads cost := by
  induction steps with
  | nil => exact .nil _ _
  | next first rest ih => exact .next (first.mapState f correct) ih

theorem Steps.extend {program : Program σ ρ} {state last : σ} {before after : Cursor α ρ} {reads cost}
    (steps : Steps program state before last after reads cost) (outside : List (Frame α ρ)) :
    Steps program state (before.extend outside) last (after.extend outside) reads cost := by
  induction steps with
  | nil => exact .nil _ _
  | next first rest ih => exact .next (first.extend outside) ih

theorem Steps.agrees_run {program : Program σ ρ} {state middle last : σ} {before current after : Cursor α ρ}
    {frontReads fullReads frontCost fullCost} (front : Steps program state before middle current frontReads frontCost)
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

def ReachesLeafRead (program : Program σ ρ) (initial : σ) (before : Cursor α ρ) (key : α) : Prop :=
  ∃ (state : σ) (atLeaf : Cursor α ρ) (record : ρ) (reads : List ρ) (cost : Nat) (next : ρ → Bool → σ),
    Steps program initial before state atLeaf reads cost ∧ atLeaf.focus = .leaf key record ∧ program state = .read next

theorem ReachesLeafRead.prepend {program : Program σ ρ} {initial middle : σ} {before current : Cursor α ρ}
    {key reads cost} (first : Steps program initial before middle current reads cost)
    (reaches : ReachesLeafRead program middle current key) : ReachesLeafRead program initial before key := by
  obtain ⟨state,atLeaf,record,observed,budget,next,steps,focus,instruction⟩ := reaches
  exact ⟨state,atLeaf,record,_,_,next,first.append steps,focus,instruction⟩

theorem ReachesLeafRead.mapState {source : Program σ ρ} {target : Program τ ρ} (f : σ → τ)
    (correct : ∀ state, source state ≠ .halt → target (f state) = (source state).mapState f)
    {initial : σ} {before : Cursor α ρ} {key} (reaches : ReachesLeafRead source initial before key) :
    ReachesLeafRead target (f initial) before key := by
  obtain ⟨state,atLeaf,record,reads,cost,next,steps,focus,instruction⟩ := reaches
  have active : source state ≠ .halt := by rw [instruction]; intro impossible; cases impossible
  refine ⟨f state,atLeaf,record,reads,cost,fun record leaf => f (next record leaf),steps.mapState f correct,focus,?_⟩
  rw [correct state active,instruction]
  rfl

theorem ReachesLeafRead.extend {program : Program σ ρ} {initial : σ} {before : Cursor α ρ} {key}
    (reaches : ReachesLeafRead program initial before key) (outside : List (Frame α ρ)) :
    ReachesLeafRead program initial (before.extend outside) key := by
  obtain ⟨state,atLeaf,record,reads,cost,next,steps,focus,instruction⟩ := reaches
  exact ⟨state,atLeaf.extend outside,record,reads,cost,next,steps.extend outside,focus,instruction⟩

/-- The read occurs within this completed execution and its exact cost. -/
theorem ReachesLeafRead.trace {program : Program σ ρ} {initial last : σ} {before after : Cursor α ρ}
    {key reads cost} (reaches : ReachesLeafRead program initial before key)
    (run : Run program initial before last after reads cost) :
    ∃ (atLeaf : Cursor α ρ) (record : ρ) (firstReads lastReads : List ρ) (firstCost lastCost : Nat),
      Trace before firstReads atLeaf firstCost ∧ atLeaf.focus = .leaf key record ∧
      Trace atLeaf (record::lastReads) after lastCost ∧ firstCost+lastCost = cost := by
  obtain ⟨state,atLeaf,record,frontReads,frontCost,next,front,focus,instruction⟩ := reaches
  have read : Step program state atLeaf (next atLeaf.focus.rootRecord (isLeaf atLeaf.focus)) atLeaf
      (some atLeaf.focus.rootRecord) := .read instruction
  obtain ⟨tailReads,tailCost,tailRun,_,costEq⟩ := (front.append read.prefix).agrees_run run
  refine ⟨atLeaf,record,frontReads,tailReads,frontCost,tailCost+1,front.trace,focus,?_,by omega⟩
  simpa only [focus,Source.rootRecord] using SourcePointer.Trace.read tailRun.trace

end TangoSquared.Paper20261030.SourceLocalProgram
