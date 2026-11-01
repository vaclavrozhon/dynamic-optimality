import TangoSquared.Paper20261030.LocalStructuralWrite
import TangoSquared.Paper20261030.SourceProgramObservation

/-! A fixed compiler maintaining structural annotations for each local
source instruction. Its source program receives the original payload and
leaf bit. Auxiliary reads and writes are internal to the compiler.

Correctness at a rotation or a write requires unique identifiers in the
current whole source tree, so the parent repair can select its return
edge. The execution theorem states this reachable-state invariant
explicitly; it must be established for an application of the compiler.
-/

namespace TangoSquared.Paper20261030.Structural.Compiler

open ColoredStorage SourcePointer SourceLocalProgram
open DynamicOptimality.LocalProgram (Move)

variable {α ρ ι C σ : Type*} [DecidableEq C] [DecidableEq ι]

abbrev RotationState (ρ ι C : Type*) := ContextController.State (RotationController.State ρ ι C) ρ ι C
abbrev WriteState (ρ ι C : Type*) := ContextController.State (WriteController.State ρ ι C) ρ ι C

inductive State (σ ρ ι C : Type*) where
  | ready (state : σ)
  | rotating (right : Bool) (next : σ) (phase : RotationState ρ ι C)
  | writing (fresh : ρ) (next : σ) (phase : WriteState ρ ι C)

def finishRotation (right : Bool) (next : σ) : RotationState ρ ι C → State σ ρ ι C
  | .done => .ready next
  | phase => .rotating right next phase

def finishWrite (fresh : ρ) (next : σ) : WriteState ρ ι C → State σ ρ ι C
  | .done => .ready next
  | phase => .writing fresh next phase

def rotationProgram (identifier : ρ → ι) (right : Bool) : Program (RotationState ρ ι C) (ρ × Fields ι C) :=
  ContextController.program identifier (RotationController.program identifier right) .start

def writeProgram (identifier : ρ → ι) (fresh : ρ) : Program (WriteState ρ ι C) (ρ × Fields ι C) :=
  ContextController.program identifier (WriteController.program identifier fresh) .start

def program (identifier : ρ → ι) (source : Program σ ρ) : Program (State σ ρ ι C) (ρ × Fields ι C)
  | .ready state => match source state with
    | .halt => .halt
    | .read next => .read (fun record leaf => .ready (next record.1 leaf))
    | .nav .rotateRight next => (rotationProgram identifier true .start).mapState (finishRotation true next)
    | .nav .rotateLeft next => (rotationProgram identifier false .start).mapState (finishRotation false next)
    | .nav action next => .nav action (.ready next)
    | .write fresh next => (writeProgram identifier fresh .start).mapState (finishWrite fresh next)
  | .rotating right next phase => (rotationProgram identifier right phase).mapState (finishRotation right next)
  | .writing fresh next phase => (writeProgram identifier fresh phase).mapState (finishWrite fresh next)

theorem rotation_code (identifier : ρ → ι) (source : Program σ ρ) (right : Bool)
    (next : σ) (phase : RotationState ρ ι C) (active : rotationProgram identifier right phase ≠ .halt) :
    program identifier source (finishRotation right next phase) =
      (rotationProgram identifier right phase).mapState (finishRotation right next) := by
  cases phase with
  | done => exact False.elim (active rfl)
  | start | running | parent => rfl

theorem write_code (identifier : ρ → ι) (source : Program σ ρ)
    (fresh : ρ) (next : σ) (phase : WriteState ρ ι C) (active : writeProgram identifier fresh phase ≠ .halt) :
    program identifier source (finishWrite fresh next phase) =
      (writeProgram identifier fresh phase).mapState (finishWrite fresh next) := by
  cases phase with
  | done => exact False.elim (active rfl)
  | start | running | parent => rfl

omit [DecidableEq ι] in
theorem isLeaf_annotate (identifier : ρ → ι) (color : α → C) (parent : Option ι) (source : Source α ρ) :
    isLeaf (annotate identifier color parent source) = isLeaf source := by
  cases source <;> rfl

omit [DecidableEq ι] in
theorem navigate_direct (identifier : ρ → ι) (color : α → C) (action : Move)
    (notRight : action ≠ .rotateRight) (notLeft : action ≠ .rotateLeft)
    {before after : Cursor α ρ} (moved : navigate action before = some after) :
    navigate action (cursor identifier color before) = some (cursor identifier color after) := by
  rcases before with ⟨focus,outside⟩
  cases action with
  | rotateRight => exact False.elim (notRight rfl)
  | rotateLeft => exact False.elim (notLeft rfl)
  | left => cases focus with
    | leaf => simp [navigate] at moved
    | fork => cases Option.some.inj moved; rfl
  | right => cases focus with
    | leaf => simp [navigate] at moved
    | fork => cases Option.some.inj moved; rfl
  | up => cases outside with
    | nil => simp [navigate] at moved
    | cons frame rest => cases frame <;> cases Option.some.inj moved <;> rfl

theorem rotation_step (identifier : ρ → ι) (color : α → C) (source : Program σ ρ)
    (state next : σ) (right : Bool)
    (instruction : source state = .nav (if right then .rotateRight else .rotateLeft) next)
    {before after : Cursor α ρ}
    (moved : navigate (if right then .rotateRight else .rotateLeft) before = some after)
    (unique : (before.tree.inventory identifier).Nodup) :
    ∃ reads cost, Steps (program identifier source) (.ready state) (cursor identifier color before)
      (.ready next) (cursor identifier color after) reads cost ∧ cost ≤ 19 := by
  have kernel : ∃ reads cost, Run (rotationProgram identifier right) .start (cursor identifier color before)
      .done (cursor identifier color after) reads cost ∧ cost ≤ 19 := by
    rcases before with ⟨focus,outside⟩
    cases right with
    | true => cases focus with
      | leaf => simp [navigate] at moved
      | fork q l w => cases l with
        | leaf => simp [navigate] at moved
        | fork p u v =>
          cases Option.some.inj moved
          exact ContextController.rotate_right identifier color u v w p q outside unique
    | false => cases focus with
      | leaf => simp [navigate] at moved
      | fork p u r => cases r with
        | leaf => simp [navigate] at moved
        | fork q v w =>
          cases Option.some.inj moved
          exact ContextController.rotate_left identifier color u v w p q outside unique
  obtain ⟨reads,cost,run,bounded⟩ := kernel
  have positive : 0 < cost := by cases run with
    | next => omega
  have steps := run.map_prefix (finishRotation right next) (rotation_code identifier source right next)
  refine ⟨reads,cost,steps.change_start positive ?_,bounded⟩
  cases right <;> simp [program,instruction,finishRotation]

theorem step (identifier : ρ → ι) (color : α → C) {source : Program σ ρ}
    {state next : σ} {before after : Cursor α ρ} {entry}
    (execution : SourceLocalProgram.Step source state before next after entry)
    (unique : (before.tree.inventory identifier).Nodup) :
    ∃ reads cost, Steps (program identifier source) (.ready state) (cursor identifier color before)
      (.ready next) (cursor identifier color after) reads cost ∧ cost ≤ 19 := by
  cases execution with
  | read instruction =>
    rename_i nextRead
    have actual := SourceLocalProgram.Step.read (program := program (C := C) identifier source)
      (state := .ready state) (cursor := cursor identifier color before)
      (next := fun record leaf => .ready (nextRead record.1 leaf))
      (by simp only [program,instruction])
    refine ⟨[(cursor identifier color before).focus.rootRecord],1,?_,by decide⟩
    simpa only [cursor,annotate_root,isLeaf_annotate,Option.toList_some] using actual.prefix
  | nav instruction moved =>
    rename_i action
    cases action with
    | rotateRight => exact rotation_step identifier color source state _ true instruction moved unique
    | rotateLeft => exact rotation_step identifier color source state _ false instruction moved unique
    | left =>
      have actual : SourceLocalProgram.Step (program identifier source) (.ready state) (cursor identifier color before)
          (.ready next) (cursor identifier color after) none :=
        .nav (by simp only [program,instruction]) (navigate_direct identifier color .left (by intro h; cases h) (by intro h; cases h) moved)
      exact ⟨[],1,actual.prefix,by decide⟩
    | right =>
      have actual : SourceLocalProgram.Step (program identifier source) (.ready state) (cursor identifier color before)
          (.ready next) (cursor identifier color after) none :=
        .nav (by simp only [program,instruction]) (navigate_direct identifier color .right (by intro h; cases h) (by intro h; cases h) moved)
      exact ⟨[],1,actual.prefix,by decide⟩
    | up =>
      have actual : SourceLocalProgram.Step (program identifier source) (.ready state) (cursor identifier color before)
          (.ready next) (cursor identifier color after) none :=
        .nav (by simp only [program,instruction]) (navigate_direct identifier color .up (by intro h; cases h) (by intro h; cases h) moved)
      exact ⟨[],1,actual.prefix,by decide⟩
  | write instruction =>
    rename_i fresh
    obtain ⟨reads,cost,run,bounded⟩ := WriteController.write_cursor identifier color before.focus fresh before.ancestors unique
    have positive : 0 < cost := by cases run with
        | next => omega
    have steps := run.map_prefix (finishWrite fresh next) (write_code identifier source fresh next)
    refine ⟨reads,cost,steps.change_start positive ?_,by omega⟩
    simp only [program,instruction,finishWrite]

/-- An application invariant, checked at every source instruction boundary.
It is stronger than uniqueness of only the initial and final trees. -/
def UniqueFrom (identifier : ρ → ι) (source : Program σ ρ) (initial : σ) (before : Cursor α ρ) : Prop :=
  ∀ state current reads cost, Steps source initial before state current reads cost →
    (current.tree.inventory identifier).Nodup

omit [DecidableEq C] [DecidableEq ι] in
theorem UniqueFrom.current {identifier : ρ → ι} {source : Program σ ρ} {initial : σ} {before : Cursor α ρ}
    (unique : UniqueFrom identifier source initial before) : (before.tree.inventory identifier).Nodup :=
  unique initial before [] 0 (.nil _ _)

omit [DecidableEq C] [DecidableEq ι] in
theorem UniqueFrom.after {identifier : ρ → ι} {source : Program σ ρ} {initial state : σ}
    {before current : Cursor α ρ} {reads cost}
    (unique : UniqueFrom identifier source initial before) (steps : Steps source initial before state current reads cost) :
    UniqueFrom identifier source state current := by
  intro last after tailReads tailCost tail
  exact unique last after _ _ (steps.append tail)

theorem compile_steps (identifier : ρ → ι) (color : α → C) {source : Program σ ρ}
    {initial last : σ} {before after : Cursor α ρ} {reads cost}
    (steps : Steps source initial before last after reads cost)
    (unique : UniqueFrom identifier source initial before) :
    ∃ actualReads actualCost,
      Steps (program identifier source) (.ready initial) (cursor identifier color before)
        (.ready last) (cursor identifier color after) actualReads actualCost ∧ actualCost ≤ 19*cost := by
  induction steps with
  | nil => exact ⟨[],0,.nil _ _,by omega⟩
  | next first rest ih =>
    obtain ⟨firstReads,firstCost,compiled,firstBound⟩ := step identifier color first unique.current
    obtain ⟨lastReads,lastCost,tail,lastBound⟩ := ih (unique.after first.prefix)
    exact ⟨_,_,compiled.append tail,by omega⟩

theorem compile_run (identifier : ρ → ι) (color : α → C) {source : Program σ ρ}
    {initial last : σ} {before after : Cursor α ρ} {reads cost}
    (run : Run source initial before last after reads cost)
    (unique : UniqueFrom identifier source initial before) :
    ∃ actualReads actualCost,
      Run (program identifier source) (.ready initial) (cursor identifier color before)
        (.ready last) (cursor identifier color after) actualReads actualCost ∧ actualCost ≤ 19*cost := by
  induction run with
  | halt stopped => exact ⟨[],0,.halt (by simp only [program,stopped]),by omega⟩
  | next first rest ih =>
    obtain ⟨firstReads,firstCost,compiled,firstBound⟩ := step identifier color first unique.current
    obtain ⟨lastReads,lastCost,tail,lastBound⟩ := ih (unique.after first.prefix)
    exact ⟨_,_,compiled.then_run tail,by omega⟩

theorem compile_leaf_read (identifier : ρ → ι) (color : α → C) {source : Program σ ρ}
    {initial : σ} {before : Cursor α ρ} {key : α}
    (reaches : ReachesLeafRead source initial before key)
    (unique : UniqueFrom identifier source initial before) :
    ReachesLeafRead (program identifier source) (.ready initial) (cursor identifier color before) key := by
  obtain ⟨state,atLeaf,record,reads,cost,next,steps,focus,instruction⟩ := reaches
  obtain ⟨actualReads,actualCost,compiled,bounded⟩ := compile_steps identifier color steps unique
  refine ⟨.ready state,cursor identifier color atLeaf,
    (record,fields identifier color (parentId identifier atLeaf.ancestors) (.leaf key record)),
    actualReads,actualCost,(fun entry leaf => .ready (next entry.1 leaf)),compiled,?_,?_⟩
  · simp only [cursor,focus,annotate]
  · simp only [program,instruction]

end TangoSquared.Paper20261030.Structural.Compiler
