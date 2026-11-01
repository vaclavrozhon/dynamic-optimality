import TangoSquared.Paper20261030.CheckedStructuralWriteContext

/-! Compiling one source instruction into an execution whose metadata
is ready at every primitive step. Writes must preserve the separate
vertex identifier; the immutable-identifier compiler supplies this fact.
-/

namespace TangoSquared.Paper20261030.Structural.Compiler

open ColoredStorage SourcePointer SourceLocalProgram PackedReadiness

variable {α ρ ι C σ : Type*} [DecidableEq ι] [LinearOrder C] [Fintype C]

theorem checked_rotation_step (identifier : ρ → ι) (color : α → C) (source : Program σ ρ)
    (state next : σ) (right : Bool)
    (instruction : source state = .nav (if right then .rotateRight else .rotateLeft) next)
    {before after : Cursor α ρ}
    (moved : navigate (if right then .rotateRight else .rotateLeft) before = some after)
    (unique : (before.tree.inventory identifier).Nodup) :
    ∃ reads cost, CheckedSteps identifier color (program identifier source) (.ready state) (cursor identifier color before)
      (.ready next) (cursor identifier color after) reads cost ∧ cost ≤ 19 := by
  have kernel : ∃ reads cost, CheckedRun identifier color (rotationProgram identifier right) .start (cursor identifier color before)
      .done (cursor identifier color after) reads cost ∧ cost ≤ 19 := by
    rcases before with ⟨focus,outside⟩
    cases right with
    | true => cases focus with
      | leaf => simp [navigate] at moved
      | fork q l w => cases l with
        | leaf => simp [navigate] at moved
        | fork p u v =>
          cases Option.some.inj moved
          exact ContextController.checked_rotate_right identifier color u v w p q outside unique
    | false => cases focus with
      | leaf => simp [navigate] at moved
      | fork p u r => cases r with
        | leaf => simp [navigate] at moved
        | fork q v w =>
          cases Option.some.inj moved
          exact ContextController.checked_rotate_left identifier color u v w p q outside unique
  obtain ⟨reads,cost,run,bounded⟩ := kernel
  have positive : 0 < cost := by cases run with
    | next => omega
  have steps := run.map_prefix (finishRotation right next) (rotation_code identifier source right next)
  refine ⟨reads,cost,steps.change_start positive ?_,bounded⟩
  cases right <;> simp [program,instruction,finishRotation]

theorem checked_step (identifier : ρ → ι) (color : α → C) {source : Program σ ρ}
    {state next : σ} {before after : Cursor α ρ} {entry}
    (execution : SourceLocalProgram.Step source state before next after entry)
    (stable : ∀ fresh next, source state = .write fresh next → identifier fresh = identifier before.focus.rootRecord)
    (unique : (before.tree.inventory identifier).Nodup) :
    ∃ reads cost, CheckedSteps identifier color (program identifier source) (.ready state) (cursor identifier color before)
      (.ready next) (cursor identifier color after) reads cost ∧ cost ≤ 19 := by
  cases execution with
  | read instruction =>
    rename_i nextRead
    have actual := SourceLocalProgram.Step.read (program := program (C := C) identifier source)
      (state := .ready state) (cursor := cursor identifier color before)
      (next := fun record leaf => .ready (nextRead record.1 leaf))
      (by simp only [program,instruction])
    refine ⟨[(cursor identifier color before).focus.rootRecord],1,?_,by decide⟩
    simpa only [cursor,annotate_root,isLeaf_annotate,Option.toList_some] using step_prefix actual (by
      simp only [program,instruction]
      exact cursor_read_ready identifier color before _)
  | nav instruction moved =>
    rename_i action
    cases action with
    | rotateRight => exact checked_rotation_step identifier color source state _ true instruction moved unique
    | rotateLeft => exact checked_rotation_step identifier color source state _ false instruction moved unique
    | left =>
      have actual : SourceLocalProgram.Step (program identifier source) (.ready state) (cursor identifier color before)
          (.ready next) (cursor identifier color after) none :=
        .nav (by simp only [program,instruction]) (navigate_direct identifier color .left (by intro h; cases h) (by intro h; cases h) moved)
      exact ⟨[],1,step_prefix actual (by
        simp only [program,instruction]
        exact cursor_direct_ready identifier color .left (by intro h; cases h) (by intro h; cases h) moved _),by decide⟩
    | right =>
      have actual : SourceLocalProgram.Step (program identifier source) (.ready state) (cursor identifier color before)
          (.ready next) (cursor identifier color after) none :=
        .nav (by simp only [program,instruction]) (navigate_direct identifier color .right (by intro h; cases h) (by intro h; cases h) moved)
      exact ⟨[],1,step_prefix actual (by
        simp only [program,instruction]
        exact cursor_direct_ready identifier color .right (by intro h; cases h) (by intro h; cases h) moved _),by decide⟩
    | up =>
      have actual : SourceLocalProgram.Step (program identifier source) (.ready state) (cursor identifier color before)
          (.ready next) (cursor identifier color after) none :=
        .nav (by simp only [program,instruction]) (navigate_direct identifier color .up (by intro h; cases h) (by intro h; cases h) moved)
      exact ⟨[],1,step_prefix actual (by
        simp only [program,instruction]
        exact cursor_direct_ready identifier color .up (by intro h; cases h) (by intro h; cases h) moved _),by decide⟩
  | write instruction =>
    rename_i fresh
    obtain ⟨reads,cost,run,bounded⟩ := WriteController.checked_write_cursor identifier color before.focus fresh before.ancestors (stable fresh next instruction) unique
    have positive : 0 < cost := by cases run with
        | next => omega
    have steps := run.map_prefix (finishWrite fresh next) (write_code identifier source fresh next)
    refine ⟨reads,cost,steps.change_start positive ?_,by omega⟩
    simp only [program,instruction,finishWrite]


end TangoSquared.Paper20261030.Structural.Compiler
