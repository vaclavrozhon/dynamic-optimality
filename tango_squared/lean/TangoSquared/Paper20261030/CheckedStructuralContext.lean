import TangoSquared.Paper20261030.CheckedStructuralParent
import TangoSquared.Paper20261030.CheckedStructuralRotation
import TangoSquared.Paper20261030.CheckedStructuralWrite

/-! Checked context lifting: both the rooted structural kernel and the
external-parent repair supply readiness at every primitive instruction.
-/

namespace TangoSquared.Paper20261030.Structural.ContextController

open ColoredStorage SourcePointer SourceLocalProgram PackedReadiness

variable {α ρ ι C σ : Type*} [DecidableEq ι] [LinearOrder C] [Fintype C]

theorem checked_lift (identifier : ρ → ι) (color : α → C)
    (kernel : Program σ (ρ × Fields ι C)) (initial last : σ)
    (before after : Source α ρ) (outside : List (Frame α ρ))
    (sameColors : before.support color = after.support color)
    (unique : ((plug before outside).inventory identifier).Nodup)
    {kernelReads kernelCost}
    (execution : CheckedRun identifier color kernel initial
      ⟨annotate identifier color (parentId identifier outside) before,frames identifier color before outside⟩ last
      ⟨annotate identifier color (parentId identifier outside) after,frames identifier color before outside⟩
      kernelReads kernelCost)
    (halted : kernel last = .halt) :
    ∃ reads cost, CheckedRun identifier color (program identifier kernel initial) .start (cursor identifier color ⟨before,outside⟩)
      .done (cursor identifier color ⟨after,outside⟩) reads cost ∧ cost ≤ kernelCost+6 := by
  let code := program identifier kernel initial
  let old := identifier before.rootRecord
  let fresh := descriptor identifier color after
  let middle : Cursor α (ρ × Fields ι C) :=
    ⟨annotate identifier color (parentId identifier outside) after,frames identifier color before outside⟩
  have first : SourceLocalProgram.Step code .start (cursor identifier color ⟨before,outside⟩)
      (.running old initial) (cursor identifier color ⟨before,outside⟩)
      (some (annotate identifier color (parentId identifier outside) before).rootRecord) := by
    have actual := SourceLocalProgram.Step.read (program := code) (state := .start)
      (cursor := cursor identifier color ⟨before,outside⟩)
      (next := fun record _ => .running (identifier record.1) initial) rfl
    simpa only [cursor,annotate_root,old] using actual
  have body := execution.map_prefix (State.running old) (running_code identifier kernel initial old)
  have observed : SourceLocalProgram.Step code (.running old last) middle
      (finishParent old fresh (ParentController.initial (parentId identifier outside))) middle
      (some middle.focus.rootRecord) := by
    have actual := SourceLocalProgram.Step.read (program := code) (state := .running old last)
      (cursor := middle) (next := fun record _ => parentInitial identifier old record)
      (by simp only [code,program,halted])
    have entry : parentInitial (σ := σ) identifier old middle.focus.rootRecord =
        finishParent old fresh (ParentController.initial (parentId identifier outside)) := by
      simp only [middle,annotate_root,parentInitial,fields,fresh,descriptor]
    simpa only [entry] using actual
  obtain ⟨parentReads,parentCost,parentRun,parentBound⟩ :=
    ParentController.checked_repair identifier color before after sameColors outside unique
  have ending := parentRun.map_prefix (finishParent old fresh)
    (parent_code identifier kernel initial old fresh)
  have joined := (step_prefix first (cursor_read_ready identifier color ⟨before,outside⟩ _)).append (body.append ((step_prefix observed (by
    simp only [code,program,halted]
    exact annotate_read_ready identifier color _ _ _ _)).append ending))
  exact ⟨_,_,joined.run rfl,by omega⟩

theorem checked_rotate_right (identifier : ρ → ι) (color : α → C)
    (u v w : Source α ρ) (p q : ρ) (outside : List (Frame α ρ))
    (unique : ((plug (.fork q (.fork p u v) w) outside).inventory identifier).Nodup) :
    ∃ reads cost, CheckedRun identifier color (program identifier (RotationController.program identifier true) .start) .start
      (cursor identifier color ⟨.fork q (.fork p u v) w,outside⟩) .done
      (cursor identifier color ⟨.fork p u (.fork q v w),outside⟩) reads cost ∧ cost ≤ 19 := by
  obtain ⟨reads,body⟩ := RotationController.checked_rotate_right identifier color (parentId identifier outside)
    u v w p q (frames identifier color (.fork q (.fork p u v) w) outside)
    (cursor_colors_correct identifier color ⟨.fork q (.fork p u v) w,outside⟩)
  exact checked_lift identifier color (RotationController.program identifier true) .start .done
    (.fork q (.fork p u v) w) (.fork p u (.fork q v w)) outside
    (by simp only [Source.support,Finset.union_assoc]) unique body rfl

theorem checked_rotate_left (identifier : ρ → ι) (color : α → C)
    (u v w : Source α ρ) (p q : ρ) (outside : List (Frame α ρ))
    (unique : ((plug (.fork p u (.fork q v w)) outside).inventory identifier).Nodup) :
    ∃ reads cost, CheckedRun identifier color (program identifier (RotationController.program identifier false) .start) .start
      (cursor identifier color ⟨.fork p u (.fork q v w),outside⟩) .done
      (cursor identifier color ⟨.fork q (.fork p u v) w,outside⟩) reads cost ∧ cost ≤ 19 := by
  obtain ⟨reads,body⟩ := RotationController.checked_rotate_left identifier color (parentId identifier outside)
    u v w p q (frames identifier color (.fork p u (.fork q v w)) outside)
    (cursor_colors_correct identifier color ⟨.fork p u (.fork q v w),outside⟩)
  exact checked_lift identifier color (RotationController.program identifier false) .start .done
    (.fork p u (.fork q v w)) (.fork q (.fork p u v) w) outside
    (by simp only [Source.support,Finset.union_assoc]) unique body rfl

end TangoSquared.Paper20261030.Structural.ContextController
