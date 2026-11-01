import TangoSquared.Paper20261030.LocalStructuralRotation
import TangoSquared.Paper20261030.LocalStructuralParent

/-! A local wrapper for a structural root operation at arbitrary depth.
The wrapper reads the old identifier, runs its kernel, reads the new root
descriptor, and repairs the external parent. All navigation parameters
come from these charged reads. The wrapper adds at most six operations.
-/

namespace TangoSquared.Paper20261030.Structural.ContextController

open ColoredStorage SourcePointer SourceLocalProgram

variable {α ρ ι C σ : Type*} [DecidableEq C] [DecidableEq ι]

inductive State (σ ρ ι C : Type*) where
  | start
  | running (old : ι) (state : σ)
  | parent (old : ι) (fresh : Child ι C) (state : ParentController.State ρ ι C)
  | done

def finishParent (old : ι) (fresh : Child ι C) : ParentController.State ρ ι C → State σ ρ ι C
  | .done => .done
  | state => .parent old fresh state

def parentInitial (identifier : ρ → ι) (old : ι) (record : ρ × Fields ι C) : State σ ρ ι C :=
  finishParent old ⟨identifier record.1,record.2.colors⟩ (ParentController.initial record.2.parent)

def program (identifier : ρ → ι) (kernel : Program σ (ρ × Fields ι C)) (initial : σ) :
    Program (State σ ρ ι C) (ρ × Fields ι C)
  | .start => .read (fun record _ => .running (identifier record.1) initial)
  | .running old state => match kernel state with
      | .halt => .read (fun record _ => parentInitial identifier old record)
      | instruction => instruction.mapState (.running old)
  | .parent old fresh state => (ParentController.program old fresh state).mapState (finishParent old fresh)
  | .done => .halt

omit [DecidableEq C] in
theorem running_code (identifier : ρ → ι) (kernel : Program σ (ρ × Fields ι C))
    (initial : σ) (old : ι) (state : σ) (active : kernel state ≠ .halt) :
    program identifier kernel initial (.running old state) = (kernel state).mapState (.running old) := by
  simp only [program]

omit [DecidableEq C] in
theorem parent_code (identifier : ρ → ι) (kernel : Program σ (ρ × Fields ι C))
    (initial : σ) (old : ι) (fresh : Child ι C) (state : ParentController.State ρ ι C)
    (active : ParentController.program old fresh state ≠ .halt) :
    program identifier kernel initial (finishParent old fresh state) =
      (ParentController.program old fresh state).mapState (finishParent old fresh) := by
  cases state with
  | done => exact False.elim (active rfl)
  | goUp | readParent | writeParent | goDown | error => rfl

theorem lift (identifier : ρ → ι) (color : α → C)
    (kernel : Program σ (ρ × Fields ι C)) (initial last : σ)
    (before after : Source α ρ) (outside : List (Frame α ρ))
    (sameColors : before.support color = after.support color)
    (unique : ((plug before outside).inventory identifier).Nodup)
    {kernelReads kernelCost}
    (execution : Run kernel initial
      ⟨annotate identifier color (parentId identifier outside) before,frames identifier color before outside⟩ last
      ⟨annotate identifier color (parentId identifier outside) after,frames identifier color before outside⟩
      kernelReads kernelCost)
    (halted : kernel last = .halt) :
    ∃ reads cost, Run (program identifier kernel initial) .start (cursor identifier color ⟨before,outside⟩)
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
    ParentController.repair identifier color before after sameColors outside unique
  have ending := parentRun.map_prefix (finishParent old fresh)
    (parent_code identifier kernel initial old fresh)
  have joined := first.prefix.append (body.append (observed.prefix.append ending))
  exact ⟨_,_,joined.run rfl,by omega⟩

theorem rotate_right (identifier : ρ → ι) (color : α → C)
    (u v w : Source α ρ) (p q : ρ) (outside : List (Frame α ρ))
    (unique : ((plug (.fork q (.fork p u v) w) outside).inventory identifier).Nodup) :
    ∃ reads cost, Run (program identifier (RotationController.program identifier true) .start) .start
      (cursor identifier color ⟨.fork q (.fork p u v) w,outside⟩) .done
      (cursor identifier color ⟨.fork p u (.fork q v w),outside⟩) reads cost ∧ cost ≤ 19 := by
  obtain ⟨reads,body⟩ := RotationController.rotate_right identifier color (parentId identifier outside)
    u v w p q (frames identifier color (.fork q (.fork p u v) w) outside)
  exact lift identifier color (RotationController.program identifier true) .start .done
    (.fork q (.fork p u v) w) (.fork p u (.fork q v w)) outside
    (by simp only [Source.support,Finset.union_assoc]) unique body rfl

theorem rotate_left (identifier : ρ → ι) (color : α → C)
    (u v w : Source α ρ) (p q : ρ) (outside : List (Frame α ρ))
    (unique : ((plug (.fork p u (.fork q v w)) outside).inventory identifier).Nodup) :
    ∃ reads cost, Run (program identifier (RotationController.program identifier false) .start) .start
      (cursor identifier color ⟨.fork p u (.fork q v w),outside⟩) .done
      (cursor identifier color ⟨.fork q (.fork p u v) w,outside⟩) reads cost ∧ cost ≤ 19 := by
  obtain ⟨reads,body⟩ := RotationController.rotate_left identifier color (parentId identifier outside)
    u v w p q (frames identifier color (.fork p u (.fork q v w)) outside)
  exact lift identifier color (RotationController.program identifier false) .start .done
    (.fork p u (.fork q v w)) (.fork q (.fork p u v) w) outside
    (by simp only [Source.support,Finset.union_assoc]) unique body rfl

end TangoSquared.Paper20261030.Structural.ContextController
