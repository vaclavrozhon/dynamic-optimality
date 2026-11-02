import ChaCha.Paper20261030.LocalPackedRotationKernel
import ChaCha.Paper20261030.ForestCursorLift
import ChaCha.Paper20261030.PhysicalForestCompiler

/-! A projected rotation executed at a selected physical color finger.
The local context kernel acquires and restores ancestor records. The
physical compiler maintains the pointer annotations, including during
the routing rotation and list edits. Only the selected projection changes.
-/

namespace ChaCha.Paper20261030.PhysicalPackedRotation

open ColoredStorage SourcePointer ForestLocalProgram PhysicalForestMetadata

variable {α ρ ι C : Type*} [DecidableEq ι] [LinearOrder C]

abbrev KernelState (ρ ι C : Type*) :=
  PhysicalForestCompiler.State (ForestCursorLift.State (PackedContextController.State ρ)) C ρ ι

def before (right : Bool) (u v w : Source α ρ) (p top : ρ) : Source α ρ :=
  if right then .fork top (.fork p u v) w else .fork p u (.fork top v w)

def after (right : Bool) (u v w : Source α ρ) (p top : ρ) : Source α ρ := before (!right) u v w p top

def kernel (mask : ρ → Finset C) (right : Bool) (q : C) (u v w : Finset C) (p top : ρ) :
    Program (KernelState ρ ι C) C (Record ρ ι) :=
  PhysicalForestCompiler.program (ForestCursorLift.program q
    (if right then PackedRotationController.program mask q u v w p top
      else PackedRotationController.leftProgram mask q u v w p top))

def initial : KernelState ρ ι C := .ready (.running (.detaching .start))
def finalState : KernelState ρ ι C := .ready (.running .done)

theorem same_support (color : α → C) (right : Bool) (u v w : Source α ρ) (p top : ρ) :
    (before right u v w p top).support color = (after right u v w p top).support color := by
  cases right <;> simp [before,after,Source.support,Finset.union_assoc]

theorem run [DecidableEq α] (mask : ρ → Finset C) (color : α → C) (right : Bool) (q : C)
    (u v w : Source α ρ) (p top : ρ) (outside : List (Frame α ρ))
    (correct : ColorsCorrect mask color (plug (before right u v w p top) outside))
    (present : q ∈ (before right u v w p top).support color)
    (forest : TaggedForest C α ρ ι) (unique : Unique forest)
    (represented : ProjectionForest.RepresentsAt color q ⟨before right u v w p top,outside⟩ (erase forest q)) :
    ∃ target reads cost,
      Run (kernel mask right q (u.support color) (v.support color) (w.support color) p top)
        initial (encode forest) finalState (encode target) reads cost ∧
      ProjectionForest.RepresentsAt color q ⟨after right u v w p top,outside⟩ (erase target q) ∧
      (∀ other, other ≠ q → erase target other = erase forest other) ∧ Unique target ∧ cost ≤ 646 := by
  cases location : erase forest q with
  | none =>
    rw [location] at represented
    exact False.elim (represented (ProjectionForest.support_focus color _ outside present))
  | some physical =>
    rw [location] at represented
    have localRun : ∃ actual reads cost,
        SourceLocalProgram.Run
          (if right then PackedRotationController.program mask q (u.support color) (v.support color) (w.support color) p top
            else PackedRotationController.leftProgram mask q (u.support color) (v.support color) (w.support color) p top)
          (.detaching .start) physical .done actual reads cost ∧
        ColoredStorage.Represents color q ⟨after right u v w p top,outside⟩ actual ∧ cost ≤ 17 := by
      cases right with
      | false => exact PackedRotationController.rotate_left mask color q u v w p top outside correct present physical represented
      | true => exact PackedRotationController.rotate_right mask color q u v w p top outside correct present physical represented
    obtain ⟨actual,localReads,localCost,body,actualRep,localBound⟩ := localRun
    have inForest := ForestCursorLift.run q body (erase forest) location
    obtain ⟨target,reads,cost,compiled,targetErases,targetUnique,bounded⟩ :=
      PhysicalForestCompiler.compile_run _ inForest forest rfl unique
    refine ⟨target,reads,cost,compiled,?_,?_,targetUnique,by omega⟩
    · rw [targetErases,Function.update_self]
      exact actualRep
    · intro other different
      rw [targetErases,Function.update_of_ne different]

end ChaCha.Paper20261030.PhysicalPackedRotation
