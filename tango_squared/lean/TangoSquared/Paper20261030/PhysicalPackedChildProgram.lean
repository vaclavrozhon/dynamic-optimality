import TangoSquared.Paper20261030.LocalPackedChildProgram
import TangoSquared.Paper20261030.PhysicalForestCompiler

/-! The existing read-driven child controller in the physically annotated
forest. The compiler maintains the physical pointer fields, so the output
can immediately be used for another descent or a parent observation.
-/

namespace TangoSquared.Paper20261030.PhysicalPackedChildController

open ColoredStorage SourcePointer ForestLocalProgram Structural PhysicalForestMetadata

variable {α ρ ι η C : Type*} [DecidableEq ι] [DecidableEq η] [LinearOrder C] [Fintype C]

abbrev State (ρ ι η C : Type*) := PhysicalForestCompiler.State (PackedChildController.State ρ η C) C (ρ × Fields η C) ι

def program (identifier : ρ → η) (wanted : η) (right : Bool) : Program (State ρ ι η C) C (Record (ρ × Fields η C) ι) :=
  PhysicalForestCompiler.program (PackedChildController.program identifier wanted right)

def initial : State ρ ι η C := .ready PackedChildController.initial

theorem descend [DecidableEq α] (identifier : ρ → η) (color : α → C) (right : Bool)
    (l r : Source α (ρ × Fields η C)) (record : ρ × Fields η C) (outside)
    (children : record.2.children = some
      (Child.mk (identifier l.rootRecord.1) (l.support color),Child.mk (identifier r.rootRecord.1) (r.support color)))
    (forest : TaggedForest C α (ρ × Fields η C) ι)
    (represented : ProjectionForest.Represents color ⟨.fork record l r,outside⟩ (erase forest))
    (physicalUnique : Unique forest)
    (logicalUnique : Distinguishes (fun entry => identifier entry.1) (Cursor.tree ⟨.fork record l r,outside⟩)) :
    ∃ target reads cost,
      Run (program identifier (identifier record.1) right) initial (encode forest)
        (.ready (.done (if right then identifier r.rootRecord.1 else identifier l.rootRecord.1))) (encode target) reads cost ∧
      ProjectionForest.Represents color (PackedDescentController.child right l r record outside) (erase target) ∧
      Unique target ∧ cost ≤ 76*Fintype.card C := by
  obtain ⟨bare,readWord,sourceCost,sourceRun,bareRep,bounded⟩ :=
    PackedChildController.descend identifier color right l r record outside children (erase forest) represented logicalUnique
  obtain ⟨target,reads,cost,actual,targetErases,targetUnique,actualBound⟩ :=
    PhysicalForestCompiler.compile_run _ sourceRun forest rfl physicalUnique
  exact ⟨target,reads,cost,actual,by rw [targetErases]; exact bareRep,targetUnique,by omega⟩

end TangoSquared.Paper20261030.PhysicalPackedChildController
