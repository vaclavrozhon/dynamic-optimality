import ChaCha.Paper20261030.ReachedBoundaryRoute
import ChaCha.Paper20261030.ObservedHeadParameters
import ChaCha.Paper20261030.AnnotatedHeadWingPacking
import ChaCha.Paper20261030.CanonicalRootComponentView

set_option autoImplicit false

/-! Acquire the incoming component pointer after active preparation.
The boundary observations determine the side and every route bit. Thus
no incoming pointer is needed before preparation. The actual route costs
at most six operations and retains the active-root finger. -/

namespace ChaCha.Paper20261030.PreparedIncomingRoute

open ColoredStorage SourcePointer Structural HeadBoundary PhysicalForestMetadata PhysicalPacketStaging
open LocalComponentCompiler MultiSourceProgram

variable {α β ρ ι η τ F : Type*} [DecidableEq α] [DecidableEq F]

local instance : LinearOrder (Option Bool) := inferInstanceAs (LinearOrder (WithBot Bool))

structure Bits where
  side : Bool
  opposite : Bool
  head : Bool
  tail : Bool

def Bits.path (bits : Bits) : List Bool := HeadBoundaryRoute.path bits.side bits.opposite bits.head bits.tail

def compute : BoundaryReadController.State (HeadBoundary.Record ρ η (Option Bool)) → Option Bits
  | .done low high terminal => (ObservedHeadParameters.direction terminal).map fun side =>
      ⟨side,decide (some (!side) ∈ (low.getD high).2.colors),
        (low.map (ObservedHeadBlueprint.childPresent (some side) false)).getD false,
        ObservedHeadBlueprint.childPresent (some side) true high⟩
  | _ => none

def program (origin work : F) (values : BoundaryReadController.State (HeadBoundary.Record ρ η (Option Bool))) :=
  match compute values with
  | none => fun _ => MultiSourceProgram.Instruction.halt
  | some bits => PathRecordRead.program (ρ := τ) origin work id bits.path

set_option backward.isDefEq.respectTransparency false in
theorem active (origin work : F) (readPacket : τ → Packet α (HeadBoundary.Record ρ η (Option Bool)) ι)
    (markerId : ι) (identifier : ρ → η) (color : α → Option Bool)
    (low high terminal : ρ) (depth : α) (headPart tail : Source α ρ) (side : Bool)
    (boundary : color depth = some side)
    (forest : TaggedForest (Option Bool) α (HeadBoundary.Record ρ η (Option Bool)) ι)
    (represented : ProjectionForest.Represents color
      ⟨annotate identifier color none (.fork low headPart (.fork high (.leaf depth terminal) tail)),[]⟩ (erase forest))
    (headerKey : α) (payload : Option Bool → α → Source β (Packet α (HeadBoundary.Record ρ η (Option Bool)) ι))
    (config : Configuration (Option Bool) β (Packet α (HeadBoundary.Record ρ η (Option Bool)) ι))
    (assembled : ForestConnector.assemble (ComponentPhysicalRepair.view none wingOrientation headerKey payload (encode forest))
      (ForestConnector.ThreeColors.layout (ComponentPhysicalRepair.view none wingOrientation headerKey payload (encode forest))) = some config)
    (saved : Packet α (HeadBoundary.Record ρ η (Option Bool)) ι) (current : Cursor β τ)
    (view : current.focus.mapRecords readPacket = config.tree.setRoot (saved ++ config.tree.rootRecord))
    (global : Configuration F β τ) (positioned : MultiSourceSingleCursor.Represents origin current global) :
    ∃ target reached packet path,
      Run (program (τ := τ) origin work (BoundaryReadController.activeResult identifier color low high terminal depth headPart tail))
        none global (some (some (.done reached.focus.rootRecord))) target [(work,reached.focus.rootRecord)] (path.length+2) ∧
      target.tree = global.tree ∧ MultiSourceSingleCursor.Represents work reached target ∧
      SourcePositions.descend current path = some reached ∧ path ≠ [] ∧
      reached.focus.mapRecords readPacket = (payload (some side) depth).setRoot
        (some packet :: none :: (payload (some side) depth).rootRecord) ∧
      (∀ finger, finger ≠ work → target.fingers finger = global.fingers finger) ∧ path.length+2 ≤ 6 := by
  let whole := annotate identifier color none (.fork low headPart (.fork high (.leaf depth terminal) tail))
  let head := packed color (some side) (annotate identifier color (some (identifier low)) headPart)
  let rest := packed color (some side) (annotate identifier color (some (identifier high)) tail)
  let bits : Bits := ⟨side,(packed color (some (!side)) whole).isSome,head.isSome,rest.isSome⟩
  have computed : compute (BoundaryReadController.activeResult identifier color low high terminal depth headPart tail) = some bits := by
    cases side <;> simp [compute,BoundaryReadController.activeResult,ObservedHeadParameters.direction,fields,Source.support,boundary,
      bits,head,rest,whole,ObservedHeadBlueprint.childPresent,descriptor,PackedRotationController.packed_isSome,ObservedHeadBlueprint.annotate_support]
  have selected := AnnotatedHeadWingPacking.active identifier color side side low high terminal depth headPart tail boundary
  simp only [decide_true] at selected
  obtain ⟨target,reached,packet,actual,tree,located,descended,payloadAt,others,bound⟩ :=
    ReachedBoundaryRoute.execute origin work readPacket markerId color whole forest represented headerKey payload config assembled
      side head rest depth _ _ _ selected bits.opposite bits.head bits.tail rfl rfl rfl saved current view global positioned
  refine ⟨target,reached,packet,bits.path,?_,tree,located,descended,HeadBoundaryRoute.path_nonempty _ _ _ _,payloadAt,others,bound⟩
  simpa only [program,computed,Bits.path] using actual

end ChaCha.Paper20261030.PreparedIncomingRoute
