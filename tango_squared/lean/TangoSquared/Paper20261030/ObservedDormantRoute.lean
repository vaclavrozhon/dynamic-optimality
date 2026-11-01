import TangoSquared.Paper20261030.ReachedBoundaryRoute
import TangoSquared.Paper20261030.ObservedHeadParameters
import TangoSquared.Paper20261030.HeadRealOutputShapes

set_option autoImplicit false

/-! The route to the new dormant root is computed only from the retained
boundary records. Its side comes from the exchanged direction, its first
two edges from the new root mask, and its remaining edges from two old
child masks. The execution theorem derives every presence-bit premise. -/

namespace TangoSquared.Paper20261030.ObservedDormantRoute

open ColoredStorage SourcePointer Structural HeadBoundary PhysicalForestMetadata PhysicalPacketStaging
open LocalComponentCompiler MultiSourceProgram

variable {α β ρ η τ F : Type*} [DecidableEq α] [DecidableEq F]

local instance observedDormantRouteColorOrder : LinearOrder (Option Bool) :=
  inferInstanceAs (LinearOrder (WithBot Bool))

def oppositePresent (data : ObservedHeadParameters.Data α ρ η) : Bool :=
  decide (some data.direction ∈ data.fresh.low.2.colors)

def headPresent (data : ObservedHeadParameters.Data α ρ η) : Bool :=
  ObservedHeadBlueprint.childPresent (some (!data.direction)) false data.old.low

def tailPresent (data : ObservedHeadParameters.Data α ρ η) : Bool :=
  ObservedHeadBlueprint.childPresent (some (!data.direction)) true data.old.incomingHigh

def path (data : ObservedHeadParameters.Data α ρ η) : List Bool :=
  HeadBoundaryRoute.path (!data.direction) (oppositePresent data) (headPresent data) (tailPresent data)

theorem path_length (data : ObservedHeadParameters.Data α ρ η) : (path data).length ≤ 4 :=
  HeadBoundaryRoute.path_length _ _ _ _

set_option backward.isDefEq.respectTransparency false in
theorem execute (origin work : F) (readPacket : τ → Packet α (HeadBoundary.Record ρ η (Option Bool)) Nat)
    (markerId : Nat) (identifier : ρ → η) (oldColor incomingColor newColor : α → Option Bool)
    (low oldHigh incomingHigh oldTerminal incomingTerminal : ρ) (depth : α)
    (headPart oldTail incomingTail : Source α ρ) (data : ObservedHeadParameters.Data α ρ η)
    (observed : data.old = HeadBoundary.observed identifier oldColor incomingColor low oldHigh incomingHigh oldTerminal incomingTerminal
      depth headPart oldTail incomingTail)
    (view : activeTree data.fresh depth
      (annotate identifier oldColor (some (identifier low)) headPart)
      (annotate identifier incomingColor (some (identifier incomingHigh)) incomingTail) =
      annotate identifier newColor none (.fork low headPart (.fork incomingHigh (.leaf depth incomingTerminal) incomingTail)))
    (boundary : newColor depth = some (!data.direction))
    (headColors : ∀ key ∈ headPart.shape.leaves, oldColor key = newColor key)
    (tailColors : ∀ key ∈ incomingTail.shape.leaves, incomingColor key = newColor key)
    (forest : TaggedForest (Option Bool) α (HeadBoundary.Record ρ η (Option Bool)) Nat)
    (represented : ProjectionForest.Represents newColor
      ⟨annotate identifier newColor none (.fork low headPart (.fork incomingHigh (.leaf depth incomingTerminal) incomingTail)),[]⟩ (erase forest))
    (headerKey : α) (payload : Option Bool → α → Source β (Packet α (HeadBoundary.Record ρ η (Option Bool)) Nat))
    (config : Configuration (Option Bool) β (Packet α (HeadBoundary.Record ρ η (Option Bool)) Nat))
    (assembled : ForestConnector.assemble (ComponentPhysicalRepair.view none wingOrientation headerKey payload (encode forest))
      (ForestConnector.ThreeColors.layout (ComponentPhysicalRepair.view none wingOrientation headerKey payload (encode forest))) = some config)
    (saved : Packet α (HeadBoundary.Record ρ η (Option Bool)) Nat) (current : Cursor β τ)
    (erases : current.focus.mapRecords readPacket = config.tree.setRoot (saved ++ config.tree.rootRecord))
    (global : Configuration F β τ) (positioned : MultiSourceSingleCursor.Represents origin current global) :
    ∃ target reached packet,
      Run (PathRecordRead.program origin work id (path data)) none global
        (some (some (.done reached.focus.rootRecord))) target [(work,reached.focus.rootRecord)] ((path data).length+2) ∧
      target.tree = global.tree ∧ MultiSourceSingleCursor.Represents work reached target ∧
      SourcePositions.descend current (path data) = some reached ∧
      reached.focus.mapRecords readPacket = (payload (some (!data.direction)) depth).setRoot
        (some packet :: none :: (payload (some (!data.direction)) depth).rootRecord) ∧
      (∀ finger, finger ≠ work → target.fingers finger = global.fingers finger) ∧ (path data).length+2 ≤ 6 := by
  have selected := HeadRealOutputShapes.active identifier oldColor incomingColor newColor low incomingHigh incomingTerminal
    depth (!data.direction) (!data.direction) headPart incomingTail data.fresh view boundary headColors tailColors
  simp only [decide_true] at selected
  have rootEq := congrArg Source.rootRecord view
  simp only [activeTree,annotate,Source.rootRecord] at rootEq
  have oppositeBit : oppositePresent data =
      (packed newColor (some (!(!data.direction)))
        (annotate identifier newColor none (.fork low headPart (.fork incomingHigh (.leaf depth incomingTerminal) incomingTail)))).isSome := by
    simp only [oppositePresent,rootEq,Bool.not_not,PackedRotationController.packed_isSome,ObservedHeadBlueprint.annotate_support,fields]
  have headBit : headPresent data =
      (packed oldColor (some (!data.direction)) (annotate identifier oldColor (some (identifier low)) headPart)).isSome := by
    simp only [headPresent,observed,HeadBoundary.observed,ObservedHeadBlueprint.childPresent,fields,descriptor,
      Bool.false_eq_true,if_false,PackedRotationController.packed_isSome,ObservedHeadBlueprint.annotate_support]
  have tailBit : tailPresent data =
      (packed incomingColor (some (!data.direction)) (annotate identifier incomingColor (some (identifier incomingHigh)) incomingTail)).isSome := by
    simp only [tailPresent,observed,HeadBoundary.observed,ObservedHeadBlueprint.childPresent,fields,descriptor,
      if_true,PackedRotationController.packed_isSome,ObservedHeadBlueprint.annotate_support]
  exact ReachedBoundaryRoute.execute origin work readPacket markerId newColor _ forest represented headerKey payload config assembled
    (!data.direction) _ _ depth _ _ data.fresh.incomingTerminal selected
    (oppositePresent data) (headPresent data) (tailPresent data) oppositeBit headBit tailBit saved current erases global positioned

end TangoSquared.Paper20261030.ObservedDormantRoute
