import TangoSquared.Paper20261030.CanonicalBoundaryRoute
import TangoSquared.Paper20261030.EnclosedProperDescent
import TangoSquared.Paper20261030.PathRecordRead

set_option autoImplicit false

/-! Copy the active-root finger, follow the observed boundary route, and
read the reached root. This costs at most six charged operations, including
the copy and read, and preserves the tree and all other finger positions. -/

namespace TangoSquared.Paper20261030.ReachedBoundaryRoute

open ColoredStorage SourcePointer SourcePositions Structural PhysicalForestMetadata PhysicalPacketStaging
open LocalComponentCompiler CanonicalHeadWingViews MultiSourceProgram

variable {α β ρ ι τ F : Type*} [DecidableEq α] [DecidableEq F]

local instance reachedBoundaryRouteColorOrder : LinearOrder (Option Bool) :=
  inferInstanceAs (LinearOrder (WithBot Bool))

set_option backward.isDefEq.respectTransparency false in
theorem execute (origin work : F) (readPacket : τ → Packet α ρ ι)
    (dummyId : ι) (color : α → Option Bool) (source : Source α ρ)
    (forest : TaggedForest (Option Bool) α ρ ι)
    (represented : ProjectionForest.Represents color ⟨source,[]⟩ (erase forest))
    (headerKey : α) (payload : Option Bool → α → Source β (Packet α ρ ι))
    (config : Configuration (Option Bool) β (Packet α ρ ι))
    (assembled : ForestConnector.assemble (ComponentPhysicalRepair.view none wingOrientation headerKey payload (encode forest))
      (ForestConnector.ThreeColors.layout (ComponentPhysicalRepair.view none wingOrientation headerKey payload (encode forest))) = some config)
    (side : Bool) (headPart tail : ProjectionLocal.Projected α ρ) (key : α)
    (low high : List ρ) (terminal : ρ)
    (selected : packed color (some side) source = activePacked headPart tail key true low high terminal)
    (oppositePresent headPresent tailPresent : Bool)
    (oppositeBit : oppositePresent = (packed color (some (!side)) source).isSome)
    (headBit : headPresent = headPart.isSome) (tailBit : tailPresent = tail.isSome)
    (saved : Packet α ρ ι) (current : Cursor β τ)
    (view : current.focus.mapRecords readPacket = config.tree.setRoot (saved ++ config.tree.rootRecord))
    (global : Configuration F β τ) (positioned : MultiSourceSingleCursor.Represents origin current global) :
    ∃ target reached packet,
      Run (PathRecordRead.program origin work id (HeadBoundaryRoute.path side oppositePresent headPresent tailPresent))
        none global (some (some (.done reached.focus.rootRecord))) target [(work,reached.focus.rootRecord)]
        ((HeadBoundaryRoute.path side oppositePresent headPresent tailPresent).length+2) ∧
      target.tree = global.tree ∧ MultiSourceSingleCursor.Represents work reached target ∧
      descend current (HeadBoundaryRoute.path side oppositePresent headPresent tailPresent) = some reached ∧
      reached.focus.mapRecords readPacket = (payload (some side) key).setRoot
        (some packet :: none :: (payload (some side) key).rootRecord) ∧
      (∀ finger, finger ≠ work → target.fingers finger = global.fingers finger) ∧
      (HeadBoundaryRoute.path side oppositePresent headPresent tailPresent).length+2 ≤ 6 := by
  obtain ⟨ghost,packet,located,focus⟩ := CanonicalBoundaryRoute.locate dummyId color source forest represented headerKey payload config assembled
    side headPart tail key low high terminal selected
  rw [← oppositeBit,← headBit,← tailBit] at located
  obtain ⟨reached,descended,erases⟩ := reached_proper readPacket config.tree (saved ++ config.tree.rootRecord)
    (HeadBoundaryRoute.path side oppositePresent headPresent tailPresent)
    (HeadBoundaryRoute.path_nonempty side oppositePresent headPresent tailPresent) ghost located current view
  obtain ⟨target,actual,tree,atRoot,others⟩ := PathRecordRead.execute origin work id _ global current reached positioned descended
  exact ⟨target,reached,packet,actual,tree,atRoot,descended,erases.trans focus,others,
    by have short := HeadBoundaryRoute.path_length side oppositePresent headPresent tailPresent; omega⟩

end TangoSquared.Paper20261030.ReachedBoundaryRoute
