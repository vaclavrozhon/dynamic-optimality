import TangoSquared.Paper20261030.ReachedVirtualHeaderRead

set_option autoImplicit false

/-! Reading both stored virtual cursors with one working finger. The
two component anchors are preserved, all stored data stay unchanged, and
both acquired headers remain available in the final controller state. -/

namespace TangoSquared.Paper20261030.ReachedVirtualHeaderPair

open ColoredStorage SourcePointer Structural PhysicalForestMetadata PhysicalPacketStaging MultiSourceProgram
open ForestConnector.ThreeColors ReachedVirtualHeaderRead

variable {α β ρ ι η τ F : Type*} [DecidableEq F]

abbrev ReadState (α ρ ι : Type*) := Option (Option (PathRecordRead.State (Option (Stored α ρ ι))))

def value : ReadState α ρ ι → Option (Stored α ρ ι)
  | some (some (.done result)) => result
  | _ => none

def program (origin : Bool → F) (work : F) (readPacket : τ → Packet α ρ ι)
    (count : Bool → Nat) (header : Bool → PrimaryHeaderController.Header η) :=
  MultiSourceFinish.program (ReachedVirtualHeaderRead.program (origin false) work readPacket (count false) (header false))
    value (fun _ => none)
    (fun _ => ReachedVirtualHeaderRead.program (origin true) work readPacket (count true) (header true))

theorem execute (origin : Bool → F) (work : F) (separate : ∀ side, origin side ≠ work)
    (readPacket : τ → Packet α ρ ι) (header : Bool → PrimaryHeaderController.Header η)
    (orientation : Bool → Option Bool → Bool) (headerKey : Bool → α)
    (payload : Bool → Option Bool → α → Source β (Packet α ρ ι))
    (forest : Bool → TaggedForest (Option Bool) α ρ ι)
    (config : Bool → Configuration (Option Bool) β (Packet α ρ ι))
    (assembled : ∀ side, ForestConnector.assemble
      (ComponentPhysicalRepair.view none (orientation side) (headerKey side) (payload side) (encode (forest side)))
      (layout (ComponentPhysicalRepair.view none (orientation side) (headerKey side) (payload side) (encode (forest side)))) = some (config side))
    (leftWing : ∀ side, (header side).leftWing =
      (ComponentPhysicalRepair.view none (orientation side) (headerKey side) (payload side) (encode (forest side)) (some true)).isSome)
    (rightWing : ∀ side, (header side).rightWing =
      (ComponentPhysicalRepair.view none (orientation side) (headerKey side) (payload side) (encode (forest side)) (some false)).isSome)
    (saved : Bool → Packet α ρ ι) (current : Bool → Cursor β τ)
    (view : ∀ side, (current side).focus.mapRecords readPacket =
      (config side).tree.setRoot (saved side++(config side).tree.rootRecord))
    (global : Configuration F β τ)
    (positioned : ∀ side, MultiSourceSingleCursor.Represents (origin side) (current side) global) :
    ∃ target reads cost,
      Run (program origin work readPacket (fun side => (saved side).length) header) (.first none) global
        (.second (some (ForestMirrorController.transform (orientation false) (encode (forest false)) none))
          (some (some (.done (some (ForestMirrorController.transform (orientation true) (encode (forest true)) none))))))
        target reads cost ∧
      target.tree = global.tree ∧
      (∀ finger, finger ≠ work → target.fingers finger = global.fingers finger) ∧
      (∀ side, MultiSourceSingleCursor.Represents (origin side) (current side) target) ∧ cost ≤ 8 := by
  obtain ⟨middle,firstReads,firstCost,front,middleTree,middleFingers,firstBound⟩ :=
    ReachedVirtualHeaderRead.execute (origin false) work readPacket (header false) (orientation false) (headerKey false)
      (payload false) (forest false) (config false) (assembled false) (leftWing false) (rightWing false)
      (saved false) (current false) (view false) global (positioned false)
  have incomingLocated : MultiSourceSingleCursor.Represents (origin true) (current true) middle :=
    ⟨middleTree.trans (positioned true).1,(middleFingers _ (separate true)).trans (positioned true).2⟩
  obtain ⟨target,lastReads,lastCost,back,targetTree,targetFingers,lastBound⟩ :=
    ReachedVirtualHeaderRead.execute (origin true) work readPacket (header true) (orientation true) (headerKey true)
      (payload true) (forest true) (config true) (assembled true) (leftWing true) (rightWing true)
      (saved true) (current true) (view true) middle incomingLocated
  have actual := MultiSourceFinish.finish value (fun _ => none)
    (fun _ => ReachedVirtualHeaderRead.program (origin true) work readPacket (saved true).length (header true)) front back
  have finalTree := targetTree.trans middleTree
  have finalFingers : ∀ finger, finger ≠ work → target.fingers finger = global.fingers finger :=
    fun finger different => (targetFingers finger different).trans (middleFingers finger different)
  refine ⟨target,firstReads++lastReads,firstCost+lastCost,?_,finalTree,finalFingers,?_,by omega⟩
  · exact actual
  · intro side
    exact ⟨finalTree.trans (positioned side).1,(finalFingers _ (separate side)).trans (positioned side).2⟩

end TangoSquared.Paper20261030.ReachedVirtualHeaderPair
