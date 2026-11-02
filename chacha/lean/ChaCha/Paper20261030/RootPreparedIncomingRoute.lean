import ChaCha.Paper20261030.PreparedIncomingRoute

set_option autoImplicit false

/-! The observed incoming route at the minimum depth has no prefix part.
Its side, opposite wing, and tail bits still come only from the two
boundary records acquired by the sentinel preparation. -/

namespace ChaCha.Paper20261030.PreparedIncomingRoute

open ColoredStorage SourcePointer Structural HeadBoundary PhysicalForestMetadata PhysicalPacketStaging
open LocalComponentCompiler MultiSourceProgram

variable {α β ρ ι η τ F : Type*} [DecidableEq α] [DecidableEq F]

local instance : LinearOrder (Option Bool) := inferInstanceAs (LinearOrder (WithBot Bool))

set_option backward.isDefEq.respectTransparency false in
theorem sentinel (origin work : F) (readPacket : τ → Packet α (HeadBoundary.Record ρ η (Option Bool)) ι)
    (markerId : ι) (identifier : ρ → η) (color : α → Option Bool)
    (high terminal : ρ) (depth : α) (tail : Source α ρ) (side : Bool)
    (boundary : color depth = some side)
    (forest : TaggedForest (Option Bool) α (HeadBoundary.Record ρ η (Option Bool)) ι)
    (represented : ProjectionForest.Represents color
      ⟨annotate identifier color none (.fork high (.leaf depth terminal) tail),[]⟩ (erase forest))
    (headerKey : α) (payload : Option Bool → α → Source β (Packet α (HeadBoundary.Record ρ η (Option Bool)) ι))
    (config : Configuration (Option Bool) β (Packet α (HeadBoundary.Record ρ η (Option Bool)) ι))
    (assembled : ForestConnector.assemble (ComponentPhysicalRepair.view none wingOrientation headerKey payload (encode forest))
      (ForestConnector.ThreeColors.layout (ComponentPhysicalRepair.view none wingOrientation headerKey payload (encode forest))) = some config)
    (saved : Packet α (HeadBoundary.Record ρ η (Option Bool)) ι) (current : Cursor β τ)
    (view : current.focus.mapRecords readPacket = config.tree.setRoot (saved ++ config.tree.rootRecord))
    (global : Configuration F β τ) (positioned : MultiSourceSingleCursor.Represents origin current global) :
    ∃ target reached packet path,
      Run (program (τ := τ) origin work (BoundaryReadController.sentinelResult identifier color high terminal depth tail))
        none global (some (some (.done reached.focus.rootRecord))) target [(work,reached.focus.rootRecord)] (path.length+2) ∧
      target.tree = global.tree ∧ MultiSourceSingleCursor.Represents work reached target ∧
      SourcePositions.descend current path = some reached ∧ path ≠ [] ∧
      reached.focus.mapRecords readPacket = (payload (some side) depth).setRoot
        (some packet :: none :: (payload (some side) depth).rootRecord) ∧
      (∀ finger, finger ≠ work → target.fingers finger = global.fingers finger) ∧ path.length+2 ≤ 6 := by
  let whole := annotate identifier color none (.fork high (.leaf depth terminal) tail)
  let rest := packed color (some side) (annotate identifier color (some (identifier high)) tail)
  let bits : Bits := ⟨side,(packed color (some (!side)) whole).isSome,false,rest.isSome⟩
  have computed : compute (BoundaryReadController.sentinelResult identifier color high terminal depth tail) = some bits := by
    cases side <;> simp [compute,BoundaryReadController.sentinelResult,ObservedHeadParameters.direction,fields,Source.support,boundary,
      bits,rest,whole,ObservedHeadBlueprint.childPresent,descriptor,PackedRotationController.packed_isSome,ObservedHeadBlueprint.annotate_support]
  have selected := CanonicalRootComponentView.packing identifier color side side high terminal depth tail boundary
  simp only [decide_true] at selected
  obtain ⟨target,reached,packet,actual,tree,located,descended,payloadAt,others,bound⟩ :=
    ReachedBoundaryRoute.execute origin work readPacket markerId color whole forest represented headerKey payload config assembled
      side none rest depth _ _ _ selected bits.opposite bits.head bits.tail rfl rfl rfl saved current view global positioned
  refine ⟨target,reached,packet,bits.path,?_,tree,located,descended,HeadBoundaryRoute.path_nonempty _ _ _ _,payloadAt,others,bound⟩
  simpa only [program,computed,Bits.path] using actual


end ChaCha.Paper20261030.PreparedIncomingRoute
