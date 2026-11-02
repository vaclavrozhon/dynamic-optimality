import ChaCha.Paper20261030.CanonicalRoutingDecomposition
import ChaCha.Paper20261030.ThreeColorConnectors

/-!
# From the maintained forest to the assembled canonical component

This supplies both links needed by finite head views: the real pieces
are canonically annotated tagged projections, and their primary connector
has exactly the left/header/right shape with absent wings suppressed.
The outer dummy ids are used only in the erasure-based input proof.
-/

namespace ChaCha.Paper20261030.CanonicalComponentAssembly

open ColoredStorage SourcePointer Structural PhysicalForestMetadata PhysicalPacketStaging
open PacketLayers.Representation CanonicalRoutingDecomposition

variable {α β ρ ι C : Type*} [DecidableEq α] [LinearOrder C]

theorem packed_focus (color : α → C) (source : Source α ρ) (forest : TaggedForest C α ρ ι)
    (represented : ProjectionForest.Represents color ⟨source,[]⟩ (erase forest)) (q : C) :
    ((forest q).map Cursor.focus).map (Source.mapRecords Prod.snd) = packed color q source := by
  have equal := congrArg (Option.map Cursor.focus) (RootPackedForest.erases color source forest represented q)
  simpa only [erase,Option.map_map,Function.comp_def,Cursor.mapRecords,Option.map_id'] using equal

theorem real_piece (dummyId : ι) (color : α → C) (source : Source α ρ)
    (forest : TaggedForest C α ρ ι)
    (represented : ProjectionForest.Represents color ⟨source,[]⟩ (erase forest))
    (virtualColor q : C) (different : q ≠ virtualColor) (orientation : C → Bool) (headerKey : α)
    (payload : C → α → Source β (Packet α ρ ι)) :
    (ComponentPhysicalRepair.view virtualColor orientation headerKey payload (encode forest) q).map
      (fun current => current.tree.mapRecords (fun packet => (dummyId,packet))) =
        render dummyId (payload q) (orientation q) none ((forest q).map Cursor.focus) := by
  cases found : forest q with
  | none =>
    simp only [ComponentPhysicalRepair.view,PayloadForestController.transform,VirtualHeaderController.encode,
      different,if_false,ForestMirrorController.transform,encode,found,Option.map_none,render]
  | some current =>
    have rep := represented q
    simp only [erase,found,Option.map_some,ProjectionForest.RepresentsAt] at rep
    have root := ColoredStorage.Represents.root_ancestors color q _ _ rep
    have rooted : current.ancestors = [] := by simpa only [Cursor.mapRecords,List.map_eq_nil_iff] using root
    rcases current with ⟨tagged,ancestors⟩
    dsimp only at rooted
    subst ancestors
    rw [CanonicalPacketLayerViews.component_real virtualColor q different orientation headerKey payload forest tagged found]
    rfl

omit [DecidableEq α] in
theorem virtual_piece (dummyId : ι) (virtualColor : C) (orientation : C → Bool) (headerKey : α)
    (payload : C → α → Source β (Packet α ρ ι)) (forest : TaggedForest C α ρ ι) :
    (ComponentPhysicalRepair.view virtualColor orientation headerKey payload (encode forest) virtualColor).map
      (fun current => current.tree.mapRecords (fun packet => (dummyId,packet))) =
        some (MixedHeadInputView.rawBlock
          [some (.header (ForestMirrorController.transform orientation (encode forest) virtualColor)),none]
          ((payload virtualColor headerKey).mapRecords (fun packet => (dummyId,packet)))) := by
  rw [CanonicalPacketLayerViews.component_virtual virtualColor orientation headerKey payload forest]
  simp only [Option.map_some,Cursor.tree,plug,Source.mapRecords_setRoot,MixedHeadInputView.rawBlock,
    Source.mapRecords_root,List.cons_append,List.nil_append]

omit [DecidableEq α] in
theorem assembled (dummyId : ι)
    (forest : ProjectionForest.State (Option Bool) β (Option (PhysicalPacketStaging.Datum α ρ ι)))
    (header : Cursor β (Packet α ρ ι)) (present : forest none = some header)
    (config : MultiSourceProgram.Configuration (Option Bool) β (Packet α ρ ι))
    (assembly : ForestConnector.assemble forest (ForestConnector.ThreeColors.layout forest) = some config) :
    some (config.tree.mapRecords (fun packet => (dummyId,packet))) =
      physicalPrimaryJoin dummyId
        (physicalPrimaryJoin dummyId
          ((forest (some true)).map (fun current => current.tree.mapRecords (fun packet => (dummyId,packet))))
          ((forest none).map (fun current => current.tree.mapRecords (fun packet => (dummyId,packet)))))
        ((forest (some false)).map (fun current => current.tree.mapRecords (fun packet => (dummyId,packet)))) := by
  cases left : forest (some true) <;> cases right : forest (some false) <;>
    simp only [ForestConnector.ThreeColors.layout,left,right,Option.isSome_none,Option.isSome_some,
      Bool.false_eq_true,if_false,if_true,ForestConnector.assemble,present,Option.map_some,
      Option.bind_some,Option.some.injEq] at assembly <;>
    rw [← assembly,present] <;> rfl

end ChaCha.Paper20261030.CanonicalComponentAssembly
