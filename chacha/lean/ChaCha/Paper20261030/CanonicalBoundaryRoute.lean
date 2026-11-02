import ChaCha.Paper20261030.HeadBoundaryRoute
import ChaCha.Paper20261030.CanonicalComponentAssembly
import ChaCha.Paper20261030.ComponentOriginalKeys
import ChaCha.Paper20261030.MultiSourceRecordEquivalence

set_option autoImplicit false

/-! The short boundary route is determined by the represented real
projections. Its endpoint is the boundary payload with exactly one
routing record and its delimiter attached to the root. -/

namespace ChaCha.Paper20261030.CanonicalBoundaryRoute

open ColoredStorage SourcePointer SourcePositions Structural PhysicalForestMetadata PhysicalPacketStaging
open LocalComponentCompiler CanonicalRoutingDecomposition CanonicalHeadWingViews PacketLayers.Representation

variable {α β ρ ι : Type*} [DecidableEq α]

local instance canonicalBoundaryRouteColorOrder : LinearOrder (Option Bool) :=
  inferInstanceAs (LinearOrder (WithBot Bool))

set_option backward.isDefEq.respectTransparency false in
theorem locate (dummyId : ι) (color : α → Option Bool) (source : Source α ρ)
    (forest : TaggedForest (Option Bool) α ρ ι)
    (represented : ProjectionForest.Represents color ⟨source,[]⟩ (erase forest))
    (headerKey : α) (payload : Option Bool → α → Source β (Packet α ρ ι))
    (config : MultiSourceProgram.Configuration (Option Bool) β (Packet α ρ ι))
    (assembled : ForestConnector.assemble (ComponentPhysicalRepair.view none wingOrientation headerKey payload (encode forest))
      (ForestConnector.ThreeColors.layout (ComponentPhysicalRepair.view none wingOrientation headerKey payload (encode forest))) = some config)
    (side : Bool) (headPart tail : ProjectionLocal.Projected α ρ) (key : α)
    (low high : List ρ) (terminal : ρ)
    (selected : packed color (some side) source = activePacked headPart tail key true low high terminal) :
    ∃ current packet,
      SourcePositions.locate config.tree
        (HeadBoundaryRoute.path side (packed color (some (!side)) source).isSome headPart.isSome tail.isSome) = some current ∧
      current.focus = (payload (some side) key).setRoot (some packet :: none :: (payload (some side) key).rootRecord) := by
  have selectedPacked := (CanonicalComponentAssembly.packed_focus color source forest represented (some side)).trans selected
  obtain ⟨physicalHead,physicalTail,lower,upper,attachmentId,attachmentFields,headPresence,tailPresence,selectedView,_,_,_,_⟩ :=
    active_canonical dummyId (payload (some side)) (!side) none headPart tail key true low high terminal
      ((forest (some side)).map Cursor.focus) selectedPacked
  let opposite := render dummyId (payload (some (!side))) side none ((forest (some (!side))).map Cursor.focus)
  have oppositePresence : opposite.isSome = (packed color (some (!side)) source).isSome :=
    render_presence dummyId _ _ _ _ _ (CanonicalComponentAssembly.packed_focus color source forest represented (some (!side)))
  let middle := MixedHeadInputView.rawBlock
    [some (.header (ForestMirrorController.transform wingOrientation (encode forest) none)),none]
    ((payload none headerKey).mapRecords (fun packet => (dummyId,packet)))
  obtain ⟨tree,current,packet,view,walk,focus⟩ := HeadBoundaryRoute.component side dummyId dummyId lower upper
    attachmentId attachmentFields low high terminal physicalHead physicalTail opposite middle
    ((payload (some side) key).mapRecords (fun packet => (dummyId,packet)))
  rw [← selectedView] at view
  have middleExists : ∃ header,
      ComponentPhysicalRepair.view none wingOrientation headerKey payload (encode forest) none = some ⟨header,[]⟩ := by
    simp only [ComponentPhysicalRepair.view,PayloadForestController.transform,VirtualHeaderController.encode,ite_true,Option.map_some]
    exact ⟨_,rfl⟩
  obtain ⟨header,headerPresent⟩ := middleExists
  have assemblyView := CanonicalComponentAssembly.assembled dummyId _ _ headerPresent config assembled
  rw [CanonicalComponentAssembly.real_piece dummyId color source forest represented none (some true) (by decide),
    CanonicalComponentAssembly.real_piece dummyId color source forest represented none (some false) (by decide),
    CanonicalComponentAssembly.virtual_piece] at assemblyView
  have treeEq : config.tree.mapRecords (fun packet => (dummyId,packet)) = tree := by
    apply Option.some.inj
    rw [assemblyView]
    cases side <;> exact view
  rw [headPresence,tailPresence,oppositePresence,← treeEq] at walk
  have eraseAugment (tree : Source β (Packet α ρ ι)) :
      (tree.mapRecords (fun packet => (dummyId,packet))).mapRecords Prod.snd = tree := by
    rw [MultiSourceRecordEquivalence.map_source_comp]
    exact MultiSourceRecordEquivalence.map_source_id tree
  have packetWalk := congrArg (Option.map (Cursor.mapRecords Prod.snd)) walk
  rw [← SourcePositions.locate_mapRecords] at packetWalk
  simp only [eraseAugment,Option.map_some] at packetWalk
  refine ⟨current.mapRecords Prod.snd,packet,packetWalk,?_⟩
  change current.focus.mapRecords Prod.snd = _
  rw [focus,Source.mapRecords_setRoot]
  simp only [eraseAugment,Source.mapRecords_root]

end ChaCha.Paper20261030.CanonicalBoundaryRoute
