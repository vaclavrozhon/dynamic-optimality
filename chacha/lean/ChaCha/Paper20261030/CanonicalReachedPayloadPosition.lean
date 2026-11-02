import ChaCha.Paper20261030.NeutralEnclosingContext
import ChaCha.Paper20261030.CanonicalRetainedPayloadHandoff
import ChaCha.Paper20261030.ReachedCursorUniqueness

set_option autoImplicit false

/-! Identifying the already reached incoming cursor with its exact
canonical routing-leaf context. A neutral enclosing prefix may overwrite
the active component's root packet, but the connector context remains
neutral and nonempty. This supplies the parent-repair boundary needed by
the subsequent nested preparation. No extra runtime move is performed. -/

namespace ChaCha.Paper20261030.CanonicalReachedPayloadPosition

open ColoredStorage SourcePointer Structural PhysicalForestMetadata MultiSourceProgram
open LocalComponentForestCompiler LocalComponentCompiler ForestConnector.ThreeColors
open EnclosedRootedComponentExecution (Packet Cell)

variable {α β ρ ι η F : Type*} [DecidableEq α] [DecidableEq ι] [DecidableEq F]

local instance reachedPayloadPositionColorOrder : LinearOrder (Option Bool) := inferInstanceAs (LinearOrder (WithBot Bool))

theorem position (markerId : ι) (color : α → Option Bool) (decorated : Source α (η × ρ))
    (forest : TaggedForest (Option Bool) α (LocalColoredCompiler.LogicalRecord ρ η (Option Bool)) ι)
    (represented : ProjectionForest.Represents color ⟨annotate Prod.fst color none decorated,[]⟩ (erase forest))
    (headerKey : α) (payload : Option Bool → α → Source β (Packet α ρ ι η))
    (config : Configuration (Option Bool) β (Packet α ρ ι η))
    (assembled : ForestConnector.assemble (representation none wingOrientation headerKey payload forest)
      (layout (representation none wingOrientation headerKey payload forest)) = some config)
    (tree : Source β (Cell α ρ ι η)) (erases : tree.mapRecords Prod.snd = config.tree)
    (outside : List (Frame β (Cell α ρ ι η))) (saved : Packet α ρ ι η) (old : ι)
    (neutral : PacketParentNeutral.Neutral saved)
    (global : Configuration F β (Cell α ρ ι η)) (exit finger : F)
    (returned : MultiSourceSingleCursor.Represents exit (EnclosingPacketOperation.output saved old ⟨tree,outside⟩) global)
    (valid : CanonicalComponentUniqueness.Valid markerId global.tree) (distinct : global.tree.shape.leaves.Nodup)
    (current : Cursor β (Cell α ρ ι η)) (positioned : MultiSourceSingleCursor.Represents finger current global)
    (key : α) (member : key ∈ decorated.shape.leaves) (real : color key ≠ none)
    (payloadAt : CanonicalRetainedPayloadHandoff.PayloadAt (payload (color key) key) current) :
    ∃ tagged records inside originalConnectors connectors,
      forest (color key) = some ⟨tagged,[]⟩ ∧
      tagged = plug (.leaf key (current.focus.rootRecord.1,records)) inside ∧
      originalConnectors ≠ [] ∧ EmptyConnector originalConnectors ∧
      config.tree = plug (CanonicalRoutingCursor.cursor (payload (color key)) (wingOrientation (color key))
        ⟨.leaf key (current.focus.rootRecord.1,records),inside⟩).tree originalConnectors ∧
      (∀ fresh : Cursor β (Packet α ρ ι η), ∃ next,
        ForestConnector.assemble (Function.update (representation none wingOrientation headerKey payload forest) (color key) (some fresh))
          (layout (Function.update (representation none wingOrientation headerKey payload forest) (color key) (some fresh))) = some next ∧
        next.tree = plug fresh.tree originalConnectors) ∧
      connectors ≠ [] ∧ FrameRecords PacketParentNeutral.Neutral connectors ∧
      (∀ replacement : Source β (Packet α ρ ι η),
        (plug replacement originalConnectors).setRoot (PacketPrefixTransfer.reidentify tree.rootRecord.1 saved ++ tree.rootRecord.2) =
          plug replacement connectors) ∧
      current.mapRecords Prod.snd =
        ⟨(CanonicalRoutingCursor.cursor (payload (color key)) (wingOrientation (color key))
            ⟨.leaf key (current.focus.rootRecord.1,records),inside⟩).focus,
          (CanonicalRoutingCursor.cursor (payload (color key)) (wingOrientation (color key))
            ⟨.leaf key (current.focus.rootRecord.1,records),inside⟩).ancestors ++
              (connectors ++ (EnclosingPacketOperation.output saved old ⟨tree,outside⟩).ancestors.map (Frame.mapRecords Prod.snd))⟩ := by
  obtain ⟨tagged,ident,records,inside,connectors,present,taggedEq,proper,empty,componentView,replacementAssembly⟩ :=
    real_payload_position color decorated forest represented headerKey payload config assembled key member real
  let route := CanonicalRoutingCursor.cursor (payload (color key)) (wingOrientation (color key))
    ⟨.leaf key (ident,records),inside⟩
  let finished := EnclosingPacketOperation.output saved old ⟨tree,outside⟩
  let packet := PacketPrefixTransfer.reidentify tree.rootRecord.1 saved ++ tree.rootRecord.2
  have connectorNeutral := PacketParentNeutral.empty_context connectors empty
  have rootNeutral : PacketParentNeutral.Neutral tree.rootRecord.2 := by
    have atRoot := FrameRecords.root PacketParentNeutral.Neutral route.tree connectors proper connectorNeutral
    rw [← componentView] at atRoot
    have rootErases := congrArg Source.rootRecord erases
    simp only [Source.mapRecords_root] at rootErases
    rw [rootErases]
    exact atRoot
  have newNeutral := PacketParentNeutral.append (PacketParentNeutral.reidentify saved tree.rootRecord.1 neutral) rootNeutral
  obtain ⟨changed,changedProper,changedNeutral,rebuild⟩ := proper_context_setRoot_preserves
    PacketParentNeutral.Neutral connectors proper connectorNeutral packet newNeutral
  have changedTree := rebuild route.tree
  have finishedFocus : finished.focus.mapRecords Prod.snd = plug route.tree changed := by
    change (tree.setRoot (tree.rootRecord.1,packet)).mapRecords Prod.snd = _
    rw [Source.mapRecords_setRoot,erases,componentView,changedTree]
  let view : Cursor β (Packet α ρ ι η) :=
    ⟨route.focus,route.ancestors++(changed++finished.ancestors.map (Frame.mapRecords Prod.snd))⟩
  have viewTree : view.tree = global.tree.mapRecords Prod.snd := by
    rw [returned.1]
    change view.tree = (plug finished.focus finished.ancestors).mapRecords Prod.snd
    rw [← plug_mapRecords,finishedFocus]
    change plug route.focus (route.ancestors++(changed++finished.ancestors.map (Frame.mapRecords Prod.snd))) = _
    rw [plug_append,plug_append]
    rfl
  have normalized : view.focus.setRoot (payload (color key) key).rootRecord = payload (color key) key := by
    change route.focus.setRoot _ = _
    rw [CanonicalRoutingCursor.leaf]
    cases payload (color key) key <;> rfl
  obtain ⟨actual,located,actualErases,_⟩ := retained_subtree_handoff_of_leaves rfl rfl distinct valid.2.2 finger rfl
    current positioned view viewTree (payload (color key) key).rootRecord (payload (color key) key).rootRecord
    (payloadAt.trans normalized.symm)
  have same := positioned.unique located
  rw [← same] at actualErases
  have focusErases := congrArg Cursor.focus actualErases
  change current.focus.mapRecords Prod.snd = route.focus at focusErases
  rw [CanonicalRoutingCursor.leaf] at focusErases
  have routingFocus : current.focus.mapRecords Prod.snd =
      CanonicalPacketLayerViews.routing (payload (color key)) (wingOrientation (color key)) (parentId Prod.fst inside)
        (.leaf key (ident,records)) := by
    simpa only [CanonicalPacketLayerViews.leaf] using focusErases
  have identity := CanonicalMixedPacketRepair.routing_root_id markerId (payload (color key)) (wingOrientation (color key))
    (parentId Prod.fst inside) (.leaf key (ident,records)) current.focus routingFocus
    (SourceRecordPredicate.focused _ current (positioned.1 ▸ valid.1))
    (SourceRecordPredicate.focused _ current (positioned.1 ▸ valid.2.1))
  change current.focus.rootRecord.1 = ident at identity
  refine ⟨tagged,records,inside,connectors,changed,present,?_,proper,empty,?_,replacementAssembly,changedProper,changedNeutral,rebuild,?_⟩
  · rw [identity]
    exact taggedEq
  · rw [identity]
    exact componentView
  · rw [identity]
    exact actualErases

end ChaCha.Paper20261030.CanonicalReachedPayloadPosition
