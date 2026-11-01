import TangoSquared.Paper20261030.HeadCacheFrame
import TangoSquared.Paper20261030.RootDormantRestorationPreservesActive
import TangoSquared.Paper20261030.RootActiveRestorationPreservesDormant
import TangoSquared.Paper20261030.RootPreparedRestorationController

set_option autoImplicit false

/-! Both balanced restorations execute in sequence in the shared cached
tree. The dormant child is restored first and its new root is parked;
then the active component is restored while retaining that child. A final
charged copy parks the active root. All phase runs are derived here from
the prepared representation and split witnesses. -/

namespace TangoSquared.Paper20261030.SecondaryDecomposition.RootPreparedRestorationExecution

open ColoredStorage SourcePointer Structural PhysicalForestMetadata MultiSourceProgram
open Auxiliary AuxiliaryComponent BoundaryObservations PathDecomposition
open LocalComponentForestCompiler LocalComponentCompiler ForestConnector.ThreeColors
open EnclosedRootedComponentExecution (Packet Cell)
open CachedRootedComponentExecution (CachedCell)

variable {β η G : Type*} [DecidableEq η] [DecidableEq G]

local instance rootPreparedRestorationExecutionColorOrder : LinearOrder (Option Bool) :=
  inferInstanceAs (LinearOrder (WithBot Bool))

theorem execute (markerId : Nat) {a b : Nat} (reference : DepthTree a b) (preferences : DepthSplit → Bool)
    (prepared : (Secondary.decodeDepth reference preferences).terminal = a)
    (old right : AuxiliaryComponent Nat Nat (Tagged Payload))
    (oldRep : Represents followsRight (source reference preferences) old)
    (high : Cached) (split : PreparedSplitWitnesses.Sentinel old a right high)
    (color : Nat → Option Bool) (decorated : Source Nat (η × Cached)) (erases : decorated.mapRecords Prod.snd = .fork high (terminalLeaf a) right.tree)
    (logicalUnique : (decorated.inventory Prod.fst).Nodup)
    (forest : TaggedForest (Option Bool) Nat (LocalColoredCompiler.LogicalRecord Cached η (Option Bool)) Nat)
    (represented : ProjectionForest.Represents color ⟨annotate Prod.fst color none decorated,[]⟩ (erase forest))
    (physicalUnique : Unique forest) (headerKey : Nat) (payload : Option Bool → Nat → Source β (Packet Nat Cached Nat η))
    (config : Configuration (Option Bool) β (Packet Nat Cached Nat η))
    (assembled : ForestConnector.assemble (representation none wingOrientation headerKey payload forest)
      (layout (representation none wingOrientation headerKey payload forest)) = some config)
    (current : Cursor β (Cell Nat Cached Nat η)) (saved : Packet Nat Cached Nat η)
    (prefixLength : saved.length = 2) (proper : current.ancestors ≠ [])
    (view : current.focus.mapRecords Prod.snd = config.tree.setRoot (saved ++ config.tree.rootRecord))
    (global : Configuration (Sum (Option Bool) G) β (Cell Nat Cached Nat η))
    (valid : WellFormed global) (physical : CanonicalComponentUniqueness.Valid markerId global.tree)
    (reserved : markerId ∉ global.tree.inventory Prod.fst)
    (dormantAnchor : G) (entryRep : MultiSourceSingleCursor.Represents (.inr dormantAnchor) current global)
    (header : PrimaryHeaderController.Header η) (bottom : Int) (start : Nat)
    (headerRep : PrimaryHeaderController.Represents header bottom start decorated forest headerKey payload)
    (cached : Configuration (Sum (Option Bool) G) β (CachedCell Nat Cached Nat η))
    (cachedErases : cached.mapRecords Prod.fst = global)
    (cachedCurrent : Cursor β (CachedCell Nat Cached Nat η))
    (cachedAtRoot : MultiSourceSingleCursor.Represents (.inr dormantAnchor) cachedCurrent cached)
    (cachedHeader : cachedCurrent.focus.rootRecord.2 = some header)
    (activeColor : Nat → Option Bool) (activeDecorated : Source Nat (η × Cached))
    (activeForest : TaggedForest (Option Bool) Nat (LocalColoredCompiler.LogicalRecord Cached η (Option Bool)) Nat)
    (activeRep : ProjectionForest.Represents activeColor ⟨annotate Prod.fst activeColor none activeDecorated,[]⟩ (erase activeForest))
    (activeUnique : Unique activeForest) (activeHeaderKey : Nat)
    (activePayload : Option Bool → Nat → Source β (List (Option (PhysicalDatum Nat Cached Nat η (Option Bool)))))
    (activeConfig : MultiSourceProgram.Configuration (Option Bool) β (List (Option (PhysicalDatum Nat Cached Nat η (Option Bool)))))
    (activeAssembly : ForestConnector.assemble (representation none wingOrientation activeHeaderKey activePayload activeForest)
      (layout (representation none wingOrientation activeHeaderKey activePayload activeForest)) = some activeConfig)
    (activeTree : Source β (Cell Nat Cached Nat η)) (activeTreeErases : activeTree.mapRecords Prod.snd = activeConfig.tree)
    (activeOutside : List (Frame β (Cell Nat Cached Nat η))) (activeSaved : List (Option (PhysicalDatum Nat Cached Nat η (Option Bool)))) (activeOld : Nat)
    (activeNeutral : PacketParentNeutral.Neutral activeSaved)
    (activeAnchor : G) (activeCurrent : Cursor β (CachedCell Nat Cached Nat η))
    (activeLocated : MultiSourceSingleCursor.Represents (.inr activeAnchor) activeCurrent cached)
    (activeErases : activeCurrent.mapRecords Prod.fst = EnclosingPacketOperation.output activeSaved activeOld ⟨activeTree,activeOutside⟩)
    (member : a ∈ activeDecorated.shape.leaves) (real : activeColor a ≠ none)
    (attached : activePayload (activeColor a) a = config.tree)
    (distinct : global.tree.shape.leaves.Nodup)
    (differentAnchors : activeAnchor ≠ dormantAnchor)
    (incomingPreferences : DepthSplit → Bool)
    (incomingPrepared : (Secondary.decodeDepth reference incomingPreferences).terminal = a)
    (incoming incomingRight : AuxiliaryComponent Nat Nat (Tagged Payload))
    (incomingRep : Represents followsRight (suffixSource reference incomingPreferences a ⟨le_rfl,Secondary.reference_bounds reference⟩) incoming)
    (incomingHigh : Cached) (incomingSplit : PreparedSplitWitnesses.Sentinel incoming a incomingRight incomingHigh)
    (activeSourceErases : activeDecorated.mapRecords Prod.snd = .fork incomingHigh (terminalLeaf a) incomingRight.tree)
    (activeLogicalUnique : (activeDecorated.inventory Prod.fst).Nodup)
    (activeHeader : PrimaryHeaderController.Header η) (activeBottom : Int) (activeStart : Nat)
    (activeHeaderRep : PrimaryHeaderController.Represents activeHeader activeBottom activeStart activeDecorated activeForest activeHeaderKey activePayload)
    (activeCachedHeader : activeCurrent.focus.rootRecord.2 = some activeHeader) :
    ∃ (dormantOut activeOut : AuxiliaryComponent Nat Nat (Tagged Payload)),
      ∃ (dormantTarget activeTarget : Source Nat (η × Cached)),
      ∃ dormantForest dormantConfig activeFinalForest activeFinalConfig,
      ∃ (final : Configuration (Sum (Option Bool) G) β (CachedCell Nat Cached Nat η)),
      ∃ (dormantReached activeReached : Cursor β (CachedCell Nat Cached Nat η)), ∃ reads cost,
      Represents followsRight (suffixSource reference preferences a ⟨le_rfl,Secondary.reference_bounds reference⟩) dormantOut ∧
      Represents followsRight (source reference (Secondary.spliceBits a preferences incomingPreferences)) activeOut ∧
      Run (RootPreparedRestorationController.restoring activeAnchor dormantAnchor activeSaved.length (!activeOutside.isEmpty))
        (.first (.first .start)) cached (.second () (some (.second () true))) final reads cost ∧
      dormantTarget.mapRecords Prod.snd = closed dormantOut ∧ activeTarget.mapRecords Prod.snd = closed activeOut ∧
      dormantTarget.inventory Prod.fst = decorated.inventory Prod.fst ∧ activeTarget.inventory Prod.fst = activeDecorated.inventory Prod.fst ∧
      ProjectionForest.Represents color ⟨annotate Prod.fst color none dormantTarget,[]⟩ (erase dormantForest) ∧ Unique dormantForest ∧
      ForestConnector.assemble (representation none wingOrientation headerKey payload dormantForest)
        (layout (representation none wingOrientation headerKey payload dormantForest)) = some dormantConfig ∧
      PrimaryHeaderController.Represents {header with rootId := dormantTarget.rootRecord.1} bottom start dormantTarget dormantForest headerKey payload ∧
      let newPayload := Function.update activePayload (activeColor a) (Function.update (activePayload (activeColor a)) a dormantConfig.tree)
      ProjectionForest.Represents activeColor ⟨annotate Prod.fst activeColor none activeTarget,[]⟩ (erase activeFinalForest) ∧ Unique activeFinalForest ∧
      ForestConnector.assemble (representation none wingOrientation activeHeaderKey newPayload activeFinalForest)
        (layout (representation none wingOrientation activeHeaderKey newPayload activeFinalForest)) = some activeFinalConfig ∧
      PrimaryHeaderController.Represents {activeHeader with rootId := activeTarget.rootRecord.1} activeBottom activeStart activeTarget activeFinalForest activeHeaderKey newPayload ∧
      MultiSourceSingleCursor.Represents (.inr dormantAnchor) dormantReached final ∧
      MultiSourceSingleCursor.Represents (.inr activeAnchor) activeReached final ∧
      dormantReached.focus.rootRecord.2 = some {header with rootId := dormantTarget.rootRecord.1} ∧
      activeReached.focus.rootRecord.2 = some {activeHeader with rootId := activeTarget.rootRecord.1} ∧
      (∃ packet : Packet Nat Cached Nat η, packet.length = 2 ∧
        (dormantReached.focus.mapRecords Prod.fst).mapRecords Prod.snd = dormantConfig.tree.setRoot (packet ++ dormantConfig.tree.rootRecord)) ∧
      (∃ packet : Packet Nat Cached Nat η, packet.length = activeSaved.length ∧
        (activeReached.focus.mapRecords Prod.fst).mapRecords Prod.snd = activeFinalConfig.tree.setRoot (packet ++ activeFinalConfig.tree.rootRecord)) ∧
      CanonicalComponentUniqueness.Valid markerId (final.mapRecords Prod.fst).tree ∧
      markerId ∉ (final.mapRecords Prod.fst).tree.inventory Prod.fst ∧
      (final.mapRecords Prod.fst).tree.inventory Prod.fst = global.tree.inventory Prod.fst ∧ WellFormed final ∧
      HeadCacheFrame.MetadataFrame Prod.fst
        [dormantReached.focus.rootRecord.1.1,activeReached.focus.rootRecord.1.1] cached.tree final.tree ∧
      (final.mapRecords Prod.fst).tree.inorderLabels Prod.fst = global.tree.inorderLabels Prod.fst ∧
      cost ≤ 1896960*(4200*Nat.clog 2 ((LocalReferences.depthReference reference).height+1)+620)+92 := by
  have oldSuffixRep : Represents followsRight
      (suffixSource reference preferences a ⟨le_rfl,Secondary.reference_bounds reference⟩) old := by
    simpa only [suffixSource_minimum] using oldRep
  obtain ⟨dormantOut,dormantTarget,dormantForest,dormantConfig,dormantComponent,afterDormant,dormantReads,dormantCost,reached,
    updatedActiveForest,updatedActiveConfig,returnedActive,
    dormantOutRep,dormantRun,dormantErases,dormantIds,dormantRep,dormantUnique,dormantAssembly,dormantPresence,
    dormantComponentErases,reachedErases,dormantLocated,dormantHeader,globalIds,finalPhysical,finalReserved,finalValid,
    metadata,order,anchors,dormantCacheRep,dormantBound,updatedErases,updatedRep,updatedUnique,updatedAssembly,updatedPresence,
    activeReturned,updatedView,activeIdentity,activeCache,activeAncestors⟩ :=
    RootDormantRestorationPreservesActive.execute markerId reference preferences a ⟨le_rfl,Secondary.reference_bounds reference⟩ prepared old right oldSuffixRep high split
      color decorated erases logicalUnique forest represented physicalUnique headerKey payload config assembled current saved prefixLength proper view
      global valid physical reserved (.inr dormantAnchor) entryRep header bottom start headerRep cached cachedErases cachedCurrent cachedAtRoot cachedHeader
      activeColor activeDecorated activeForest activeRep activeUnique activeHeaderKey activePayload activeConfig activeAssembly activeTree activeTreeErases
      activeOutside activeSaved activeOld activeNeutral activeAnchor activeCurrent activeLocated activeErases member real attached distinct
  let newPayload := Function.update activePayload (activeColor a) (Function.update (activePayload (activeColor a)) a dormantConfig.tree)
  let parked := copyResult afterDormant (.inr dormantAnchor) (.inl none)
  let dormantRoot := PrimaryHeaderRefresh.refreshed header dormantTarget.rootRecord.1 reached
  let enclosing := PacketPrefixTransfer.reidentify activeTree.rootRecord.1 activeSaved
  have different : (Sum.inr activeAnchor : Sum (Option Bool) G) ≠ .inr dormantAnchor := by
    intro equal
    exact differentAnchors (Sum.inr.inj equal)
  have activeParked := MultiSourceParkContinuation.other (.inr dormantAnchor) (.inl none) (.inr activeAnchor) different
    returnedActive afterDormant activeReturned
  have dormantParked := MultiSourceParkContinuation.parked (.inr dormantAnchor) (.inl none) dormantRoot afterDormant dormantLocated
  have parkedValid : WellFormed parked := copy_wellFormed afterDormant finalValid _ _
  have parkedRawValid : WellFormed (parked.mapRecords Prod.fst) := by
    intro finger position present
    obtain ⟨cursor,located⟩ := parkedValid finger position present
    refine ⟨cursor.mapRecords Prod.fst,?_⟩
    simp only [Configuration.mapRecords,SourcePositions.locate_mapRecords,located,Option.map_some]
  have initialDistinct : cached.tree.shape.leaves.Nodup := by
    have same := congrArg (fun state : Configuration (Sum (Option Bool) G) β (Cell Nat Cached Nat η) => state.tree.shape.leaves) cachedErases
    simp only [Configuration.mapRecords,Source.mapRecords_shape] at same
    exact same.symm ▸ distinct
  have parkedDistinct : (parked.mapRecords Prod.fst).tree.shape.leaves.Nodup := by
    simpa only [parked,copyResult,Configuration.mapRecords,Source.mapRecords_shape] using dormantRun.leaves ▸ initialDistinct
  have activeCacheRep := PrimaryHeaderController.Represents.preserve activeHeader activeBottom activeStart activeDecorated
    activeForest updatedActiveForest activeHeaderKey activePayload newPayload activeHeaderRep updatedPresence
  have activeHeaderStored : returnedActive.focus.rootRecord.2 = some activeHeader := activeCache.trans activeCachedHeader
  have dormantRootErases : dormantRoot.mapRecords Prod.fst =
      EnclosingPacketOperation.output saved current.focus.rootRecord.1 ⟨dormantComponent.tree,current.ancestors⟩ :=
    (PrimaryHeaderRefresh.refreshed_erases header dormantTarget.rootRecord.1 reached).trans reachedErases
  have dormantTreeErases : dormantComponent.tree.mapRecords Prod.snd = dormantConfig.tree := congrArg Configuration.tree dormantComponentErases
  have dormantPayload : CanonicalRetainedPayloadHandoff.PayloadAt (newPayload (activeColor a) a) (dormantRoot.mapRecords Prod.fst) := by
    have atBoundary : newPayload (activeColor a) a = dormantConfig.tree := by simp [newPayload]
    unfold CanonicalRetainedPayloadHandoff.PayloadAt
    rw [atBoundary,dormantRootErases]
    simp only [EnclosingPacketOperation.output,PacketPrefixTransfer.output,PacketPrefixTransfer.attach,Source.mapRecords_setRoot]
    rw [← dormantTreeErases]
    cases dormantComponent.tree <;> rfl
  obtain ⟨activeOut,activeTarget,activeFinalForest,activeFinalConfig,activeComponent,afterActive,activeReads,activeCost,activeResult,
    dormantResult,dormantRaw,activeOutRep,activeRun,activeTargetErases,activeIds,activeFinalRep,activeFinalUnique,activeFinalAssembly,activePresence,
    activeComponentErases,activeResultErases,activeResultLocated,activeResultHeader,activeGlobalIds,activePhysical,activeReserved,activeValid,
    activeMetadata,activeOrder,activeAnchors,activeFinalCacheRep,dormantResultLocated,dormantResultErases,dormantResultHeader,
    dormantPayloadRep,differentRoots,dormantProper,dormantAttachment,samePayload,activeBound⟩ :=
    RootActiveRestorationPreservesDormant.execute markerId reference preferences incomingPreferences prepared incomingPrepared
      incoming incomingRight incomingRep incomingHigh incomingSplit
      activeColor activeDecorated activeSourceErases activeLogicalUnique updatedActiveForest updatedRep updatedUnique activeHeaderKey newPayload
      updatedActiveConfig updatedAssembly (returnedActive.mapRecords Prod.fst) enclosing updatedView
      (parked.mapRecords Prod.fst) parkedRawValid finalPhysical finalReserved (.inr activeAnchor) (activeParked.mapRecords Prod.fst)
      activeHeader activeBottom activeStart activeCacheRep parked rfl returnedActive activeParked activeHeaderStored
      dormantAnchor dormantRoot dormantParked dormantPayload real parkedDistinct
  have prefixLengthActive : enclosing.length = activeSaved.length := by simp only [enclosing,PacketPrefixTransfer.reidentify,List.length_map]
  have parentFlag : (!(returnedActive.mapRecords Prod.fst).ancestors.isEmpty) = !activeOutside.isEmpty := by
    rw [activeAncestors,activeErases]
    cases activeOutside <;> rfl
  rw [prefixLengthActive,parentFlag] at activeRun
  change Run (RootPreparedRestorationController.restore (.inr activeAnchor) activeSaved.length (!activeOutside.isEmpty) false)
    (.first .start) parked _ afterActive activeReads activeCost at activeRun
  have activeFinished := MultiSourceFinish.finish (fun _ => ()) (fun _ => false)
    (fun _ => RootPreparedRestorationController.parkActive activeAnchor) activeRun (RootPreparedRestorationController.park_run activeAnchor afterActive)
  change Run (RootPreparedRestorationController.active activeAnchor activeSaved.length (!activeOutside.isEmpty))
    (.first (.first .start)) parked _ _ _ _ at activeFinished
  have parkedDormant := MultiSourceParkContinuation.execute (.inr dormantAnchor) (.inl none)
    (RootPreparedRestorationController.active activeAnchor activeSaved.length (!activeOutside.isEmpty))
    (.first (.first .start)) (.second () true) afterDormant _ activeFinished
  have restored := MultiSourceFinish.finish (fun _ => ()) (fun _ => none)
    (fun _ => MultiSourceParkContinuation.program (.inr dormantAnchor) (.inl none)
      (RootPreparedRestorationController.active activeAnchor activeSaved.length (!activeOutside.isEmpty)) (.first (.first .start))) dormantRun parkedDormant
  let final := copyResult afterActive (.inr activeAnchor) (.inl none)
  let activeRoot := PrimaryHeaderRefresh.refreshed activeHeader activeTarget.rootRecord.1 activeResult
  have finalActive := MultiSourceParkContinuation.parked (.inr activeAnchor) (.inl none) activeRoot afterActive activeResultLocated
  have finalDormant := MultiSourceParkContinuation.other (.inr activeAnchor) (.inl none) (.inr dormantAnchor) (Ne.symm different)
    dormantResult afterActive dormantResultLocated
  have activeTreeErasesFinal : activeComponent.tree.mapRecords Prod.snd = activeFinalConfig.tree := congrArg Configuration.tree activeComponentErases
  have activeViewFinal : (activeRoot.focus.mapRecords Prod.fst).mapRecords Prod.snd = activeFinalConfig.tree.setRoot
      (PacketPrefixTransfer.reidentify activeComponent.tree.rootRecord.1 enclosing ++ activeFinalConfig.tree.rootRecord) := by
    have finalRoot : activeComponent.tree.rootRecord.2 = activeFinalConfig.tree.rootRecord := by
      simpa only [Source.mapRecords_root] using congrArg Source.rootRecord activeTreeErasesFinal
    have erased := (PrimaryHeaderRefresh.refreshed_erases activeHeader activeTarget.rootRecord.1 activeResult).trans activeResultErases
    have focus := congrArg (fun cursor : Cursor β (Cell Nat Cached Nat η) => cursor.focus.mapRecords Prod.snd) erased
    simpa only [Cursor.mapRecords,EnclosingPacketOperation.output,PacketPrefixTransfer.output,PacketPrefixTransfer.attach,
      Source.mapRecords_setRoot,activeTreeErasesFinal,finalRoot] using focus
  obtain ⟨dormantPacket,dormantPacketLength,dormantView⟩ := dormantAttachment
  have boundary : newPayload (activeColor a) a = dormantConfig.tree := by simp [newPayload]
  rw [boundary] at dormantView
  have finalDormantView : (dormantResult.focus.mapRecords Prod.fst).mapRecords Prod.snd =
      dormantConfig.tree.setRoot (dormantPacket ++ dormantConfig.tree.rootRecord) := by
    change (dormantResult.mapRecords Prod.fst).focus.mapRecords Prod.snd = _
    rw [dormantResultErases]
    exact dormantView
  have frontIds : afterDormant.tree.inventory (Prod.fst ∘ Prod.fst) = cached.tree.inventory (Prod.fst ∘ Prod.fst) := by
    rw [← mapRecords_inventory Prod.fst Prod.fst afterDormant.tree,
      ← mapRecords_inventory Prod.fst Prod.fst cached.tree]
    change (afterDormant.mapRecords Prod.fst).tree.inventory Prod.fst = (cached.mapRecords Prod.fst).tree.inventory Prod.fst
    rw [cachedErases]
    exact globalIds
  have backIds : afterActive.tree.inventory (Prod.fst ∘ Prod.fst) = parked.tree.inventory (Prod.fst ∘ Prod.fst) := by
    simpa only [Configuration.mapRecords,mapRecords_inventory] using activeGlobalIds
  have frontFrame := HeadCacheFrame.MetadataFrame.of_retained Prod.fst dormantComponent.tree.rootRecord.1
    cached.tree afterDormant.tree frontIds metadata
  have backFrame := HeadCacheFrame.MetadataFrame.of_retained Prod.fst activeComponent.tree.rootRecord.1
    parked.tree afterActive.tree backIds activeMetadata
  have dormantIdentity : dormantRoot.focus.rootRecord.1.1 = dormantComponent.tree.rootRecord.1 := by
    have same := congrArg (fun cursor : Cursor β (Cell Nat Cached Nat η) => cursor.focus.rootRecord.1) dormantRootErases
    simpa only [Cursor.mapRecords,Source.mapRecords_root,EnclosingPacketOperation.output,PacketPrefixTransfer.output_root_id] using same
  have activeIdentityFinal : activeRoot.focus.rootRecord.1.1 = activeComponent.tree.rootRecord.1 := by
    have same := congrArg (fun cursor : Cursor β (Cell Nat Cached Nat η) => cursor.focus.rootRecord.1)
      ((PrimaryHeaderRefresh.refreshed_erases activeHeader activeTarget.rootRecord.1 activeResult).trans activeResultErases)
    simpa only [Cursor.mapRecords,Source.mapRecords_root,EnclosingPacketOperation.output,PacketPrefixTransfer.output_root_id] using same
  have dormantIdentityFinal : dormantResult.focus.rootRecord.1.1 = dormantRoot.focus.rootRecord.1.1 := by
    have oldLabel := fingerLabel_of_represents Prod.fst (parked.mapRecords Prod.fst) (.inr dormantAnchor) _
      (dormantParked.mapRecords Prod.fst)
    have newLabel := fingerLabel_of_represents Prod.fst (afterActive.mapRecords Prod.fst) (.inr dormantAnchor) _
      (dormantResultLocated.mapRecords Prod.fst)
    rw [activeAnchors dormantAnchor,oldLabel] at newLabel
    simpa only [Cursor.mapRecords,Source.mapRecords_root] using (Option.some.inj newLabel).symm
  have frame : HeadCacheFrame.MetadataFrame Prod.fst
      [dormantResult.focus.rootRecord.1.1,activeRoot.focus.rootRecord.1.1] cached.tree final.tree := by
    rw [dormantIdentityFinal,dormantIdentity,activeIdentityFinal]
    exact frontFrame.trans backFrame
  have totalOrder : (final.mapRecords Prod.fst).tree.inorderLabels Prod.fst = global.tree.inorderLabels Prod.fst :=
    activeOrder.trans order
  refine ⟨dormantOut,activeOut,dormantTarget,activeTarget,dormantForest,dormantConfig,activeFinalForest,activeFinalConfig,
    final,dormantResult,activeRoot,_,_,dormantOutRep,activeOutRep,restored,dormantErases,activeTargetErases,dormantIds,activeIds,
    dormantRep,dormantUnique,dormantAssembly,dormantCacheRep,activeFinalRep,activeFinalUnique,activeFinalAssembly,activeFinalCacheRep,
    finalDormant,finalActive,dormantResultHeader.trans dormantHeader,activeResultHeader,
    ⟨dormantPacket,dormantPacketLength,finalDormantView⟩,⟨_,?_,activeViewFinal⟩,activePhysical,activeReserved,
    activeGlobalIds.trans globalIds,copy_wellFormed afterActive activeValid _ _,frame,totalOrder,?_⟩
  · simp only [PacketPrefixTransfer.reidentify,List.length_map,prefixLengthActive]
  · omega

end TangoSquared.Paper20261030.SecondaryDecomposition.RootPreparedRestorationExecution
