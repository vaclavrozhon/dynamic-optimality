import TangoSquared.Paper20261030.RootPreparedHeadExecution
import TangoSquared.Paper20261030.RootPreparedRestorationExecution

import TangoSquared.Paper20261030.RestoredHeadPayloadFrame

set_option autoImplicit false

/-! The minimum-depth SwitchHead program executes both preparations,
observations, head exchange, both balanced restorations, and charged parking
of the new roots. It returns both maintained canonical components and their
actual root caches. At this boundary the two whole source inventories are
exchanged, so separate initial logical uniqueness suffices. The global
primary scheduler is a separate obligation. -/

namespace TangoSquared.Paper20261030.SecondaryDecomposition.RootHeadExecution

open ColoredStorage SourcePointer Structural PhysicalForestMetadata Auxiliary AuxiliaryComponent BoundaryObservations PathDecomposition
open LocalComponentForestCompiler LocalComponentCompiler ForestConnector.ThreeColors MultiSourceProgram
open PreparedExposureExecution (Logical Datum)
open ObservedPreparedExposure

variable {α β η G : Type*} [DecidableEq α] [DecidableEq η] [DecidableEq G]

local instance rootHeadExecutionColorOrder : LinearOrder (Option Bool) := inferInstanceAs (LinearOrder (WithBot Bool))

set_option backward.isDefEq.respectTransparency false in
theorem execute (markerId : Nat) {a b : Nat} (reference : DepthTree a b) (preferences : DepthSplit → Bool)
    (terminal : (Secondary.decodeDepth reference preferences).terminal = a) (upper : a < b)
    (component : AuxiliaryComponent Nat Nat (Tagged Payload))
    (represented : Represents followsRight (source reference preferences) component)
    (color : Nat → Option Bool) (decorated : Source Nat (η × Cached))
    (erases : decorated.mapRecords Prod.snd = closed component) (logicalUnique : (decorated.inventory Prod.fst).Nodup)
    (forest : TaggedForest (Option Bool) Nat (Logical η) Nat)
    (forestRep : ProjectionForest.Represents color ⟨annotate Prod.fst color none decorated,[]⟩ (erase forest))
    (physicalUnique : Unique forest) (headerKey : Nat)
    (payload : Option Bool → Nat → Source β (List (Option (Datum Nat η))))
    (config : MultiSourceProgram.Configuration (Option Bool) β (List (Option (Datum Nat η))))
    (assembled : ForestConnector.assemble (representation none wingOrientation headerKey payload forest)
      (layout (representation none wingOrientation headerKey payload forest)) = some config)
    (tree : Source β (ReentryCell Nat η))
    (treeErases : tree.mapRecords Prod.snd = config.tree)
    (outside : List (Frame β (ReentryCell Nat η)))
    (global : MultiSourceProgram.Configuration (Sum (Option Bool) G) β (ReentryCell Nat η))
    (wellFormed : MultiSourceProgram.WellFormed global)
    (physical : CanonicalComponentUniqueness.Valid markerId global.tree)
    (reserved : markerId ∉ global.tree.inventory Prod.fst)
    (entry : Sum (Option Bool) G)
    (entryRep : MultiSourceSingleCursor.Represents entry ⟨tree,outside⟩ global)
    (saved : List (Option (Datum Nat η)))
    (anchor : G) (incoming : Cursor β (ReentryCell Nat η))
    (incomingRep : MultiSourceSingleCursor.Represents (.inr anchor) incoming global)
    (incomingPayload : CanonicalRetainedPayloadHandoff.PayloadAt (payload (color a) a) incoming)
    (real : color a ≠ none) (distinct : global.tree.shape.leaves.Nodup)
    (header : PrimaryHeaderController.Header η)
    (rootId : header.rootId = decorated.rootRecord.1)
    (leftWing : header.leftWing = (representation none wingOrientation headerKey payload forest (some true)).isSome)
    (rightWing : header.rightWing = (representation none wingOrientation headerKey payload forest (some false)).isSome)
    (cached : MultiSourceProgram.Configuration (Sum (Option Bool) G) β (CachedCell Nat η))
    (cachedErases : cached.mapRecords Prod.fst = MultiSourcePacketPrefix.attached saved tree outside global)
    (cachedCurrent : Cursor β (CachedCell Nat η))
    (cachedAtRoot : MultiSourceSingleCursor.Represents entry cachedCurrent cached)
    (cachedHeader : cachedCurrent.focus.rootRecord.2 = some header)
    (cachedIncoming : Cursor β (CachedCell Nat η))
    (cachedIncomingRep : MultiSourceSingleCursor.Represents (.inr anchor) cachedIncoming cached)
    (activeAnchor : G) (differentAnchors : anchor ≠ activeAnchor)
    (neutral : PacketParentNeutral.Neutral saved)
    (incomingPreferences : DepthSplit → Bool)
    (incomingTerminal : (Secondary.decodeDepth reference incomingPreferences).terminal = a)
    (incomingComponent : AuxiliaryComponent Nat Nat (Tagged Payload))
    (incomingRepresented : Represents followsRight (suffixSource reference incomingPreferences a ⟨by omega,by omega⟩) incomingComponent)
    (incomingColor : Nat → Option Bool) (incomingDecorated : Source Nat (η × Cached))
    (incomingErases : incomingDecorated.mapRecords Prod.snd = closed incomingComponent)
    (incomingLogicalUnique : (incomingDecorated.inventory Prod.fst).Nodup)
    (incomingForest : TaggedForest (Option Bool) Nat (Logical η) Nat)
    (incomingForestRep : ProjectionForest.Represents incomingColor ⟨annotate Prod.fst incomingColor none incomingDecorated,[]⟩ (erase incomingForest))
    (incomingUnique : Unique incomingForest)
    (incomingPayloads : Option Bool → Nat → Source β (List (Option (Datum Nat η))))
    (incomingConfig : MultiSourceProgram.Configuration (Option Bool) β (List (Option (Datum Nat η))))
    (incomingAssembly : ForestConnector.assemble (representation none wingOrientation headerKey incomingPayloads incomingForest)
      (layout (representation none wingOrientation headerKey incomingPayloads incomingForest)) = some incomingConfig)
    (attached : payload (color a) a = incomingConfig.tree)
    (incomingHeader : PrimaryHeaderController.Header η)
    (incomingRootId : incomingHeader.rootId = incomingDecorated.rootRecord.1)
    (incomingLeftWing : incomingHeader.leftWing = (representation none wingOrientation headerKey incomingPayloads incomingForest (some true)).isSome)
    (incomingRightWing : incomingHeader.rightWing = (representation none wingOrientation headerKey incomingPayloads incomingForest (some false)).isSome)
    (incomingCachedHeader : cachedIncoming.focus.rootRecord.2 = some incomingHeader)
    (beforePrimary afterPrimary oldPrimary incomingPrimary : PreferredProjection.PrefRouter α)
    (common : List (PrimaryWings.Exit α)) (side : Bool) (depthEq : common.length = a)
    (beforeWord : PrimaryWings.exits beforePrimary = common ++ ⟨side,incomingPrimary⟩ :: PrimaryWings.exits oldPrimary)
    (afterWord : PrimaryWings.exits afterPrimary = common ++ ⟨!side,oldPrimary⟩ :: PrimaryWings.exits incomingPrimary)
    (startDepth : a = 0) (activeBottom : b = (PrimaryWings.exits beforePrimary).length)
    (incomingBottom : b = a+1+(PrimaryWings.exits incomingPrimary).length)
    (activeColor : color = PackedPrimary.color 0 beforePrimary)
    (incomingColorEq : incomingColor = PackedPrimary.color (a+1) incomingPrimary) :
    ∃ (dormantOut activeOut : AuxiliaryComponent Nat Nat (Tagged Payload)),
      ∃ (dormantTarget activeTarget : Source Nat (η × Cached)),
      ∃ dormantForest dormantConfig activeFinalForest activeFinalConfig,
      ∃ (dormantPayload activePayload : Option Bool → Nat → Source β (List (Option (Datum Nat η)))),
      ∃ (dormantHeader activeHeader : PrimaryHeaderController.Header η),
      ∃ (final : Configuration (Sum (Option Bool) G) β (CachedCell Nat η)),
      ∃ (dormantReached activeReached : Cursor β (CachedCell Nat η)), ∃ reads cost, ∃ changed : List Nat,
      Represents followsRight (suffixSource reference preferences a ⟨by omega,by omega⟩) dormantOut ∧
      Represents followsRight (source reference (Secondary.spliceBits a preferences incomingPreferences)) activeOut ∧
      Run (RootPreparedRestorationController.program entry markerId saved.length (!outside.isEmpty) activeAnchor anchor a)
        (.first (.first (.first (.first (.first (.first (.first .start))))))) cached
        (.second () (.second () (some (.second () true)))) final reads cost ∧
      dormantTarget.mapRecords Prod.snd = closed dormantOut ∧ activeTarget.mapRecords Prod.snd = closed activeOut ∧
      activeTarget.inventory Prod.fst + dormantTarget.inventory Prod.fst = decorated.inventory Prod.fst + incomingDecorated.inventory Prod.fst ∧
      ProjectionForest.Represents (PackedPrimary.color (a+1) oldPrimary) ⟨annotate Prod.fst (PackedPrimary.color (a+1) oldPrimary) none dormantTarget,[]⟩ (erase dormantForest) ∧ Unique dormantForest ∧
      ForestConnector.assemble (representation none wingOrientation headerKey dormantPayload dormantForest)
        (layout (representation none wingOrientation headerKey dormantPayload dormantForest)) = some dormantConfig ∧
      PrimaryHeaderController.Represents dormantHeader header.bottom incomingHeader.start dormantTarget dormantForest headerKey dormantPayload ∧
      ProjectionForest.Represents (PackedPrimary.color 0 afterPrimary) ⟨annotate Prod.fst (PackedPrimary.color 0 afterPrimary) none activeTarget,[]⟩ (erase activeFinalForest) ∧ Unique activeFinalForest ∧
      ForestConnector.assemble (representation none wingOrientation headerKey activePayload activeFinalForest)
        (layout (representation none wingOrientation headerKey activePayload activeFinalForest)) = some activeFinalConfig ∧
      PrimaryHeaderController.Represents activeHeader incomingHeader.bottom header.start activeTarget activeFinalForest headerKey activePayload ∧
      activePayload (PackedPrimary.color 0 afterPrimary a) a = dormantConfig.tree ∧
      dormantPayload none headerKey = payload none headerKey ∧
      activePayload none headerKey = incomingPayloads none headerKey ∧
      (∀ side key, key ≠ a → dormantPayload (some side) key = payload (some side) key) ∧
      (∀ side key, key ∈ RepairedPayloadLayouts.ports
        (packed (PackedPrimary.color 0 afterPrimary) (some side)
          (annotate Prod.fst (PackedPrimary.color 0 afterPrimary) none activeTarget)) → key ≠ a →
        activePayload (some side) key = if key < a then payload (some side) key else incomingPayloads (some side) key) ∧
      MultiSourceSingleCursor.Represents (.inr anchor) dormantReached final ∧
      MultiSourceSingleCursor.Represents (.inr activeAnchor) activeReached final ∧
      dormantReached.focus.rootRecord.2 = some dormantHeader ∧ activeReached.focus.rootRecord.2 = some activeHeader ∧
      (∃ packet : List (Option (Datum Nat η)), packet.length = 2 ∧
        (dormantReached.focus.mapRecords Prod.fst).mapRecords Prod.snd = dormantConfig.tree.setRoot (packet ++ dormantConfig.tree.rootRecord)) ∧
      (∃ packet : List (Option (Datum Nat η)), packet.length = saved.length ∧
        (activeReached.focus.mapRecords Prod.fst).mapRecords Prod.snd = activeFinalConfig.tree.setRoot (packet ++ activeFinalConfig.tree.rootRecord)) ∧
      CanonicalComponentUniqueness.Valid markerId (final.mapRecords Prod.fst).tree ∧
      markerId ∉ (final.mapRecords Prod.fst).tree.inventory Prod.fst ∧
      (final.mapRecords Prod.fst).tree.inventory Prod.fst = global.tree.inventory Prod.fst ∧ WellFormed final ∧
      HeadCacheFrame.MetadataFrame Prod.fst changed cached.tree final.tree ∧ changed.length = 6 ∧
      (final.mapRecords Prod.fst).tree.inorderLabels Prod.fst = global.tree.inorderLabels Prod.fst ∧
      cost ≤ 1896960*(84420*Nat.clog 2 ((LocalReferences.depthReference reference).height+1)+624)+401167 := by
  obtain ⟨right,incomingRight,high,incomingHigh,highId,terminalId,incomingHighId,incomingTerminalId,
    taggedTail,incomingTail,incomingFinalConfig,data,activePhysicalRoot,bare,afterHead,reached,dormantReached,routingPacket,headReads,headCost,
    newLeftPayload,newRightPayload,newForest,newConfig,dormantBody,dormantForest,dormantConfig,headChanged,
    highKey,incomingHighKey,rightClean,rightMarked,incomingClean,incomingMarked,
    tailEq,incomingTailEq,headRun,activeLocated,activeErases,direction,activeStructural,dormantStructural,
    newReady,dormantReady,newVirtual,dormantVirtual,headPhysical,headReserved,headIds,headValid,headMetadata,headChangedLength,headOrder,headBound,
    result,activeSplit,incomingSplit,activeIds,incomingIds,newRep,newUnique,newAssembly,newTree,dormantRep,dormantUnique,dormantAssembly,
    dormantTree,dormantAttached,dormantValid,dormantLocated,descended,dormantView,activeStored,dormantStored,activeCacheRep,dormantCacheRep,bareEmpty,activePreparedWord,incomingPreparedWord,newPayloads⟩ :=
    RootPreparedHeadExecution.execute markerId reference preferences a terminal rfl upper component represented color decorated erases logicalUnique
      forest forestRep physicalUnique headerKey payload config assembled tree treeErases outside global wellFormed physical reserved
      entry entryRep saved anchor incoming incomingRep incomingPayload real distinct header rootId leftWing rightWing cached cachedErases
      cachedCurrent cachedAtRoot cachedHeader cachedIncoming cachedIncomingRep activeAnchor differentAnchors neutral
      incomingPreferences incomingTerminal incomingComponent incomingRepresented incomingColor incomingDecorated incomingErases incomingLogicalUnique
      incomingForest incomingForestRep incomingUnique incomingPayloads incomingConfig incomingAssembly attached incomingHeader incomingRootId
      incomingLeftWing incomingRightWing incomingCachedHeader beforePrimary afterPrimary oldPrimary incomingPrimary common side depthEq
      beforeWord afterWord startDepth activeBottom incomingBottom activeColor incomingColorEq
  let newPayload := Function.update payload (color a) (Function.update (payload (color a)) a incomingFinalConfig.tree)
  let physicalPayload := ComputedComponentReconstruction.payload newLeftPayload newRightPayload (incomingPayloads none headerKey)
  let dormantPayload := ComputedComponentReconstruction.payload (newPayload (some true)) (newPayload (some false)) (newPayload none headerKey)
  let activeSource := Source.fork (incomingHighId,incomingHigh)
    (.leaf a (incomingTerminalId,(terminalLeaf a).rootRecord)) incomingTail
  let dormantSource := Source.fork (highId,high) (.leaf a (terminalId,(terminalLeaf a).rootRecord)) taggedTail
  let enclosing := PacketPrefixTransfer.reidentify activePhysicalRoot saved
  let headers := PrimaryHeaderController.switchedMinimum header incomingHeader data.fresh
  have activeSourceUnique : (activeSource.inventory Prod.fst).Nodup := incomingIds.symm ▸ incomingLogicalUnique
  have dormantSourceUnique : (dormantSource.inventory Prod.fst).Nodup := activeIds.symm ▸ logicalUnique
  have activeSourceErases : activeSource.mapRecords Prod.snd = .fork incomingHigh (terminalLeaf a) incomingRight.tree := by
    simp only [activeSource,Source.mapRecords,incomingTailEq,terminalLeaf,Source.rootRecord]
  have dormantSourceErases : dormantSource.mapRecords Prod.snd = .fork high (terminalLeaf a) right.tree := by
    simp only [dormantSource,Source.mapRecords,tailEq,terminalLeaf,Source.rootRecord]
  have newExit : PackedPrimary.color 0 afterPrimary a = some (!data.direction) := by
    rw [direction,← depthEq]
    simp only [PackedPrimary.color,afterWord,PrimaryWings.portAt_boundary,Option.map_some]
  have boundaryMember : a ∈ activeSource.shape.leaves := by
    simp only [activeSource,Source.shape,RouterProjection.Router.leaves]
    exact List.mem_cons_self
  have headRawValid : WellFormed (afterHead.mapRecords Prod.fst) := by
    intro finger position present
    obtain ⟨cursor,located⟩ := headValid finger position present
    refine ⟨cursor.mapRecords Prod.fst,?_⟩
    simp only [Configuration.mapRecords,SourcePositions.locate_mapRecords,located,Option.map_some]
  have initialDistinct : cached.tree.shape.leaves.Nodup := by
    have same := congrArg (fun state : Configuration (Sum (Option Bool) G) β (ReentryCell Nat η) => state.tree.shape.leaves) cachedErases
    simp only [Configuration.mapRecords,Source.mapRecords_shape] at same
    have attachedLeaves : (MultiSourcePacketPrefix.attached saved tree outside global).tree.shape.leaves = global.tree.shape.leaves := by
      rw [entryRep.1]
      exact (SourcePointer.Step.write tree (tree.rootRecord.1,saved++tree.rootRecord.2) outside).leaves.symm
    rw [same,attachedLeaves]
    exact distinct
  have headDistinct : (afterHead.mapRecords Prod.fst).tree.shape.leaves.Nodup := by
    simpa only [Configuration.mapRecords,Source.mapRecords_shape] using headRun.leaves ▸ initialDistinct
  have dormantProper : (dormantReached.mapRecords Prod.fst).ancestors ≠ [] := by
    intro empty
    have emptyLength := congrArg List.length empty
    simp only [Cursor.mapRecords,List.length_map,List.length_nil] at emptyLength
    have lengths := congrArg List.length (SourcePositions.descend_address reached dormantReached _ descended)
    simp only [SourcePositions.address,List.length_map,List.length_reverse,List.length_append] at lengths
    have nonempty := HeadBoundaryRoute.path_nonempty (!data.direction)
      (ObservedRootDormantRoute.oppositePresent data) false (ObservedRootDormantRoute.tailPresent data)
    have positive : 0 < (ObservedRootDormantRoute.path data).length := by
      cases found : ObservedRootDormantRoute.path data with
      | nil => exact False.elim (nonempty found)
      | cons => simp only [List.length_cons]; omega
    omega
  have dormantViewRaw : (dormantReached.mapRecords Prod.fst).focus.mapRecords Prod.snd =
      dormantConfig.tree.setRoot ([some routingPacket,none] ++ dormantConfig.tree.rootRecord) := by
    simpa only [Cursor.mapRecords,MultiSourceRecordEquivalence.map_source_comp,Function.comp_def,List.cons_append,List.nil_append] using dormantView
  have attachedNew : physicalPayload (PackedPrimary.color 0 afterPrimary a) a = dormantConfig.tree := by
    rw [newExit]
    exact dormantAttached.symm
  obtain ⟨dormantOut,activeOut,dormantTarget,activeTarget,restoredDormantForest,restoredDormantConfig,activeFinalForest,activeFinalConfig,
    final,dormantFinal,activeFinal,restoreReads,restoreCost,dormantOutRep,activeOutRep,restored,dormantTargetErases,activeTargetErases,
    dormantTargetIds,activeTargetIds,restoredDormantRep,restoredDormantUnique,restoredDormantAssembly,restoredDormantCache,
    restoredActiveRep,restoredActiveUnique,restoredActiveAssembly,restoredActiveCache,dormantFinalRep,activeFinalRep,
    dormantFinalCache,activeFinalCache,dormantFinalView,activeFinalView,finalPhysical,finalReserved,finalIds,finalValid,restoredMetadata,restoredOrder,restoreBound⟩ :=
    RootPreparedRestorationExecution.execute markerId reference preferences terminal component right represented high activeSplit
      (PackedPrimary.color (a+1) oldPrimary) dormantSource dormantSourceErases dormantSourceUnique dormantForest dormantRep dormantUnique headerKey dormantPayload
      dormantConfig dormantAssembly (dormantReached.mapRecords Prod.fst) [some routingPacket,none] rfl dormantProper dormantViewRaw
      (afterHead.mapRecords Prod.fst) headRawValid headPhysical headReserved anchor (dormantLocated.mapRecords Prod.fst)
      headers.2 header.bottom incomingHeader.start dormantCacheRep afterHead rfl dormantReached dormantLocated dormantStored
      (PackedPrimary.color 0 afterPrimary) activeSource newForest newRep newUnique headerKey physicalPayload newConfig newAssembly
      bare.focus newTree.symm bare.ancestors enclosing activePhysicalRoot (PacketParentNeutral.reidentify saved activePhysicalRoot neutral)
      activeAnchor reached activeLocated activeErases boundaryMember (by rw [newExit]; exact Option.some_ne_none _) attachedNew headDistinct
      differentAnchors.symm incomingPreferences incomingTerminal incomingComponent incomingRight incomingRepresented incomingHigh incomingSplit
      activeSourceErases activeSourceUnique headers.1 incomingHeader.bottom header.start activeCacheRep activeStored
  let finalPayload := Function.update physicalPayload (PackedPrimary.color 0 afterPrimary a)
    (Function.update (physicalPayload (PackedPrimary.color 0 afterPrimary a)) a restoredDormantConfig.tree)
  have dormantBottom : dormantPayload none headerKey = payload none headerKey := by
    simp only [dormantPayload,ComputedComponentReconstruction.payload,newPayload,
      Function.update_of_ne (Ne.symm real)]
  have activeBottom : finalPayload none headerKey = incomingPayloads none headerKey := by
    simp [finalPayload,newExit,physicalPayload,ComputedComponentReconstruction.payload]
  have dormantFrame : ∀ side key, key ≠ a → dormantPayload (some side) key = payload (some side) key := by
    intro side key different
    cases side <;> exact RestoredHeadPayloadFrame.update_other payload (color a) a
      incomingFinalConfig.tree _ key different
  have incomingInterval := PreparedLeafIntervals.represented_incoming reference incomingPreferences ⟨by omega,by omega⟩
    incomingComponent incomingRepresented incomingDecorated incomingErases incomingTail incomingPreparedWord
  have incomingFull : Represents followsRight (source reference incomingPreferences) incomingComponent := by
    simpa only [suffixSource_minimum] using incomingRepresented
  have incomingErasedWord := congrArg (fun tree : Source Nat Cached => tree.shape.leaves) incomingErases
  simp only [Source.mapRecords_shape] at incomingErasedWord
  have newWord : activeSource.shape.leaves = List.range' a (b+1-a) :=
    incomingPreparedWord.trans (incomingErasedWord.trans (represented_leaf_word reference incomingPreferences incomingComponent incomingFull))
  have targetWord : activeTarget.shape.leaves = List.range' a (b+1-a) := by
    rw [← Source.mapRecords_shape Prod.snd activeTarget,activeTargetErases]
    exact represented_leaf_word reference (Secondary.spliceBits a preferences incomingPreferences) activeOut activeOutRep
  have activeFrame : ∀ side key, key ∈ RepairedPayloadLayouts.ports
      (packed (PackedPrimary.color 0 afterPrimary) (some side)
        (annotate Prod.fst (PackedPrimary.color 0 afterPrimary) none activeTarget)) → key ≠ a →
      finalPayload (some side) key = if key < a then payload (some side) key else incomingPayloads (some side) key := by
    intro side key member different
    have samePorts := RestoredHeadPayloadFrame.ports_of_leaf_word (PackedPrimary.color 0 afterPrimary) side
      (annotate Prod.fst (PackedPrimary.color 0 afterPrimary) none activeSource)
      (annotate Prod.fst (PackedPrimary.color 0 afterPrimary) none activeTarget)
      (by rw [annotate_shape,annotate_shape,newWord,targetWord])
    have retained := newPayloads side key (samePorts.symm ▸ member)
    apply RestoredHeadPayloadFrame.off_boundary payload incomingPayloads physicalPayload
      (fun _ => none)
      (ObservedCanonicalRootHeadExecution.projected Prod.fst color highId taggedTail)
      (ObservedCanonicalRootHeadExecution.projected Prod.fst incomingColor incomingHighId incomingTail)
      data.direction a data.fresh (ObservedHeadParameters.packet data.dormantHeader) (newPayload none headerKey)
      incomingFinalConfig.tree restoredDormantConfig.tree (color a) (PackedPrimary.color 0 afterPrimary a) side key different
    · intro impossible
      exact False.elim (List.not_mem_nil impossible)
    · intro inTail
      exact PreparedLeafIntervals.above incomingInterval key
        (CanonicalRetainedPortFacts.member_source Prod.fst incomingColor (some side) (some incomingHighId) incomingTail key inTail)
    · exact retained
  have enclosingLength : enclosing.length = saved.length := by simp only [enclosing,PacketPrefixTransfer.reidentify,List.length_map]
  rw [enclosingLength,bareEmpty] at restored
  have complete := MultiSourceFinish.finish (fun _ => ()) (fun _ => .first (.first .start))
    (fun _ => RootPreparedRestorationController.restoring activeAnchor anchor saved.length (!outside.isEmpty)) headRun restored
  have finalInventory : activeTarget.inventory Prod.fst + dormantTarget.inventory Prod.fst =
      decorated.inventory Prod.fst + incomingDecorated.inventory Prod.fst := by
    rw [activeTargetIds,dormantTargetIds]
    exact (congrArg₂ (·+·) incomingIds activeIds).trans (add_comm _ _)
  let changed := headChanged ++ [dormantFinal.focus.rootRecord.1.1,activeFinal.focus.rootRecord.1.1]
  have frame : HeadCacheFrame.MetadataFrame Prod.fst changed cached.tree final.tree := headMetadata.trans restoredMetadata
  have changedLength : changed.length = 6 := by simp only [changed,List.length_append,headChangedLength,List.length_cons,List.length_nil]
  have totalOrder : (final.mapRecords Prod.fst).tree.inorderLabels Prod.fst = global.tree.inorderLabels Prod.fst :=
    restoredOrder.trans headOrder
  obtain ⟨activePacket,activePacketLength,activeViewFinal⟩ := activeFinalView
  refine ⟨dormantOut,activeOut,dormantTarget,activeTarget,restoredDormantForest,restoredDormantConfig,activeFinalForest,activeFinalConfig,
    dormantPayload,finalPayload,{headers.2 with rootId := dormantTarget.rootRecord.1},{headers.1 with rootId := activeTarget.rootRecord.1},
    final,dormantFinal,activeFinal,_,_,changed,dormantOutRep,activeOutRep,complete,dormantTargetErases,activeTargetErases,finalInventory,
    restoredDormantRep,restoredDormantUnique,restoredDormantAssembly,restoredDormantCache,
    restoredActiveRep,restoredActiveUnique,restoredActiveAssembly,restoredActiveCache,?_,dormantBottom,activeBottom,dormantFrame,activeFrame,dormantFinalRep,activeFinalRep,
    dormantFinalCache,activeFinalCache,dormantFinalView,⟨activePacket,activePacketLength.trans enclosingLength,activeViewFinal⟩,
    finalPhysical,finalReserved,finalIds.trans headIds,finalValid,frame,changedLength,totalOrder,?_⟩
  · simp [finalPayload]
  · omega

end TangoSquared.Paper20261030.SecondaryDecomposition.RootHeadExecution
