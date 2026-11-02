import ChaCha.Paper20261030.HeadCacheFrameControllers
import ChaCha.Paper20261030.HeadCacheFrameHeadOrderCanonical
import ChaCha.Paper20261030.RootPreparedPairHeaderExecution
import ChaCha.Paper20261030.RootPreparedHeadController
import ChaCha.Paper20261030.PrimaryObservedRootHeadParameters
import ChaCha.Paper20261030.ObservedCanonicalRootHeadExecution
import ChaCha.Paper20261030.ComputedVirtualHeaderReadiness
import ChaCha.Paper20261030.CanonicalRootActiveHeadForest
import ChaCha.Paper20261030.EnclosingOutputFocusValidity
import ChaCha.Paper20261030.CanonicalDormantHeadForest
import ChaCha.Paper20261030.CanonicalRealPayloadValidity
import ChaCha.Paper20261030.RootPreparedHeadReturnController
import ChaCha.Paper20261030.RootPreparedHeadCacheController
import ChaCha.Paper20261030.RootSwitchedHeaderRepresentation

set_option autoImplicit false

/-! Minimum-depth preparation and head exchange in one actual shared-tree
program. Both source representations determine the observed computation;
the run reconstructs both canonical forests, reaches the dormant component,
and installs the switched caches. Balanced restoration is a later phase. -/

namespace ChaCha.Paper20261030.SecondaryDecomposition.RootPreparedHeadExecution

open ColoredStorage SourcePointer Structural PhysicalForestMetadata Auxiliary AuxiliaryComponent BoundaryObservations PathDecomposition
open LocalComponentForestCompiler LocalComponentCompiler ForestConnector.ThreeColors MultiSourceProgram
open PreparedExposureExecution (Logical Datum)
open ObservedPreparedExposure

variable {α β η G : Type*} [DecidableEq α] [DecidableEq η] [DecidableEq G]

local instance rootPreparedHeadExecutionColorOrder : LinearOrder (Option Bool) := inferInstanceAs (LinearOrder (WithBot Bool))

set_option backward.isDefEq.respectTransparency false in
theorem execute (markerId : Nat) {a b : Nat} (reference : DepthTree a b) (preferences : DepthSplit → Bool)
    (d : Nat) (terminal : (Secondary.decodeDepth reference preferences).terminal = d) (minimum : d = a) (upper : d < b)
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
    (incomingPayload : CanonicalRetainedPayloadHandoff.PayloadAt (payload (color d) d) incoming)
    (real : color d ≠ none) (distinct : global.tree.shape.leaves.Nodup)
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
    (incomingTerminal : (Secondary.decodeDepth reference incomingPreferences).terminal = d)
    (incomingComponent : AuxiliaryComponent Nat Nat (Tagged Payload))
    (incomingRepresented : Represents followsRight (suffixSource reference incomingPreferences d ⟨by omega,by omega⟩) incomingComponent)
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
    (attached : payload (color d) d = incomingConfig.tree)
    (incomingHeader : PrimaryHeaderController.Header η)
    (incomingRootId : incomingHeader.rootId = incomingDecorated.rootRecord.1)
    (incomingLeftWing : incomingHeader.leftWing = (representation none wingOrientation headerKey incomingPayloads incomingForest (some true)).isSome)
    (incomingRightWing : incomingHeader.rightWing = (representation none wingOrientation headerKey incomingPayloads incomingForest (some false)).isSome)
    (incomingCachedHeader : cachedIncoming.focus.rootRecord.2 = some incomingHeader)
    (beforePrimary afterPrimary oldPrimary incomingPrimary : PreferredProjection.PrefRouter α)
    (common : List (PrimaryWings.Exit α)) (side : Bool) (depthEq : common.length = d)
    (beforeWord : PrimaryWings.exits beforePrimary = common ++ ⟨side,incomingPrimary⟩ :: PrimaryWings.exits oldPrimary)
    (afterWord : PrimaryWings.exits afterPrimary = common ++ ⟨!side,oldPrimary⟩ :: PrimaryWings.exits incomingPrimary)
    (startDepth : a = 0) (activeBottom : b = (PrimaryWings.exits beforePrimary).length)
    (incomingBottom : b = d+1+(PrimaryWings.exits incomingPrimary).length)
    (activeColor : color = PackedPrimary.color 0 beforePrimary)
    (incomingColorEq : incomingColor = PackedPrimary.color (d+1) incomingPrimary) :
    ∃ (right incomingRight : AuxiliaryComponent Nat Nat (Tagged Payload)) (high incomingHigh : Cached),
      ∃ highId terminalId incomingHighId incomingTerminalId,
      ∃ taggedTail incomingTail : Source Nat (η × Cached),
      ∃ (incomingFinalConfig : MultiSourceProgram.Configuration (Option Bool) β (List (Option (Datum Nat η)))),
      ∃ (data : RootPreparedHeadController.Data η) (activePhysicalRoot : Nat),
      ∃ (bare : Cursor β (ReentryCell Nat η)) (final : MultiSourceProgram.Configuration (Sum (Option Bool) G) β (CachedCell Nat η)),
      ∃ (reached dormantReached : Cursor β (CachedCell Nat η)), ∃ routingPacket reads cost,
      ∃ newLeftPayload newRightPayload newForest newConfig,
      ∃ (dormantBody : Source β (ReentryCell Nat η)), ∃ dormantForest dormantConfig, ∃ changed : List Nat,
      high.2.1 = d ∧ incomingHigh.2.1 = d ∧
      Clean right.core ∧ MarkedPorts right ∧
      Clean incomingRight.core ∧ MarkedPorts incomingRight ∧
      taggedTail.mapRecords Prod.snd = right.tree ∧
      incomingTail.mapRecords Prod.snd = incomingRight.tree ∧
      MultiSourceProgram.Run
        (RootPreparedHeadCacheController.program entry markerId saved.length (!outside.isEmpty) activeAnchor anchor d)
        (.first (.first (.first (.first (.first (.first .start)))))) cached
        (.second (some (⟨{header with rootId := highId},{incomingHeader with rootId := incomingHighId},
          BoundaryReadController.sentinelResult Prod.fst color (highId,high)
            (terminalId,(terminalLeaf d).rootRecord) d taggedTail,
          BoundaryReadController.sentinelResult Prod.fst incomingColor (incomingHighId,incomingHigh)
            (incomingTerminalId,(terminalLeaf d).rootRecord) d incomingTail⟩,data))
          (.second () (some .done))) final reads cost ∧
      MultiSourceSingleCursor.Represents (.inr activeAnchor) reached final ∧
      reached.mapRecords Prod.fst = EnclosingPacketOperation.output
        (PacketPrefixTransfer.reidentify activePhysicalRoot saved) activePhysicalRoot bare ∧
      data.direction = side ∧
      Source.fork data.fresh.incomingHigh (.leaf d data.fresh.incomingTerminal)
        (annotate Prod.fst incomingColor (some incomingHighId) incomingTail) =
        annotate Prod.fst (PackedPrimary.color 0 afterPrimary) none
          (.fork (incomingHighId,incomingHigh)
            (.leaf d (incomingTerminalId,(terminalLeaf d).rootRecord)) incomingTail) ∧
      Structural.HeadBoundary.dormantTree data.fresh d
        (annotate Prod.fst color (some highId) taggedTail) =
        annotate Prod.fst (PackedPrimary.color (d+1) oldPrimary) none
          (.fork (highId,high) (.leaf d (terminalId,(terminalLeaf d).rootRecord)) taggedTail) ∧
      VirtualPhysicalPackets.Ready data.newHeader ∧ VirtualPhysicalPackets.Ready data.dormantHeader ∧
      VirtualPhysicalPackets.decode data.newHeader =
        (packed (PackedPrimary.color 0 afterPrimary) none (annotate Prod.fst (PackedPrimary.color 0 afterPrimary) none
          (.fork (incomingHighId,incomingHigh)
            (.leaf d (incomingTerminalId,(terminalLeaf d).rootRecord)) incomingTail))).map (fun source => ⟨source,[]⟩) ∧
      VirtualPhysicalPackets.decode data.dormantHeader =
        (packed (PackedPrimary.color (d+1) oldPrimary) none (annotate Prod.fst (PackedPrimary.color (d+1) oldPrimary) none
          (.fork (highId,high) (.leaf d (terminalId,(terminalLeaf d).rootRecord)) taggedTail))).map (fun source => ⟨source,[]⟩) ∧
      CanonicalComponentUniqueness.Valid markerId (final.mapRecords Prod.fst).tree ∧
      markerId ∉ (final.mapRecords Prod.fst).tree.inventory Prod.fst ∧
      (final.mapRecords Prod.fst).tree.inventory Prod.fst = global.tree.inventory Prod.fst ∧
      MultiSourceProgram.WellFormed final ∧
      HeadCacheFrame.MetadataFrame Prod.fst changed cached.tree final.tree ∧ changed.length = 4 ∧
      (final.mapRecords Prod.fst).tree.inorderLabels Prod.fst = global.tree.inorderLabels Prod.fst ∧
      cost ≤ 8*(474240*(40110*Nat.clog 2 ((LocalReferences.depthReference reference).height+1)+2)+49920)+1715 ∧
      let newPayload := Function.update payload (color d) (Function.update (payload (color d)) d incomingFinalConfig.tree)
      CanonicalHeadSuccessor.Result newPayload incomingPayloads
        (fun _ => none)
        (ObservedCanonicalRootHeadExecution.projected Prod.fst color highId taggedTail)
        (ObservedCanonicalRootHeadExecution.projected Prod.fst incomingColor incomingHighId incomingTail)
        data.direction d data.fresh (ObservedHeadParameters.packet data.newHeader) (ObservedHeadParameters.packet data.dormantHeader)
        (newPayload none headerKey) (incomingPayloads none headerKey) (some (bare.focus.mapRecords Prod.snd)) ∧
      PreparedSplitWitnesses.Sentinel component d right high ∧
      PreparedSplitWitnesses.Sentinel incomingComponent d incomingRight incomingHigh ∧
      (Source.fork (highId,high)
          (.leaf d (terminalId,(terminalLeaf d).rootRecord)) taggedTail).inventory Prod.fst = decorated.inventory Prod.fst ∧
      (Source.fork (incomingHighId,incomingHigh) (.leaf d (incomingTerminalId,(terminalLeaf d).rootRecord)) incomingTail).inventory Prod.fst =
        incomingDecorated.inventory Prod.fst ∧
      let newSource := annotate Prod.fst (PackedPrimary.color 0 afterPrimary) none
        (.fork (incomingHighId,incomingHigh)
          (.leaf d (incomingTerminalId,(terminalLeaf d).rootRecord)) incomingTail)
      ProjectionForest.Represents (PackedPrimary.color 0 afterPrimary) ⟨newSource,[]⟩ (erase newForest) ∧ Unique newForest ∧
      ForestConnector.assemble
        (ComponentPhysicalRepair.view none wingOrientation headerKey
          (ComputedComponentReconstruction.payload newLeftPayload newRightPayload (incomingPayloads none headerKey)) (encode newForest))
        (layout (ComponentPhysicalRepair.view none wingOrientation headerKey
          (ComputedComponentReconstruction.payload newLeftPayload newRightPayload (incomingPayloads none headerKey)) (encode newForest))) = some newConfig ∧
      newConfig.tree = bare.focus.mapRecords Prod.snd ∧
      ProjectionForest.Represents (PackedPrimary.color (d+1) oldPrimary)
        ⟨annotate Prod.fst (PackedPrimary.color (d+1) oldPrimary) none
          (.fork (highId,high) (.leaf d (terminalId,(terminalLeaf d).rootRecord)) taggedTail),[]⟩ (erase dormantForest) ∧
      Unique dormantForest ∧
      ForestConnector.assemble
        (ComponentPhysicalRepair.view none wingOrientation headerKey
          (ComputedComponentReconstruction.payload (newPayload (some true)) (newPayload (some false)) (newPayload none headerKey)) (encode dormantForest))
        (layout (ComponentPhysicalRepair.view none wingOrientation headerKey
          (ComputedComponentReconstruction.payload (newPayload (some true)) (newPayload (some false)) (newPayload none headerKey)) (encode dormantForest))) = some dormantConfig ∧
      dormantConfig.tree = dormantBody.mapRecords Prod.snd ∧
      dormantConfig.tree = ComputedComponentReconstruction.payload newLeftPayload newRightPayload
        (incomingPayloads none headerKey) (some (!data.direction)) d ∧
      CanonicalComponentUniqueness.Valid markerId dormantBody ∧
      MultiSourceSingleCursor.Represents (.inr anchor) dormantReached final ∧
      SourcePositions.descend reached (ObservedRootDormantRoute.path data) = some dormantReached ∧
      dormantReached.focus.mapRecords (fun record => record.1.2) =
        dormantConfig.tree.setRoot (some routingPacket :: none :: dormantConfig.tree.rootRecord) ∧
      reached.focus.rootRecord.2 = some (PrimaryHeaderController.switchedMinimum header incomingHeader data.fresh).1 ∧
      dormantReached.focus.rootRecord.2 = some (PrimaryHeaderController.switchedMinimum header incomingHeader data.fresh).2 ∧
      PrimaryHeaderController.Represents (PrimaryHeaderController.switchedMinimum header incomingHeader data.fresh).1 incomingHeader.bottom header.start
        (.fork (incomingHighId,incomingHigh) (.leaf d (incomingTerminalId,(terminalLeaf d).rootRecord)) incomingTail)
        newForest headerKey (ComputedComponentReconstruction.payload newLeftPayload newRightPayload (incomingPayloads none headerKey)) ∧
      PrimaryHeaderController.Represents (PrimaryHeaderController.switchedMinimum header incomingHeader data.fresh).2 header.bottom incomingHeader.start
        (.fork (highId,high) (.leaf d (terminalId,(terminalLeaf d).rootRecord)) taggedTail)
        dormantForest headerKey (ComputedComponentReconstruction.payload (newPayload (some true)) (newPayload (some false)) (newPayload none headerKey)) ∧
      bare.ancestors.isEmpty = outside.isEmpty ∧
      d::taggedTail.shape.leaves = decorated.shape.leaves ∧
      d::incomingTail.shape.leaves = incomingDecorated.shape.leaves ∧
      ∀ side key, key ∈ RepairedPayloadLayouts.ports (packed (PackedPrimary.color 0 afterPrimary) (some side) newSource) →
        CanonicalHeadSuccessor.Payload newPayload incomingPayloads
          (fun _ => none)
          (ObservedCanonicalRootHeadExecution.projected Prod.fst color highId taggedTail)
          (ObservedCanonicalRootHeadExecution.projected Prod.fst incomingColor incomingHighId incomingTail)
          data.direction d data.fresh (ObservedHeadParameters.packet data.dormantHeader) (newPayload none headerKey)
          side key (ComputedComponentReconstruction.payload newLeftPayload newRightPayload (incomingPayloads none headerKey) (some side) key) := by
  obtain ⟨right,incomingRight,high,incomingHigh,highId,terminalId,incomingHighId,incomingTerminalId,
    taggedTail,incomingTail,activeFinalForest,incomingFinalForest,activeFinalConfig,incomingFinalConfig,
    middle,returnedActive,reachedIncoming,activePhysicalRoot,incomingAttachment,firstReads,firstCost,
    highKey,incomingHighKey,rightClean,rightMarked,incomingClean,incomingMarked,
    tailEq,incomingTailEq,front,activeFinalRep,activeFinalUnique,incomingFinalRep,incomingFinalUnique,
    incomingFinalAssembly,incomingPresence,activeReturned,activeView,activeIdentity,activeCache,
    incomingReturned,incomingCache,incomingAttachmentLength,incomingView,incomingPayloadAt,middleValid,middlePhysical,
    middleReserved,middleIds,prepFrame,prepOrder,frontBound,activeFinalAssembly,activePresence,activeLeaves,incomingLeaves,activeAncestors,activeSplit,incomingSplit,activeIds,incomingIds⟩ :=
    RootPreparedPairHeaderExecution.execute markerId reference preferences d terminal minimum upper component represented color decorated erases logicalUnique
      forest forestRep physicalUnique headerKey payload config assembled tree treeErases outside global wellFormed physical reserved
      entry entryRep saved anchor incoming incomingRep incomingPayload real distinct header rootId leftWing rightWing cached cachedErases
      cachedCurrent cachedAtRoot cachedHeader cachedIncoming cachedIncomingRep activeAnchor differentAnchors neutral
      incomingPreferences incomingTerminal incomingComponent incomingRepresented incomingColor incomingDecorated incomingErases incomingLogicalUnique
      incomingForest incomingForestRep incomingUnique incomingPayloads incomingConfig incomingAssembly attached incomingHeader incomingRootId
      incomingLeftWing incomingRightWing incomingCachedHeader
  have activeErasedWord := congrArg (fun source : Source Nat Cached => source.shape.leaves) erases
  simp only [Source.mapRecords_shape] at activeErasedWord
  have activeWord := activeLeaves.trans (activeErasedWord.trans (represented_leaf_word reference preferences component represented))
  rw [startDepth,activeBottom,Nat.sub_zero] at activeWord
  have incomingErasedWord := congrArg (fun source : Source Nat Cached => source.shape.leaves) incomingErases
  simp only [Source.mapRecords_shape] at incomingErasedWord
  have incomingWord := incomingLeaves.trans (incomingErasedWord.trans
    (represented_suffix_leaf_word reference incomingPreferences d ⟨by omega,by omega⟩ incomingComponent incomingRepresented))
  rw [PreparedLeafIntervals.suffix_range a b d ⟨by omega,by omega⟩] at incomingWord
  rw [show b+1-d = (PrimaryWings.exits incomingPrimary).length+2 by omega] at incomingWord
  have depthZero : d = 0 := minimum.trans startDepth
  have commonEmpty : common = [] := by
    cases common with
    | nil => rfl
    | cons => simp only [List.length_cons] at depthEq; omega
  obtain ⟨data,freshRoot,oldPacket,incomingPacket,computed,direction,dataOld,dataFresh,activeHeaderValue,incomingHeaderValue,
    activeStructural,dormantStructural,newHeaderValue,dormantHeaderValue,newVirtual,dormantVirtual⟩ :=
    PrimaryObservedRootHeadParameters.computed beforePrimary afterPrimary oldPrimary incomingPrimary side d depthZero
      (by simpa only [commonEmpty,List.nil_append] using beforeWord)
      (by simpa only [commonEmpty,List.nil_append] using afterWord)
      Prod.fst (highId,high) (incomingHighId,incomingHigh)
      (terminalId,(terminalLeaf d).rootRecord) (incomingTerminalId,(terminalLeaf d).rootRecord)
      taggedTail incomingTail activeWord incomingWord
      activeFinalForest incomingFinalForest
      (by simpa only [depthEq,activeColor] using activeFinalRep)
      (by simpa only [depthEq,incomingColorEq] using incomingFinalRep)
  simp only [depthEq,← activeColor,← incomingColorEq] at computed dataOld activeStructural dormantStructural newVirtual dormantVirtual
  have headersReady : VirtualPhysicalPackets.Ready data.newHeader ∧ VirtualPhysicalPackets.Ready data.dormantHeader := by
    constructor
    · rw [newHeaderValue]; exact VirtualPhysicalPackets.ready_encode _
    · rw [dormantHeaderValue]; exact VirtualPhysicalPackets.ready_encode _
  have noPrefix : ∀ side, ObservedHeadBlueprint.owned (some side) data.fresh.low = [] := by
    intro side
    rw [dataFresh]
    rfl
  have oldInterval : taggedTail.shape.leaves = List.range' (d+1) (b-d) := by
    have word := activeLeaves.trans (activeErasedWord.trans (represented_leaf_word reference preferences component represented))
    rw [← minimum] at word
    have rest := (List.range'_eq_cons_iff.mp word.symm).2.2
    simpa only [show b+1-d-1 = b-d by omega] using rest
  have incomingInterval := PreparedLeafIntervals.represented_incoming reference incomingPreferences ⟨by omega,by omega⟩
    incomingComponent incomingRepresented incomingDecorated incomingErases incomingTail incomingLeaves
  have boundary : color d = some data.direction := by
    rw [activeColor,direction,← depthEq]
    simp only [PackedPrimary.color,beforeWord,PrimaryWings.portAt_boundary,Option.map_some]
  have sentinel : incomingColor d = none := by
    rw [incomingColorEq]
    simp [PackedPrimary.color,PrimaryWings.portAt]
  let newPayload := Function.update payload (color d) (Function.update (payload (color d)) d incomingFinalConfig.tree)
  have newAttached : newPayload (some data.direction) d = incomingFinalConfig.tree := by
    rw [← boundary]
    simp [newPayload]
  let rawCurrent := returnedActive.mapRecords Prod.fst
  let enclosing := PacketPrefixTransfer.reidentify activePhysicalRoot saved
  have prefixLength : enclosing.length = saved.length := by simp only [enclosing,PacketPrefixTransfer.reidentify,List.length_map]
  have parentFlag : rawCurrent.ancestors.isEmpty = outside.isEmpty := by
    simpa only [rawCurrent,Cursor.mapRecords,List.isEmpty_map] using activeAncestors
  have rawIdentity : rawCurrent.focus.rootRecord.1 = activePhysicalRoot := by
    simpa only [rawCurrent,Cursor.mapRecords,Source.mapRecords_root] using activeIdentity
  have middleRawValid : WellFormed (middle.mapRecords Prod.fst) := by
    intro finger position present
    obtain ⟨cursor,reached⟩ := middleValid finger position present
    refine ⟨cursor.mapRecords Prod.fst,?_⟩
    simp only [Configuration.mapRecords,SourcePositions.locate_mapRecords,reached,Option.map_some]
  obtain ⟨selected,bare,rawFinal,lastReads,lastCost,planned,back,returned,result,ids,valid,finalReserved,rawValid,bound,bareEmpty⟩ :=
    ObservedCanonicalRootHeadExecution.execute (.inr activeAnchor) markerId d Prod.fst color incomingColor
      (highId,high) (incomingHighId,incomingHigh)
      (terminalId,(terminalLeaf d).rootRecord) (incomingTerminalId,(terminalLeaf d).rootRecord)
      taggedTail incomingTail (PreparedLeafIntervals.above incomingInterval) data boundary sentinel dataOld
      activeFinalForest incomingFinalForest activeFinalRep incomingFinalRep activeHeaderValue incomingHeaderValue
      headerKey newPayload incomingPayloads activeFinalConfig incomingFinalConfig activeFinalAssembly incomingFinalAssembly newAttached
      rawCurrent enclosing activeView (middle.mapRecords Prod.fst) (activeReturned.mapRecords Prod.fst)
      middleRawValid middlePhysical middleReserved
  have rawOrder :=
    ObservedCanonicalRootHeadExecution.inorder_of_run (.inr activeAnchor) markerId d Prod.fst color incomingColor
      (highId,high) (incomingHighId,incomingHigh)
      (terminalId,(terminalLeaf d).rootRecord) (incomingTerminalId,(terminalLeaf d).rootRecord)
      taggedTail incomingTail (PreparedLeafIntervals.above incomingInterval) data boundary sentinel dataOld
      activeFinalForest incomingFinalForest activeFinalRep incomingFinalRep activeHeaderValue incomingHeaderValue
      headerKey newPayload incomingPayloads activeFinalConfig incomingFinalConfig activeFinalAssembly incomingFinalAssembly newAttached
      rawCurrent enclosing activeView (middle.mapRecords Prod.fst) (activeReturned.mapRecords Prod.fst)
      middleRawValid middlePhysical middleReserved back
  rw [prefixLength,parentFlag] at back
  rw [rawIdentity] at returned
  have bareValid := EnclosingPacketOperation.output_focus_valid markerId enclosing activePhysicalRoot bare (returned.1 ▸ valid)
  have newExit : PackedPrimary.color 0 afterPrimary d = some (!data.direction) := by
    rw [direction,← depthEq]
    simp only [PackedPrimary.color,afterWord,PrimaryWings.portAt_boundary,Option.map_some]
  have incomingColors : ∀ key ∈ incomingTail.shape.leaves, incomingColor key = PackedPrimary.color 0 afterPrimary key := by
    intro key member
    have above : common.length < key := by rw [depthEq]; exact PreparedLeafIntervals.above incomingInterval key member
    simp only [incomingColorEq,← depthEq,PackedPrimary.color,afterWord,PrimaryWings.portAt_tail common _ _ key above]
  obtain ⟨newLeftPayload,newRightPayload,newForest,newConfig,newRep,newUnique,newAssembly,newTree,newPayloads⟩ :=
    CanonicalRootActiveHeadForest.reconstruct markerId Prod.fst color incomingColor (PackedPrimary.color 0 afterPrimary)
      (highId,high) (incomingHighId,incomingHigh) (incomingTerminalId,(terminalLeaf d).rootRecord)
      d data.direction taggedTail incomingTail data.fresh noPrefix activeStructural newExit incomingColors
      newPayload incomingPayloads headerKey data.newHeader (ObservedHeadParameters.packet data.dormantHeader)
      headersReady.1 newVirtual bare.focus bareValid result
  let newSource := annotate Prod.fst (PackedPrimary.color 0 afterPrimary) none
    (.fork (incomingHighId,incomingHigh)
      (.leaf d (incomingTerminalId,(terminalLeaf d).rootRecord)) incomingTail)
  let physicalPayload := ComputedComponentReconstruction.payload newLeftPayload newRightPayload (incomingPayloads none headerKey)
  have boundaryMember : d ∈ newSource.shape.leaves := by
    simp only [newSource,annotate_shape,Source.shape,RouterProjection.Router.leaves]
    exact List.mem_cons_self
  have boundaryPort : d ∈ RepairedPayloadLayouts.ports (packed (PackedPrimary.color 0 afterPrimary) (some (!data.direction)) newSource) := by
    rw [CanonicalRetainedPortFacts.packed_ports]
    exact List.mem_filter.mpr ⟨boundaryMember,by simp only [newExit,decide_true]⟩
  have boundaryGood := newPayloads (!data.direction) d boundaryPort
  have headAbsent : d ∉ RepairedPayloadLayouts.ports
      (none : ProjectionLocal.Projected Nat (Structural.HeadBoundary.Record (η × Cached) η (Option Bool))) := List.not_mem_nil
  have incomingAbsent := CanonicalRetainedPortFacts.absent Prod.fst incomingColor (some (!data.direction)) (some incomingHighId) incomingTail d
    (fun member => (Nat.lt_irrefl d) (PreparedLeafIntervals.above incomingInterval d member))
  have dormantResult := (CanonicalHeadSuccessor.boundary_iff newPayload incomingPayloads
    (fun _ => none)
    (ObservedCanonicalRootHeadExecution.projected Prod.fst color highId taggedTail)
    (ObservedCanonicalRootHeadExecution.projected Prod.fst incomingColor incomingHighId incomingTail)
    data.direction d data.fresh (ObservedHeadParameters.packet data.dormantHeader) (newPayload none headerKey)
    (physicalPayload (some (!data.direction)) d) headAbsent incomingAbsent).mp boundaryGood
  obtain ⟨dormantBody,dormantErases,dormantValid⟩ := CanonicalRealPayloadValidity.realized markerId
    (PackedPrimary.color 0 afterPrimary) newSource newForest newRep headerKey physicalPayload newConfig newAssembly
    bare.focus bareValid newTree.symm d boundaryMember (by rw [newExit]; exact Option.some_ne_none _)
  rw [newExit] at dormantErases
  have dormantBoundary : PackedPrimary.color (d+1) oldPrimary d = none := by
    simp [PackedPrimary.color,PrimaryWings.portAt]
  have oldColors : ∀ key ∈ taggedTail.shape.leaves, color key = PackedPrimary.color (d+1) oldPrimary key := by
    intro key member
    have above : common.length < key := by rw [depthEq]; exact PreparedLeafIntervals.above oldInterval key member
    simp only [activeColor,← depthEq,PackedPrimary.color,beforeWord,PrimaryWings.portAt_tail common _ _ key above]
  obtain ⟨dormantForest,dormantConfig,dormantRep,dormantUnique,dormantAssembly,dormantTree⟩ :=
    CanonicalDormantHeadForest.reconstruct markerId Prod.fst color (PackedPrimary.color (d+1) oldPrimary)
      (highId,high) (terminalId,(terminalLeaf d).rootRecord) d taggedTail data.fresh dormantStructural dormantBoundary oldColors
      newPayload headerKey data.dormantHeader headersReady.2 dormantVirtual dormantBody dormantValid (dormantErases.symm ▸ dormantResult)
  have cacheRepresented := PrimaryHeaderController.switched_minimum_represents header incomingHeader data.fresh
    (.fork (incomingHighId,incomingHigh) (.leaf d (incomingTerminalId,(terminalLeaf d).rootRecord)) incomingTail)
    (.fork (highId,high) (.leaf d (terminalId,(terminalLeaf d).rootRecord)) taggedTail)
    (PackedPrimary.color 0 afterPrimary) (PackedPrimary.color (d+1) oldPrimary) newForest dormantForest newRep dormantRep
    (congrArg Source.rootRecord activeStructural) (congrArg Source.rootRecord dormantStructural) headerKey physicalPayload
    (ComputedComponentReconstruction.payload (newPayload (some true)) (newPayload (some false)) (newPayload none headerKey))
  let inputs : RootPreparedPairHeaderController.Inputs η :=
    ⟨{header with rootId := highId},{incomingHeader with rootId := incomingHighId},
      BoundaryReadController.sentinelResult Prod.fst color (highId,high)
        (terminalId,(terminalLeaf d).rootRecord) d taggedTail,
      BoundaryReadController.sentinelResult Prod.fst incomingColor (incomingHighId,incomingHigh)
        (incomingTerminalId,(terminalLeaf d).rootRecord) d incomingTail⟩
  have middleCacheUnique : (middle.tree.inventory (fun record => record.1.1)).Nodup := by
    simpa only [Configuration.mapRecords,mapRecords_inventory,Function.comp_def] using middlePhysical.2.2
  obtain ⟨final,reads,cost,actual,finalErases,headFrame,costBound⟩ := RootPreparedHeadController.append_head_frame
    entry markerId saved.length (!outside.isEmpty) activeAnchor anchor d cached middle inputs _ _ data computed front rawFinal back rawOrder middleCacheUnique
  have actualReturned : MultiSourceSingleCursor.Represents (.inr activeAnchor)
      (EnclosingPacketOperation.output enclosing activePhysicalRoot bare) (final.mapRecords Prod.fst) := finalErases.symm ▸ returned
  obtain ⟨reached,reachedRep,reachedErases⟩ := MultiSourceSingleCursor.lift_represents Prod.fst (.inr activeAnchor)
    (EnclosingPacketOperation.output enclosing activePhysicalRoot bare) final actualReturned
  let finalSaved := PacketPrefixTransfer.reidentify bare.focus.rootRecord.1 enclosing
  have reachedView : reached.focus.mapRecords (fun record => record.1.2) =
      newConfig.tree.setRoot (finalSaved ++ newConfig.tree.rootRecord) := by
    have focusView := congrArg (fun current : Cursor β (ReentryCell Nat η) => current.focus.mapRecords Prod.snd) reachedErases
    simpa only [Cursor.mapRecords,MultiSourceRecordEquivalence.map_source_comp,Function.comp_def,
      EnclosingPacketOperation.output,PacketPrefixTransfer.output,PacketPrefixTransfer.attach,
      Source.mapRecords_setRoot,Source.mapRecords_root,newTree,finalSaved] using focusView
  obtain ⟨routed,dormantReached,routingPacket,routeRun,routeTree,dormantReachedRep,routeDescended,dormantReachedView,routeFingers,routeBound⟩ :=
    ObservedRootDormantRoute.execute (.inr activeAnchor) (.inr anchor) (fun record : CachedCell Nat η => record.1.2)
      markerId Prod.fst color incomingColor (PackedPrimary.color 0 afterPrimary)
      (highId,high) (incomingHighId,incomingHigh) (terminalId,(terminalLeaf d).rootRecord)
      (incomingTerminalId,(terminalLeaf d).rootRecord) d taggedTail incomingTail data dataOld noPrefix
      activeStructural newExit incomingColors newForest newRep headerKey physicalPayload newConfig newAssembly
      finalSaved reached reachedView final reachedRep
  have combined := RootPreparedHeadReturnController.append_route entry markerId saved.length (!outside.isEmpty) activeAnchor anchor d
    cached final routed inputs data dormantReached.focus.rootRecord actual routeRun
  have activeReachedRep : MultiSourceSingleCursor.Represents (.inr activeAnchor) reached routed :=
    ⟨routeTree.trans reachedRep.1,(routeFingers (.inr activeAnchor) (by simpa only [ne_eq,Sum.inr.injEq] using differentAnchors.symm)).trans reachedRep.2⟩
  have routeRawTree : (routed.mapRecords Prod.fst).tree = (final.mapRecords Prod.fst).tree := congrArg (Source.mapRecords Prod.fst) routeTree
  have dormantReachedExact : dormantReached.focus.mapRecords (fun record => record.1.2) =
      dormantConfig.tree.setRoot (some routingPacket :: none :: dormantConfig.tree.rootRecord) := by
    rw [dormantTree,dormantErases]
    exact dormantReachedView
  have routedUnique : (routed.tree.inventory (Prod.fst ∘ Prod.fst)).Nodup := by
    rw [← mapRecords_inventory Prod.fst Prod.fst routed.tree]
    change ((routed.mapRecords Prod.fst).tree.inventory Prod.fst).Nodup
    rw [routeRawTree,finalErases]
    exact valid.2.2
  have separateRoots : reached.focus.rootRecord.1.1 ≠ dormantReached.focus.rootRecord.1.1 :=
    SourcePositions.distinct_labels_of_proper_descent (Prod.fst ∘ Prod.fst) reached dormantReached (ObservedRootDormantRoute.path data)
      (HeadBoundaryRoute.path_nonempty _ _ _ _) routeDescended (activeReachedRep.1 ▸ routedUnique)
  let headers := PrimaryHeaderController.switchedMinimum inputs.active inputs.incoming data.fresh
  obtain ⟨cachedFinal,cacheReads,cachedActive,cachedDormant,cacheRun,cacheErases,cachedActiveRep,cachedDormantRep,
    cachedActiveRaw,cachedDormantRaw,activeStored,dormantStored,cacheValid⟩ := PrimaryHeaderPairRefresh.execute Prod.fst
      (.inr activeAnchor) (.inr anchor) headers.1 headers.2 routed reached dormantReached activeReachedRep dormantReachedRep
      (routeRun.wellFormed (WellFormed.of_mapRecords Prod.fst (finalErases.symm ▸ rawValid))) routedUnique separateRoots
  have refreshFrame := HeadCacheFrame.pair_refresh_frame_of_run Prod.fst
    (.inr activeAnchor) (.inr anchor) headers.1 headers.2 routed reached dormantReached
    activeReachedRep dormantReachedRep
    (routeRun.wellFormed (WellFormed.of_mapRecords Prod.fst (finalErases.symm ▸ rawValid))) routedUnique cacheRun
  have routedFrame : HeadCacheFrame.MetadataFrame Prod.fst [] middle.tree routed.tree := routeTree.symm ▸ headFrame
  let changed := [activePhysicalRoot,reachedIncoming.focus.rootRecord.1.1] ++
    [reached.focus.rootRecord.1.1,dormantReached.focus.rootRecord.1.1]
  have frame : HeadCacheFrame.MetadataFrame Prod.fst changed cached.tree cachedFinal.tree := by
    simpa only [List.append_nil,changed] using (prepFrame.trans routedFrame).trans refreshFrame
  have totalOrder : (cachedFinal.mapRecords Prod.fst).tree.inorderLabels Prod.fst = global.tree.inorderLabels Prod.fst := by
    rw [cacheErases,routeRawTree,finalErases]
    exact rawOrder.trans prepOrder
  have complete := RootPreparedHeadCacheController.append_refresh entry markerId saved.length (!outside.isEmpty) activeAnchor anchor d
    cached routed cachedFinal inputs data dormantReached.focus.rootRecord combined cacheRun
  have cachedPacketView : cachedDormant.focus.mapRecords (fun record => record.1.2) =
      dormantConfig.tree.setRoot (some routingPacket :: none :: dormantConfig.tree.rootRecord) := by
    have packetEq := congrArg (fun current : Cursor β (ReentryCell Nat η) => current.focus.mapRecords Prod.snd) cachedDormantRaw
    have same : cachedDormant.focus.mapRecords (fun record => record.1.2) = dormantReached.focus.mapRecords (fun record => record.1.2) := by
      simpa only [Cursor.mapRecords,MultiSourceRecordEquivalence.map_source_comp,Function.comp_def] using packetEq
    exact same.trans dormantReachedExact
  have cachedDescended : SourcePositions.descend cachedActive (ObservedRootDormantRoute.path data) = some cachedDormant := by
    have activeAddress := congrArg SourcePositions.address cachedActiveRaw
    have dormantAddress := congrArg SourcePositions.address cachedDormantRaw
    simp only [SourcePositions.address_mapRecords] at activeAddress dormantAddress
    have addressEq : SourcePositions.address cachedDormant = SourcePositions.address cachedActive ++ ObservedRootDormantRoute.path data := by
      rw [activeAddress,dormantAddress]
      exact SourcePositions.descend_address reached dormantReached _ routeDescended
    have located := SourcePositions.locate_cursor cachedDormant
    rw [← cachedDormantRep.1,cachedActiveRep.1,addressEq] at located
    change SourcePositions.descend ⟨cachedActive.tree,[]⟩ (SourcePositions.address cachedActive ++ ObservedRootDormantRoute.path data) = _ at located
    rw [SourcePositions.descend_append,show SourcePositions.descend ⟨cachedActive.tree,[]⟩ (SourcePositions.address cachedActive) = some cachedActive from SourcePositions.locate_cursor cachedActive] at located
    exact located
  refine ⟨right,incomingRight,high,incomingHigh,highId,terminalId,incomingHighId,incomingTerminalId,
    taggedTail,incomingTail,incomingFinalConfig,data,activePhysicalRoot,bare,cachedFinal,cachedActive,cachedDormant,routingPacket,
    (reads++[(.inr anchor,dormantReached.focus.rootRecord)])++cacheReads,cost+((ObservedRootDormantRoute.path data).length+2)+4,newLeftPayload,newRightPayload,newForest,newConfig,
    dormantBody,dormantForest,dormantConfig,changed,
    highKey,incomingHighKey,rightClean,rightMarked,incomingClean,incomingMarked,
    tailEq,incomingTailEq,complete,cachedActiveRep,cachedActiveRaw.trans reachedErases,direction,activeStructural,dormantStructural,headersReady.1,headersReady.2,newVirtual,dormantVirtual,
    cacheErases.symm ▸ (routeRawTree.symm ▸ (finalErases.symm ▸ valid)),cacheErases.symm ▸ (routeRawTree.symm ▸ (finalErases.symm ▸ finalReserved)),?_,
    cacheValid,frame,rfl,totalOrder,by omega,result,activeSplit,incomingSplit,activeIds,incomingIds,newRep,newUnique,newAssembly,newTree,
    dormantRep,dormantUnique,dormantAssembly,dormantTree,dormantTree.trans dormantErases,dormantValid,cachedDormantRep,cachedDescended,cachedPacketView,activeStored,dormantStored,
    cacheRepresented.1,cacheRepresented.2,bareEmpty.trans parentFlag,activeLeaves,incomingLeaves,newPayloads⟩
  · rw [cacheErases,routeRawTree,finalErases,ids,middleIds]

end ChaCha.Paper20261030.SecondaryDecomposition.RootPreparedHeadExecution
