import TangoSquared.Paper20261030.HeadCacheFrameControllers
import TangoSquared.Paper20261030.HeadCacheFrameHeadOrderCanonical
import TangoSquared.Paper20261030.PreparedPairHeaderExecution
import TangoSquared.Paper20261030.PreparedHeadController
import TangoSquared.Paper20261030.PrimaryObservedHeadParameters
import TangoSquared.Paper20261030.ObservedCanonicalHeadExecution
import TangoSquared.Paper20261030.ComputedVirtualHeaderReadiness
import TangoSquared.Paper20261030.CanonicalActiveHeadForest
import TangoSquared.Paper20261030.EnclosingOutputFocusValidity
import TangoSquared.Paper20261030.CanonicalDormantHeadForest
import TangoSquared.Paper20261030.CanonicalRealPayloadValidity
import TangoSquared.Paper20261030.PreparedHeadReturnController
import TangoSquared.Paper20261030.PreparedHeadCacheController
import TangoSquared.Paper20261030.SwitchedHeaderRepresentation

set_option autoImplicit false

/-! Interior preparation and physical head exchange in one shared-tree
program, starting from the two initial component representations. The
preserved leaf words and actual primary exit decomposition discharge all
parameter-calculation and finite-layout premises. The program also reaches
the dormant root and installs both switched caches. Balanced restoration
is a later phase. -/

namespace TangoSquared.Paper20261030.SecondaryDecomposition.PreparedHeadExecution

open ColoredStorage SourcePointer Structural PhysicalForestMetadata Auxiliary AuxiliaryComponent BoundaryObservations PathDecomposition
open LocalComponentForestCompiler LocalComponentCompiler ForestConnector.ThreeColors MultiSourceProgram
open PreparedExposureExecution (Logical Datum)
open ObservedPreparedExposure

variable {α β η G : Type*} [DecidableEq α] [DecidableEq η] [DecidableEq G]

local instance preparedHeadExecutionColorOrder : LinearOrder (Option Bool) := inferInstanceAs (LinearOrder (WithBot Bool))

set_option backward.isDefEq.respectTransparency false in
theorem execute (markerId : Nat) {a b : Nat} (reference : DepthTree a b) (preferences : DepthSplit → Bool)
    (d : Nat) (terminal : (Secondary.decodeDepth reference preferences).terminal = d) (lower : a < d) (upper : d < b)
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
    ∃ (left right incomingRight : AuxiliaryComponent Nat Nat (Tagged Payload)) (low high incomingHigh : Cached),
      ∃ lowId highId terminalId incomingHighId incomingTerminalId,
      ∃ taggedHead taggedTail incomingTail : Source Nat (η × Cached),
      ∃ (incomingFinalConfig : MultiSourceProgram.Configuration (Option Bool) β (List (Option (Datum Nat η)))),
      ∃ (data : PreparedHeadController.Data η) (activePhysicalRoot : Nat),
      ∃ (bare : Cursor β (ReentryCell Nat η)) (final : MultiSourceProgram.Configuration (Sum (Option Bool) G) β (CachedCell Nat η)),
      ∃ (reached dormantReached : Cursor β (CachedCell Nat η)), ∃ routingPacket reads cost,
      ∃ newLeftPayload newRightPayload newForest newConfig,
      ∃ (dormantBody : Source β (ReentryCell Nat η)), ∃ dormantForest dormantConfig, ∃ changed : List Nat,
      low.2.1 = d-1 ∧ high.2.1 = d ∧ incomingHigh.2.1 = d ∧
      Clean left.core ∧ MarkedPorts left ∧ Clean right.core ∧ MarkedPorts right ∧
      Clean incomingRight.core ∧ MarkedPorts incomingRight ∧
      taggedHead.mapRecords Prod.snd = left.tree ∧ taggedTail.mapRecords Prod.snd = right.tree ∧
      incomingTail.mapRecords Prod.snd = incomingRight.tree ∧
      MultiSourceProgram.Run
        (PreparedHeadCacheController.program entry markerId saved.length (!outside.isEmpty) activeAnchor anchor d)
        (.first (.first (.first (.first (.first (.first .start)))))) cached
        (.second (some (⟨{header with rootId := lowId},{incomingHeader with rootId := incomingHighId},
          BoundaryReadController.activeResult Prod.fst color (lowId,low) (highId,high)
            (terminalId,(terminalLeaf d).rootRecord) d taggedHead taggedTail,
          BoundaryReadController.sentinelResult Prod.fst incomingColor (incomingHighId,incomingHigh)
            (incomingTerminalId,(terminalLeaf d).rootRecord) d incomingTail⟩,data))
          (.second () (some .done))) final reads cost ∧
      MultiSourceSingleCursor.Represents (.inr activeAnchor) reached final ∧
      reached.mapRecords Prod.fst = EnclosingPacketOperation.output
        (PacketPrefixTransfer.reidentify activePhysicalRoot saved) activePhysicalRoot bare ∧
      data.direction = side ∧
      Structural.HeadBoundary.activeTree data.fresh d
        (annotate Prod.fst color (some lowId) taggedHead)
        (annotate Prod.fst incomingColor (some incomingHighId) incomingTail) =
        annotate Prod.fst (PackedPrimary.color 0 afterPrimary) none
          (.fork (lowId,low) taggedHead (.fork (incomingHighId,incomingHigh)
            (.leaf d (incomingTerminalId,(terminalLeaf d).rootRecord)) incomingTail)) ∧
      Structural.HeadBoundary.dormantTree data.fresh d
        (annotate Prod.fst color (some highId) taggedTail) =
        annotate Prod.fst (PackedPrimary.color (d+1) oldPrimary) none
          (.fork (highId,high) (.leaf d (terminalId,(terminalLeaf d).rootRecord)) taggedTail) ∧
      VirtualPhysicalPackets.Ready data.newHeader ∧ VirtualPhysicalPackets.Ready data.dormantHeader ∧
      VirtualPhysicalPackets.decode data.newHeader =
        (packed (PackedPrimary.color 0 afterPrimary) none (annotate Prod.fst (PackedPrimary.color 0 afterPrimary) none
          (.fork (lowId,low) taggedHead (.fork (incomingHighId,incomingHigh)
            (.leaf d (incomingTerminalId,(terminalLeaf d).rootRecord)) incomingTail)))).map (fun source => ⟨source,[]⟩) ∧
      VirtualPhysicalPackets.decode data.dormantHeader =
        (packed (PackedPrimary.color (d+1) oldPrimary) none (annotate Prod.fst (PackedPrimary.color (d+1) oldPrimary) none
          (.fork (highId,high) (.leaf d (terminalId,(terminalLeaf d).rootRecord)) taggedTail))).map (fun source => ⟨source,[]⟩) ∧
      CanonicalComponentUniqueness.Valid markerId (final.mapRecords Prod.fst).tree ∧
      markerId ∉ (final.mapRecords Prod.fst).tree.inventory Prod.fst ∧
      (final.mapRecords Prod.fst).tree.inventory Prod.fst = global.tree.inventory Prod.fst ∧
      MultiSourceProgram.WellFormed final ∧
      HeadCacheFrame.MetadataFrame Prod.fst changed cached.tree final.tree ∧ changed.length = 4 ∧
      (final.mapRecords Prod.fst).tree.inorderLabels Prod.fst = global.tree.inorderLabels Prod.fst ∧
      cost ≤ 4*(474240*(120330*Nat.clog 2 ((LocalReferences.depthReference reference).height+1)+6)+137280)+1715 ∧
      let newPayload := Function.update payload (color d) (Function.update (payload (color d)) d incomingFinalConfig.tree)
      CanonicalHeadSuccessor.Result newPayload incomingPayloads
        (ObservedCanonicalHeadExecution.projected Prod.fst color lowId taggedHead)
        (ObservedCanonicalHeadExecution.projected Prod.fst color highId taggedTail)
        (ObservedCanonicalHeadExecution.projected Prod.fst incomingColor incomingHighId incomingTail)
        data.direction d data.fresh (ObservedHeadParameters.packet data.newHeader) (ObservedHeadParameters.packet data.dormantHeader)
        (newPayload none headerKey) (incomingPayloads none headerKey) (some (bare.focus.mapRecords Prod.snd)) ∧
      PreparedSplitWitnesses.Active component d left right low high ∧
      PreparedSplitWitnesses.Sentinel incomingComponent d incomingRight incomingHigh ∧
      (Source.fork (lowId,low) taggedHead (.fork (highId,high)
          (.leaf d (terminalId,(terminalLeaf d).rootRecord)) taggedTail)).inventory Prod.fst = decorated.inventory Prod.fst ∧
      (Source.fork (incomingHighId,incomingHigh) (.leaf d (incomingTerminalId,(terminalLeaf d).rootRecord)) incomingTail).inventory Prod.fst =
        incomingDecorated.inventory Prod.fst ∧
      let newSource := annotate Prod.fst (PackedPrimary.color 0 afterPrimary) none
        (.fork (lowId,low) taggedHead (.fork (incomingHighId,incomingHigh)
          (.leaf d (incomingTerminalId,(terminalLeaf d).rootRecord)) incomingTail))
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
      SourcePositions.descend reached (ObservedDormantRoute.path data) = some dormantReached ∧
      dormantReached.focus.mapRecords (fun record => record.1.2) =
        dormantConfig.tree.setRoot (some routingPacket :: none :: dormantConfig.tree.rootRecord) ∧
      reached.focus.rootRecord.2 = some (PrimaryHeaderController.switched header incomingHeader data.fresh).1 ∧
      dormantReached.focus.rootRecord.2 = some (PrimaryHeaderController.switched header incomingHeader data.fresh).2 ∧
      PrimaryHeaderController.Represents (PrimaryHeaderController.switched header incomingHeader data.fresh).1 incomingHeader.bottom header.start
        (.fork (lowId,low) taggedHead (.fork (incomingHighId,incomingHigh) (.leaf d (incomingTerminalId,(terminalLeaf d).rootRecord)) incomingTail))
        newForest headerKey (ComputedComponentReconstruction.payload newLeftPayload newRightPayload (incomingPayloads none headerKey)) ∧
      PrimaryHeaderController.Represents (PrimaryHeaderController.switched header incomingHeader data.fresh).2 header.bottom incomingHeader.start
        (.fork (highId,high) (.leaf d (terminalId,(terminalLeaf d).rootRecord)) taggedTail)
        dormantForest headerKey (ComputedComponentReconstruction.payload (newPayload (some true)) (newPayload (some false)) (newPayload none headerKey)) ∧
      bare.ancestors.isEmpty = outside.isEmpty ∧
      taggedHead.shape.leaves ++ d::taggedTail.shape.leaves = decorated.shape.leaves ∧
      d::incomingTail.shape.leaves = incomingDecorated.shape.leaves ∧
      ∀ side key, key ∈ RepairedPayloadLayouts.ports (packed (PackedPrimary.color 0 afterPrimary) (some side) newSource) →
        CanonicalHeadSuccessor.Payload newPayload incomingPayloads
          (ObservedCanonicalHeadExecution.projected Prod.fst color lowId taggedHead)
          (ObservedCanonicalHeadExecution.projected Prod.fst color highId taggedTail)
          (ObservedCanonicalHeadExecution.projected Prod.fst incomingColor incomingHighId incomingTail)
          data.direction d data.fresh (ObservedHeadParameters.packet data.dormantHeader) (newPayload none headerKey)
          side key (ComputedComponentReconstruction.payload newLeftPayload newRightPayload (incomingPayloads none headerKey) (some side) key) := by
  obtain ⟨left,right,incomingRight,low,high,incomingHigh,lowId,highId,terminalId,incomingHighId,incomingTerminalId,
    taggedHead,taggedTail,incomingTail,activeFinalForest,incomingFinalForest,activeFinalConfig,incomingFinalConfig,
    middle,returnedActive,reachedIncoming,activePhysicalRoot,incomingAttachment,firstReads,firstCost,
    lowKey,highKey,incomingHighKey,leftClean,leftMarked,rightClean,rightMarked,incomingClean,incomingMarked,
    headEq,tailEq,incomingTailEq,front,activeFinalRep,activeFinalUnique,incomingFinalRep,incomingFinalUnique,
    incomingFinalAssembly,incomingPresence,activeReturned,activeView,activeIdentity,activeCache,
    incomingReturned,incomingCache,incomingAttachmentLength,incomingView,incomingPayloadAt,middleValid,middlePhysical,
    middleReserved,middleIds,prepFrame,prepOrder,frontBound,activeFinalAssembly,activePresence,activeLeaves,incomingLeaves,activeAncestors,activeSplit,incomingSplit,activeIds,incomingIds⟩ :=
    PreparedPairHeaderExecution.execute markerId reference preferences d terminal lower upper component represented color decorated erases logicalUnique
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
  obtain ⟨data,oldPacket,incomingPacket,computed,direction,dataOld,activeHeaderValue,incomingHeaderValue,
    activeStructural,dormantStructural,newHeaderValue,dormantHeaderValue,newVirtual,dormantVirtual⟩ :=
    PrimaryObservedHeadParameters.computed beforePrimary afterPrimary oldPrimary incomingPrimary common side beforeWord afterWord
      Prod.fst (lowId,low) (highId,high) (incomingHighId,incomingHigh)
      (terminalId,(terminalLeaf d).rootRecord) (incomingTerminalId,(terminalLeaf d).rootRecord)
      taggedHead taggedTail incomingTail
      (by simpa only [depthEq] using activeWord) (by simpa only [depthEq] using incomingWord)
      activeFinalForest incomingFinalForest
      (by simpa only [depthEq,activeColor] using activeFinalRep)
      (by simpa only [depthEq,incomingColorEq] using incomingFinalRep)
  simp only [depthEq,← activeColor,← incomingColorEq] at computed dataOld activeStructural dormantStructural newVirtual dormantVirtual
  have headersReady := ObservedHeadParameters.output_ready Prod.fst _ _ _ _ data computed
  have intervals := PreparedLeafIntervals.represented_active reference preferences component represented decorated erases taggedHead taggedTail activeLeaves
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
    ObservedCanonicalHeadExecution.execute (.inr activeAnchor) markerId d Prod.fst color incomingColor
      (lowId,low) (highId,high) (incomingHighId,incomingHigh)
      (terminalId,(terminalLeaf d).rootRecord) (incomingTerminalId,(terminalLeaf d).rootRecord)
      taggedHead taggedTail incomingTail (PreparedLeafIntervals.below intervals.1)
      (PreparedLeafIntervals.above incomingInterval) data boundary sentinel dataOld
      activeFinalForest incomingFinalForest activeFinalRep incomingFinalRep activeHeaderValue incomingHeaderValue
      headerKey newPayload incomingPayloads activeFinalConfig incomingFinalConfig activeFinalAssembly incomingFinalAssembly newAttached
      rawCurrent enclosing activeView (middle.mapRecords Prod.fst) (activeReturned.mapRecords Prod.fst)
      middleRawValid middlePhysical middleReserved
  have rawOrder :=
    ObservedCanonicalHeadExecution.inorder_of_run (.inr activeAnchor) markerId d Prod.fst color incomingColor
      (lowId,low) (highId,high) (incomingHighId,incomingHigh)
      (terminalId,(terminalLeaf d).rootRecord) (incomingTerminalId,(terminalLeaf d).rootRecord)
      taggedHead taggedTail incomingTail (PreparedLeafIntervals.below intervals.1)
      (PreparedLeafIntervals.above incomingInterval) data boundary sentinel dataOld
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
  have prefixColors : ∀ key ∈ taggedHead.shape.leaves, color key = PackedPrimary.color 0 afterPrimary key := by
    intro key member
    have below : key < common.length := by rw [depthEq]; exact PreparedLeafIntervals.below intervals.1 key member
    simp only [activeColor,PackedPrimary.color,beforeWord,afterWord,PrimaryWings.portAt_prefix common _ key below]
  have incomingColors : ∀ key ∈ incomingTail.shape.leaves, incomingColor key = PackedPrimary.color 0 afterPrimary key := by
    intro key member
    have above : common.length < key := by rw [depthEq]; exact PreparedLeafIntervals.above incomingInterval key member
    simp only [incomingColorEq,← depthEq,PackedPrimary.color,afterWord,PrimaryWings.portAt_tail common _ _ key above]
  obtain ⟨newLeftPayload,newRightPayload,newForest,newConfig,newRep,newUnique,newAssembly,newTree,newPayloads⟩ :=
    CanonicalActiveHeadForest.reconstruct markerId Prod.fst color incomingColor (PackedPrimary.color 0 afterPrimary)
      (lowId,low) (highId,high) (incomingHighId,incomingHigh) (incomingTerminalId,(terminalLeaf d).rootRecord)
      d data.direction taggedHead taggedTail incomingTail data.fresh activeStructural newExit prefixColors incomingColors
      newPayload incomingPayloads headerKey data.newHeader (ObservedHeadParameters.packet data.dormantHeader)
      headersReady.1 newVirtual bare.focus bareValid result
  let newSource := annotate Prod.fst (PackedPrimary.color 0 afterPrimary) none
    (.fork (lowId,low) taggedHead (.fork (incomingHighId,incomingHigh)
      (.leaf d (incomingTerminalId,(terminalLeaf d).rootRecord)) incomingTail))
  let physicalPayload := ComputedComponentReconstruction.payload newLeftPayload newRightPayload (incomingPayloads none headerKey)
  have boundaryMember : d ∈ newSource.shape.leaves := by
    simp only [newSource,annotate_shape,Source.shape,RouterProjection.Router.leaves]
    exact List.mem_append_right _ (List.mem_cons_self)
  have boundaryPort : d ∈ RepairedPayloadLayouts.ports (packed (PackedPrimary.color 0 afterPrimary) (some (!data.direction)) newSource) := by
    rw [CanonicalRetainedPortFacts.packed_ports]
    exact List.mem_filter.mpr ⟨boundaryMember,by simp only [newExit,decide_true]⟩
  have boundaryGood := newPayloads (!data.direction) d boundaryPort
  have headAbsent := CanonicalRetainedPortFacts.absent Prod.fst color (some (!data.direction)) (some lowId) taggedHead d
    (fun member => (Nat.lt_irrefl d) (PreparedLeafIntervals.below intervals.1 d member))
  have incomingAbsent := CanonicalRetainedPortFacts.absent Prod.fst incomingColor (some (!data.direction)) (some incomingHighId) incomingTail d
    (fun member => (Nat.lt_irrefl d) (PreparedLeafIntervals.above incomingInterval d member))
  have dormantResult := (CanonicalHeadSuccessor.boundary_iff newPayload incomingPayloads
    (ObservedCanonicalHeadExecution.projected Prod.fst color lowId taggedHead)
    (ObservedCanonicalHeadExecution.projected Prod.fst color highId taggedTail)
    (ObservedCanonicalHeadExecution.projected Prod.fst incomingColor incomingHighId incomingTail)
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
    have above : common.length < key := by rw [depthEq]; exact PreparedLeafIntervals.above intervals.2 key member
    simp only [activeColor,← depthEq,PackedPrimary.color,beforeWord,PrimaryWings.portAt_tail common _ _ key above]
  obtain ⟨dormantForest,dormantConfig,dormantRep,dormantUnique,dormantAssembly,dormantTree⟩ :=
    CanonicalDormantHeadForest.reconstruct markerId Prod.fst color (PackedPrimary.color (d+1) oldPrimary)
      (highId,high) (terminalId,(terminalLeaf d).rootRecord) d taggedTail data.fresh dormantStructural dormantBoundary oldColors
      newPayload headerKey data.dormantHeader headersReady.2 dormantVirtual dormantBody dormantValid (dormantErases.symm ▸ dormantResult)
  have cacheRepresented := PrimaryHeaderController.switched_represents header incomingHeader data.fresh
    (.fork (lowId,low) taggedHead (.fork (incomingHighId,incomingHigh) (.leaf d (incomingTerminalId,(terminalLeaf d).rootRecord)) incomingTail))
    (.fork (highId,high) (.leaf d (terminalId,(terminalLeaf d).rootRecord)) taggedTail)
    (PackedPrimary.color 0 afterPrimary) (PackedPrimary.color (d+1) oldPrimary) newForest dormantForest newRep dormantRep
    (congrArg Source.rootRecord activeStructural) (congrArg Source.rootRecord dormantStructural) headerKey physicalPayload
    (ComputedComponentReconstruction.payload (newPayload (some true)) (newPayload (some false)) (newPayload none headerKey))
  let inputs : PreparedPairHeaderController.Inputs η :=
    ⟨{header with rootId := lowId},{incomingHeader with rootId := incomingHighId},
      BoundaryReadController.activeResult Prod.fst color (lowId,low) (highId,high)
        (terminalId,(terminalLeaf d).rootRecord) d taggedHead taggedTail,
      BoundaryReadController.sentinelResult Prod.fst incomingColor (incomingHighId,incomingHigh)
        (incomingTerminalId,(terminalLeaf d).rootRecord) d incomingTail⟩
  have middleCacheUnique : (middle.tree.inventory (fun record => record.1.1)).Nodup := by
    simpa only [Configuration.mapRecords,mapRecords_inventory,Function.comp_def] using middlePhysical.2.2
  obtain ⟨final,reads,cost,actual,finalErases,headFrame,costBound⟩ := PreparedHeadController.append_head_frame
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
    ObservedDormantRoute.execute (.inr activeAnchor) (.inr anchor) (fun record : CachedCell Nat η => record.1.2)
      markerId Prod.fst color incomingColor (PackedPrimary.color 0 afterPrimary)
      (lowId,low) (highId,high) (incomingHighId,incomingHigh) (terminalId,(terminalLeaf d).rootRecord)
      (incomingTerminalId,(terminalLeaf d).rootRecord) d taggedHead taggedTail incomingTail data dataOld
      activeStructural newExit prefixColors incomingColors newForest newRep headerKey physicalPayload newConfig newAssembly
      finalSaved reached reachedView final reachedRep
  have combined := PreparedHeadReturnController.append_route entry markerId saved.length (!outside.isEmpty) activeAnchor anchor d
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
    SourcePositions.distinct_labels_of_proper_descent (Prod.fst ∘ Prod.fst) reached dormantReached (ObservedDormantRoute.path data)
      (HeadBoundaryRoute.path_nonempty _ _ _ _) routeDescended (activeReachedRep.1 ▸ routedUnique)
  let headers := PrimaryHeaderController.switched inputs.active inputs.incoming data.fresh
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
  have complete := PreparedHeadCacheController.append_refresh entry markerId saved.length (!outside.isEmpty) activeAnchor anchor d
    cached routed cachedFinal inputs data dormantReached.focus.rootRecord combined cacheRun
  have cachedPacketView : cachedDormant.focus.mapRecords (fun record => record.1.2) =
      dormantConfig.tree.setRoot (some routingPacket :: none :: dormantConfig.tree.rootRecord) := by
    have packetEq := congrArg (fun current : Cursor β (ReentryCell Nat η) => current.focus.mapRecords Prod.snd) cachedDormantRaw
    have same : cachedDormant.focus.mapRecords (fun record => record.1.2) = dormantReached.focus.mapRecords (fun record => record.1.2) := by
      simpa only [Cursor.mapRecords,MultiSourceRecordEquivalence.map_source_comp,Function.comp_def] using packetEq
    exact same.trans dormantReachedExact
  have cachedDescended : SourcePositions.descend cachedActive (ObservedDormantRoute.path data) = some cachedDormant := by
    have activeAddress := congrArg SourcePositions.address cachedActiveRaw
    have dormantAddress := congrArg SourcePositions.address cachedDormantRaw
    simp only [SourcePositions.address_mapRecords] at activeAddress dormantAddress
    have addressEq : SourcePositions.address cachedDormant = SourcePositions.address cachedActive ++ ObservedDormantRoute.path data := by
      rw [activeAddress,dormantAddress]
      exact SourcePositions.descend_address reached dormantReached _ routeDescended
    have located := SourcePositions.locate_cursor cachedDormant
    rw [← cachedDormantRep.1,cachedActiveRep.1,addressEq] at located
    change SourcePositions.descend ⟨cachedActive.tree,[]⟩ (SourcePositions.address cachedActive ++ ObservedDormantRoute.path data) = _ at located
    rw [SourcePositions.descend_append,show SourcePositions.descend ⟨cachedActive.tree,[]⟩ (SourcePositions.address cachedActive) = some cachedActive from SourcePositions.locate_cursor cachedActive] at located
    exact located
  refine ⟨left,right,incomingRight,low,high,incomingHigh,lowId,highId,terminalId,incomingHighId,incomingTerminalId,
    taggedHead,taggedTail,incomingTail,incomingFinalConfig,data,activePhysicalRoot,bare,cachedFinal,cachedActive,cachedDormant,routingPacket,
    (reads++[(.inr anchor,dormantReached.focus.rootRecord)])++cacheReads,cost+((ObservedDormantRoute.path data).length+2)+4,newLeftPayload,newRightPayload,newForest,newConfig,
    dormantBody,dormantForest,dormantConfig,changed,
    lowKey,highKey,incomingHighKey,leftClean,leftMarked,rightClean,rightMarked,incomingClean,incomingMarked,
    headEq,tailEq,incomingTailEq,complete,cachedActiveRep,cachedActiveRaw.trans reachedErases,direction,activeStructural,dormantStructural,headersReady.1,headersReady.2,newVirtual,dormantVirtual,
    cacheErases.symm ▸ (routeRawTree.symm ▸ (finalErases.symm ▸ valid)),cacheErases.symm ▸ (routeRawTree.symm ▸ (finalErases.symm ▸ finalReserved)),?_,
    cacheValid,frame,rfl,totalOrder,by omega,result,activeSplit,incomingSplit,activeIds,incomingIds,newRep,newUnique,newAssembly,newTree,
    dormantRep,dormantUnique,dormantAssembly,dormantTree,dormantTree.trans dormantErases,dormantValid,cachedDormantRep,cachedDescended,cachedPacketView,activeStored,dormantStored,
    cacheRepresented.1,cacheRepresented.2,bareEmpty.trans parentFlag,activeLeaves,incomingLeaves,newPayloads⟩
  · rw [cacheErases,routeRawTree,finalErases,ids,middleIds]

end TangoSquared.Paper20261030.SecondaryDecomposition.PreparedHeadExecution
