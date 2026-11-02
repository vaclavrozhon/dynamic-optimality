import ChaCha.Paper20261030.RootPreparedPairExecution
import ChaCha.Paper20261030.RootPreparedPairHeaderController

set_option autoImplicit false

/-! Preparing both components and reading their two stored virtual
headers in one shared-tree program. All four boundary records and both
virtual cursors in the final state come from executed reads. The two
canonical component witnesses and their root caches are preserved. -/

namespace ChaCha.Paper20261030.SecondaryDecomposition.RootPreparedPairHeaderExecution

open ColoredStorage SourcePointer Structural PhysicalForestMetadata Auxiliary AuxiliaryComponent BoundaryObservations PathDecomposition
open LocalComponentForestCompiler LocalComponentCompiler ForestConnector.ThreeColors MultiSourceProgram
open PreparedExposureExecution (Logical Datum)
open ObservedPreparedExposure

variable {β ι η G : Type*} [DecidableEq ι] [DecidableEq η] [DecidableEq G]

local instance rootPreparedPairHeaderExecutionColorOrder : LinearOrder (Option Bool) := inferInstanceAs (LinearOrder (WithBot Bool))

theorem execute (markerId : ι) {a b : Nat} (reference : DepthTree a b) (preferences : DepthSplit → Bool)
    (d : Nat) (terminal : (Secondary.decodeDepth reference preferences).terminal = d) (minimum : d = a) (upper : d < b)
    (component : AuxiliaryComponent Nat Nat (Tagged Payload))
    (represented : Represents followsRight (source reference preferences) component)
    (color : Nat → Option Bool) (decorated : Source Nat (η × Cached))
    (erases : decorated.mapRecords Prod.snd = closed component) (logicalUnique : (decorated.inventory Prod.fst).Nodup)
    (forest : TaggedForest (Option Bool) Nat (Logical η) ι)
    (forestRep : ProjectionForest.Represents color ⟨annotate Prod.fst color none decorated,[]⟩ (erase forest))
    (physicalUnique : Unique forest) (headerKey : Nat)
    (payload : Option Bool → Nat → Source β (List (Option (Datum ι η))))
    (config : MultiSourceProgram.Configuration (Option Bool) β (List (Option (Datum ι η))))
    (assembled : ForestConnector.assemble (representation none wingOrientation headerKey payload forest)
      (layout (representation none wingOrientation headerKey payload forest)) = some config)
    (tree : Source β (ReentryCell ι η))
    (treeErases : tree.mapRecords Prod.snd = config.tree)
    (outside : List (Frame β (ReentryCell ι η)))
    (global : MultiSourceProgram.Configuration (Sum (Option Bool) G) β (ReentryCell ι η))
    (wellFormed : MultiSourceProgram.WellFormed global)
    (physical : CanonicalComponentUniqueness.Valid markerId global.tree)
    (reserved : markerId ∉ global.tree.inventory Prod.fst)
    (entry : Sum (Option Bool) G)
    (entryRep : MultiSourceSingleCursor.Represents entry ⟨tree,outside⟩ global)
    (saved : List (Option (Datum ι η)))
    (anchor : G) (incoming : Cursor β (ReentryCell ι η))
    (incomingRep : MultiSourceSingleCursor.Represents (.inr anchor) incoming global)
    (incomingPayload : CanonicalRetainedPayloadHandoff.PayloadAt (payload (color d) d) incoming)
    (real : color d ≠ none) (distinct : global.tree.shape.leaves.Nodup)
    (header : PrimaryHeaderController.Header η)
    (rootId : header.rootId = decorated.rootRecord.1)
    (leftWing : header.leftWing = (representation none wingOrientation headerKey payload forest (some true)).isSome)
    (rightWing : header.rightWing = (representation none wingOrientation headerKey payload forest (some false)).isSome)
    (cached : MultiSourceProgram.Configuration (Sum (Option Bool) G) β (CachedCell ι η))
    (cachedErases : cached.mapRecords Prod.fst = MultiSourcePacketPrefix.attached saved tree outside global)
    (cachedCurrent : Cursor β (CachedCell ι η))
    (cachedAtRoot : MultiSourceSingleCursor.Represents entry cachedCurrent cached)
    (cachedHeader : cachedCurrent.focus.rootRecord.2 = some header)
    (cachedIncoming : Cursor β (CachedCell ι η))
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
    (incomingForest : TaggedForest (Option Bool) Nat (Logical η) ι)
    (incomingForestRep : ProjectionForest.Represents incomingColor ⟨annotate Prod.fst incomingColor none incomingDecorated,[]⟩ (erase incomingForest))
    (incomingUnique : Unique incomingForest)
    (incomingPayloads : Option Bool → Nat → Source β (List (Option (Datum ι η))))
    (incomingConfig : MultiSourceProgram.Configuration (Option Bool) β (List (Option (Datum ι η))))
    (incomingAssembly : ForestConnector.assemble (representation none wingOrientation headerKey incomingPayloads incomingForest)
      (layout (representation none wingOrientation headerKey incomingPayloads incomingForest)) = some incomingConfig)
    (attached : payload (color d) d = incomingConfig.tree)
    (incomingHeader : PrimaryHeaderController.Header η)
    (incomingRootId : incomingHeader.rootId = incomingDecorated.rootRecord.1)
    (incomingLeftWing : incomingHeader.leftWing = (representation none wingOrientation headerKey incomingPayloads incomingForest (some true)).isSome)
    (incomingRightWing : incomingHeader.rightWing = (representation none wingOrientation headerKey incomingPayloads incomingForest (some false)).isSome)
    (incomingCachedHeader : cachedIncoming.focus.rootRecord.2 = some incomingHeader) :
    ∃ (right incomingRight : AuxiliaryComponent Nat Nat (Tagged Payload)) (high incomingHigh : Cached),
      ∃ highId terminalId incomingHighId incomingTerminalId,
      ∃ taggedTail incomingTail : Source Nat (η × Cached),
      ∃ activeFinalForest incomingFinalForest activeFinalConfig incomingFinalConfig,
      ∃ actualFinal returnedActive reachedIncoming, ∃ activePhysicalRoot incomingAttachment reads cost,
      high.2.1 = d ∧ incomingHigh.2.1 = d ∧
      Clean right.core ∧ MarkedPorts right ∧
      Clean incomingRight.core ∧ MarkedPorts incomingRight ∧
      taggedTail.mapRecords Prod.snd = right.tree ∧
      incomingTail.mapRecords Prod.snd = incomingRight.tree ∧
      MultiSourceProgram.Run
        (RootPreparedPairHeaderController.program entry saved.length (!outside.isEmpty) activeAnchor anchor d)
        (.first (.first (.first .start))) cached
        (.second (some ⟨{header with rootId := highId},{incomingHeader with rootId := incomingHighId},
          BoundaryReadController.sentinelResult Prod.fst color (highId,high)
            (terminalId,(terminalLeaf d).rootRecord) d taggedTail,
          BoundaryReadController.sentinelResult Prod.fst incomingColor (incomingHighId,incomingHigh)
            (incomingTerminalId,(terminalLeaf d).rootRecord) d incomingTail⟩)
          (.second (some (ForestMirrorController.transform wingOrientation (encode activeFinalForest) none))
            (some (some (.done (some (ForestMirrorController.transform wingOrientation (encode incomingFinalForest) none)))))))
        actualFinal reads cost ∧
      ProjectionForest.Represents color
        ⟨annotate Prod.fst color none (.fork (highId,high) (.leaf d (terminalId,(terminalLeaf d).rootRecord)) taggedTail),[]⟩ (erase activeFinalForest) ∧
      Unique activeFinalForest ∧
      ProjectionForest.Represents incomingColor
        ⟨annotate Prod.fst incomingColor none (.fork (incomingHighId,incomingHigh)
          (.leaf d (incomingTerminalId,(terminalLeaf d).rootRecord)) incomingTail),[]⟩ (erase incomingFinalForest) ∧
      Unique incomingFinalForest ∧
      ForestConnector.assemble (representation none wingOrientation headerKey incomingPayloads incomingFinalForest)
        (layout (representation none wingOrientation headerKey incomingPayloads incomingFinalForest)) = some incomingFinalConfig ∧
      (∀ q, (representation none wingOrientation headerKey incomingPayloads incomingFinalForest q).isSome =
        (representation none wingOrientation headerKey incomingPayloads incomingForest q).isSome) ∧
      MultiSourceSingleCursor.Represents (.inr activeAnchor) returnedActive actualFinal ∧
      (returnedActive.focus.mapRecords Prod.fst).mapRecords Prod.snd = activeFinalConfig.tree.setRoot
        (PacketPrefixTransfer.reidentify activePhysicalRoot saved ++ activeFinalConfig.tree.rootRecord) ∧
      returnedActive.focus.rootRecord.1.1 = activePhysicalRoot ∧
      returnedActive.focus.rootRecord.2 = some {header with rootId := highId} ∧
      MultiSourceSingleCursor.Represents (.inl none) reachedIncoming actualFinal ∧
      reachedIncoming.focus.rootRecord.2 = some {incomingHeader with rootId := incomingHighId} ∧
      List.length incomingAttachment = 2 ∧
      (reachedIncoming.focus.mapRecords Prod.fst).mapRecords Prod.snd =
        incomingFinalConfig.tree.setRoot (incomingAttachment ++ incomingFinalConfig.tree.rootRecord) ∧
      CanonicalRetainedPayloadHandoff.PayloadAt incomingFinalConfig.tree (reachedIncoming.mapRecords Prod.fst) ∧
      MultiSourceProgram.WellFormed actualFinal ∧
      CanonicalComponentUniqueness.Valid markerId (actualFinal.mapRecords Prod.fst).tree ∧
      markerId ∉ (actualFinal.mapRecords Prod.fst).tree.inventory Prod.fst ∧
      (actualFinal.mapRecords Prod.fst).tree.inventory Prod.fst = global.tree.inventory Prod.fst ∧
      HeadCacheFrame.MetadataFrame Prod.fst
        [activePhysicalRoot,reachedIncoming.focus.rootRecord.1.1] cached.tree actualFinal.tree ∧
      (actualFinal.mapRecords Prod.fst).tree.inorderLabels Prod.fst = global.tree.inorderLabels Prod.fst ∧
      cost ≤ 8*(474240*(40110*Nat.clog 2 ((LocalReferences.depthReference reference).height+1)+2)+49920)+99 ∧
      let newPayload := Function.update payload (color d) (Function.update (payload (color d)) d incomingFinalConfig.tree)
      ForestConnector.assemble (representation none wingOrientation headerKey newPayload activeFinalForest)
        (layout (representation none wingOrientation headerKey newPayload activeFinalForest)) = some activeFinalConfig ∧
      (∀ q, (representation none wingOrientation headerKey newPayload activeFinalForest q).isSome =
        (representation none wingOrientation headerKey payload forest q).isSome) ∧
      d::taggedTail.shape.leaves = decorated.shape.leaves ∧
      d::incomingTail.shape.leaves = incomingDecorated.shape.leaves ∧
      returnedActive.ancestors.isEmpty = outside.isEmpty ∧
      PreparedSplitWitnesses.Sentinel component d right high ∧
      PreparedSplitWitnesses.Sentinel incomingComponent d incomingRight incomingHigh ∧
      (Source.fork (highId,high) (.leaf d (terminalId,(terminalLeaf d).rootRecord)) taggedTail).inventory Prod.fst = decorated.inventory Prod.fst ∧
      (Source.fork (incomingHighId,incomingHigh) (.leaf d (incomingTerminalId,(terminalLeaf d).rootRecord)) incomingTail).inventory Prod.fst =
        incomingDecorated.inventory Prod.fst := by
  obtain ⟨right,incomingRight,high,incomingHigh,highId,terminalId,incomingHighId,incomingTerminalId,
    taggedTail,incomingTail,activeFinalForest,incomingFinalForest,activeFinalConfig,incomingFinalConfig,
    middle,returnedActive,reachedIncoming,activePhysicalRoot,incomingAttachment,firstReads,firstCost,
    highKey,incomingHighKey,rightClean,rightMarked,incomingClean,incomingMarked,
    tailEq,incomingTailEq,front,activeFinalRep,activeFinalUnique,incomingFinalRep,incomingFinalUnique,
    incomingFinalAssembly,incomingPresence,activeReturned,activeView,activeIdentity,activeCache,
    incomingReturned,incomingCache,incomingAttachmentLength,incomingView,incomingPayloadAt,middleValid,middlePhysical,
    middleReserved,middleIds,frame,order,frontBound,activeFinalAssembly,activePresence,activeLeaves,incomingLeaves,activeAncestors,activeSplit,incomingSplit,activeIds,incomingIds⟩ :=
    RootPreparedPairExecution.execute markerId reference preferences d terminal minimum upper component represented color decorated erases logicalUnique
      forest forestRep physicalUnique headerKey payload config assembled tree treeErases outside global wellFormed physical reserved
      entry entryRep saved anchor incoming incomingRep incomingPayload real distinct header rootId leftWing rightWing cached cachedErases
      cachedCurrent cachedAtRoot cachedHeader cachedIncoming cachedIncomingRep activeAnchor differentAnchors neutral
      incomingPreferences incomingTerminal incomingComponent incomingRepresented incomingColor incomingDecorated incomingErases incomingLogicalUnique
      incomingForest incomingForestRep incomingUnique incomingPayloads incomingConfig incomingAssembly attached incomingHeader incomingRootId
      incomingLeftWing incomingRightWing incomingCachedHeader
  let activeValues := BoundaryReadController.sentinelResult Prod.fst color (highId,high)
    (terminalId,(terminalLeaf d).rootRecord) d taggedTail
  let incomingValues := BoundaryReadController.sentinelResult Prod.fst incomingColor (incomingHighId,incomingHigh)
    (incomingTerminalId,(terminalLeaf d).rootRecord) d incomingTail
  let inputs : RootPreparedPairHeaderController.Inputs η :=
    ⟨{header with rootId := highId},{incomingHeader with rootId := incomingHighId},activeValues,incomingValues⟩
  let newPayload := Function.update payload (color d) (Function.update (payload (color d)) d incomingFinalConfig.tree)
  let payloads := fun side : Bool => if side then incomingPayloads else newPayload
  let forests := fun side : Bool => if side then incomingFinalForest else activeFinalForest
  let configs := fun side : Bool => if side then incomingFinalConfig else activeFinalConfig
  let packets := fun side : Bool => if side then incomingAttachment else PacketPrefixTransfer.reidentify activePhysicalRoot saved
  let cursors := fun side : Bool => if side then reachedIncoming else returnedActive
  let headers := RootPreparedPairHeaderController.headers inputs
  have assemblies : ∀ side, ForestConnector.assemble
      (ComponentPhysicalRepair.view none wingOrientation headerKey (payloads side) (encode (forests side)))
      (layout (ComponentPhysicalRepair.view none wingOrientation headerKey (payloads side) (encode (forests side)))) = some (configs side) := by
    intro side
    cases side
    · exact activeFinalAssembly
    · exact incomingFinalAssembly
  have leftBits : ∀ side, (headers side).leftWing =
      (ComponentPhysicalRepair.view none wingOrientation headerKey (payloads side) (encode (forests side)) (some true)).isSome := by
    intro side
    cases side
    · exact leftWing.trans (activePresence (some true)).symm
    · exact incomingLeftWing.trans (incomingPresence (some true)).symm
  have rightBits : ∀ side, (headers side).rightWing =
      (ComponentPhysicalRepair.view none wingOrientation headerKey (payloads side) (encode (forests side)) (some false)).isSome := by
    intro side
    cases side
    · exact rightWing.trans (activePresence (some false)).symm
    · exact incomingRightWing.trans (incomingPresence (some false)).symm
  have views : ∀ side, (cursors side).focus.mapRecords (fun record => record.1.2) =
      (configs side).tree.setRoot (packets side++(configs side).tree.rootRecord) := by
    intro side
    cases side
    · simpa only [MultiSourceRecordEquivalence.map_source_comp,Function.comp_def,cursors,configs,packets,Bool.false_eq_true,if_false] using activeView
    · simpa only [MultiSourceRecordEquivalence.map_source_comp,Function.comp_def,cursors,configs,packets,if_true] using incomingView
  have positions : ∀ side, MultiSourceSingleCursor.Represents (RootPreparedPairHeaderController.origins activeAnchor side) (cursors side) middle := by
    intro side
    cases side
    · exact activeReturned
    · exact incomingReturned
  obtain ⟨final,lastReads,lastCost,readRun,finalTree,finalFingers,finalPositions,readBound⟩ :=
    ReachedVirtualHeaderPair.execute (RootPreparedPairHeaderController.origins activeAnchor) (.inl (some true))
      (by intro side; cases side <;> simp [RootPreparedPairHeaderController.origins])
      (fun record => record.1.2) headers (fun _ => wingOrientation) (fun _ => headerKey) payloads forests configs
      assemblies leftBits rightBits packets cursors views middle positions
  have counts : (fun side => (packets side).length) = (fun side => if side then 2 else saved.length) := by
    funext side
    cases side
    · simp only [packets,Bool.false_eq_true,if_false,PacketPrefixTransfer.reidentify,List.length_map]
    · exact incomingAttachmentLength
  rw [counts] at readRun
  have actual := RootPreparedPairHeaderController.append_reads entry saved.length (!outside.isEmpty) activeAnchor anchor d
    cached middle final header incomingHeader highId incomingHighId activeValues incomingValues _ _ front readRun
  have physicalTree : (final.mapRecords Prod.fst).tree = (middle.mapRecords Prod.fst).tree := congrArg (Source.mapRecords Prod.fst) finalTree
  refine ⟨right,incomingRight,high,incomingHigh,highId,terminalId,incomingHighId,incomingTerminalId,
    taggedTail,incomingTail,activeFinalForest,incomingFinalForest,activeFinalConfig,incomingFinalConfig,
    final,returnedActive,reachedIncoming,activePhysicalRoot,incomingAttachment,firstReads++lastReads,firstCost+lastCost,
    highKey,incomingHighKey,rightClean,rightMarked,incomingClean,incomingMarked,
    tailEq,incomingTailEq,actual,activeFinalRep,activeFinalUnique,incomingFinalRep,incomingFinalUnique,
    incomingFinalAssembly,incomingPresence,finalPositions false,activeView,activeIdentity,activeCache,
    finalPositions true,incomingCache,incomingAttachmentLength,incomingView,incomingPayloadAt,readRun.wellFormed middleValid,
    physicalTree.symm ▸ middlePhysical,physicalTree.symm ▸ middleReserved,physicalTree.symm ▸ middleIds,
    finalTree.symm ▸ frame,physicalTree.symm ▸ order,by omega,activeFinalAssembly,activePresence,activeLeaves,incomingLeaves,activeAncestors,activeSplit,incomingSplit,activeIds,incomingIds⟩

end ChaCha.Paper20261030.SecondaryDecomposition.RootPreparedPairHeaderExecution
