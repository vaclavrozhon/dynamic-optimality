import ChaCha.Paper20261030.HeadCacheFrame
import ChaCha.Paper20261030.CachedPreparedComponentHandoff
import ChaCha.Paper20261030.IncomingPreparationPreservesActive
import ChaCha.Paper20261030.PreparedPairController

set_option autoImplicit false

/-! Both interior-head preparation phases in one actual cached program.
The initial shared representation supplies both phases; their observations
remain in the final state. One charged copy parks the active component.
Incoming preparation preserves its canonical view and cached header. -/

namespace ChaCha.Paper20261030.SecondaryDecomposition.PreparedPairExecution

open ColoredStorage SourcePointer Structural PhysicalForestMetadata Auxiliary AuxiliaryComponent BoundaryObservations PathDecomposition
open LocalComponentForestCompiler LocalComponentCompiler ForestConnector.ThreeColors MultiSourceProgram
open PreparedExposureExecution (Logical Datum)
open ObservedPreparedExposure

variable {β ι η G : Type*} [DecidableEq ι] [DecidableEq η] [DecidableEq G]

local instance preparedPairExecutionColorOrder : LinearOrder (Option Bool) := inferInstanceAs (LinearOrder (WithBot Bool))

theorem execute (markerId : ι) {a b : Nat} (reference : DepthTree a b) (preferences : DepthSplit → Bool)
    (d : Nat) (terminal : (Secondary.decodeDepth reference preferences).terminal = d) (lower : a < d) (upper : d < b)
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
    ∃ (left right incomingRight : AuxiliaryComponent Nat Nat (Tagged Payload)) (low high incomingHigh : Cached),
      ∃ lowId highId terminalId incomingHighId incomingTerminalId,
      ∃ taggedHead taggedTail incomingTail : Source Nat (η × Cached),
      ∃ activeFinalForest incomingFinalForest activeFinalConfig incomingFinalConfig,
      ∃ actualFinal returnedActive reachedIncoming, ∃ activePhysicalRoot incomingAttachment reads cost,
      low.2.1 = d-1 ∧ high.2.1 = d ∧ incomingHigh.2.1 = d ∧
      Clean left.core ∧ MarkedPorts left ∧ Clean right.core ∧ MarkedPorts right ∧
      Clean incomingRight.core ∧ MarkedPorts incomingRight ∧
      taggedHead.mapRecords Prod.snd = left.tree ∧ taggedTail.mapRecords Prod.snd = right.tree ∧
      incomingTail.mapRecords Prod.snd = incomingRight.tree ∧
      MultiSourceProgram.Run
        (PreparedPairController.program entry saved.length (!outside.isEmpty) activeAnchor anchor d)
        (.first (.first .start)) cached
        (.second (some (header,lowId,.inl none,some
          (BoundaryReadController.activeResult Prod.fst color (lowId,low) (highId,high)
            (terminalId,(terminalLeaf d).rootRecord) d taggedHead taggedTail)))
          (some (.second (some (incomingHeader,incomingHighId,.inl none,some
            (BoundaryReadController.sentinelResult Prod.fst incomingColor (incomingHighId,incomingHigh)
              (incomingTerminalId,(terminalLeaf d).rootRecord) d incomingTail))) (some .done))))
        actualFinal reads cost ∧
      ProjectionForest.Represents color
        ⟨annotate Prod.fst color none (.fork (lowId,low) taggedHead
          (.fork (highId,high) (.leaf d (terminalId,(terminalLeaf d).rootRecord)) taggedTail)),[]⟩ (erase activeFinalForest) ∧
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
      returnedActive.focus.rootRecord.2 = some {header with rootId := lowId} ∧
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
      cost ≤ 4*(474240*(120330*Nat.clog 2 ((LocalReferences.depthReference reference).height+1)+6)+137280)+91 ∧
      let newPayload := Function.update payload (color d) (Function.update (payload (color d)) d incomingFinalConfig.tree)
      ForestConnector.assemble (representation none wingOrientation headerKey newPayload activeFinalForest)
        (layout (representation none wingOrientation headerKey newPayload activeFinalForest)) = some activeFinalConfig ∧
      (∀ q, (representation none wingOrientation headerKey newPayload activeFinalForest q).isSome =
        (representation none wingOrientation headerKey payload forest q).isSome) ∧
      taggedHead.shape.leaves ++ d::taggedTail.shape.leaves = decorated.shape.leaves ∧
      d::incomingTail.shape.leaves = incomingDecorated.shape.leaves ∧
      returnedActive.ancestors.isEmpty = outside.isEmpty ∧
      PreparedSplitWitnesses.Active component d left right low high ∧
      PreparedSplitWitnesses.Sentinel incomingComponent d incomingRight incomingHigh ∧
      (Source.fork (lowId,low) taggedHead (.fork (highId,high)
          (.leaf d (terminalId,(terminalLeaf d).rootRecord)) taggedTail)).inventory Prod.fst = decorated.inventory Prod.fst ∧
      (Source.fork (incomingHighId,incomingHigh) (.leaf d (incomingTerminalId,(terminalLeaf d).rootRecord)) incomingTail).inventory Prod.fst =
        incomingDecorated.inventory Prod.fst := by
  obtain ⟨left,right,low,high,lowId,highId,terminalId,taggedHead,taggedTail,middleForest,middleConfig,activeComponent,
    middleRaw,frontReads,frontCost,incomingTarget,middleCached,activeReached,incomingReached,
    lowKey,highKey,leftClean,leftMarked,rightClean,rightMarked,activeSplit,headEq,tailEq,
    front,middleErases,activeReachedErases,activeLocated,activeHeaderCorrect,middleValid,frontRetained,
    incomingLocated,incomingReachedErases,incomingCache,
    activeIds,activeLeaves,middleRep,middleUnique,middleAssembly,middlePresence,activeComponentErases,middleReturned,middleIds,
    middlePhysical,middleReserved,middleWellFormed,middleOrder,middleAnchors,incomingPositioned,
    incomingPayloadAt,differentRoots,incomingProper,attachment,sameIncoming,frontBound⟩ :=
    active_cached_handoff markerId reference preferences d terminal lower upper component represented color decorated erases logicalUnique
      forest forestRep physicalUnique headerKey payload config assembled tree treeErases outside global wellFormed physical reserved
      entry entryRep saved anchor incoming incomingRep incomingPayload real distinct header rootId leftWing rightWing cached cachedErases
      cachedCurrent cachedAtRoot cachedHeader cachedIncoming cachedIncomingRep
  let parkedCached := copyResult middleCached (.inr activeAnchor) (.inl none)
  let parkedRaw := copyResult middleRaw (.inr activeAnchor) (.inl none)
  let activeCursor := PrimaryHeaderRefresh.refreshed header lowId activeReached
  have copiedErases : parkedCached.mapRecords Prod.fst = parkedRaw := by
    change (copyResult middleCached _ _).mapRecords Prod.fst = _
    rw [copyResult_mapRecords,middleErases]
  have other : (Sum.inr anchor : Sum (Option Bool) G) ≠ .inr activeAnchor := by
    intro equal
    exact differentAnchors (Sum.inr.inj equal)
  have copiedIncoming := MultiSourceParkContinuation.other (.inr activeAnchor) (.inl none) (.inr anchor) other
    incomingReached middleCached incomingLocated
  have copiedRawIncoming := MultiSourceParkContinuation.other (.inr activeAnchor) (.inl none) (.inr anchor) other
    incomingTarget middleRaw incomingPositioned
  have copiedActive := MultiSourceParkContinuation.parked (.inr activeAnchor) (.inl none) activeCursor middleCached activeLocated
  have activeErased : activeCursor.mapRecords Prod.fst =
      EnclosingPacketOperation.output saved tree.rootRecord.1 ⟨activeComponent.tree,outside⟩ :=
    (PrimaryHeaderRefresh.refreshed_erases header lowId activeReached).trans activeReachedErases
  have activeTreeErases : activeComponent.tree.mapRecords Prod.snd = middleConfig.tree :=
    congrArg Configuration.tree activeComponentErases
  have activeIdentity : activeCursor.focus.rootRecord.1.1 = activeComponent.tree.rootRecord.1 := by
    have identity := congrArg (fun cursor : Cursor β (ReentryCell ι η) => cursor.focus.rootRecord.1) activeErased
    simpa only [Cursor.mapRecords,Source.mapRecords_root,EnclosingPacketOperation.output,PacketPrefixTransfer.output_root_id] using identity
  have middleDistinct : parkedRaw.tree.shape.leaves.Nodup := by
    change middleRaw.tree.shape.leaves.Nodup
    have initialDistinct : cached.tree.shape.leaves.Nodup := by
      have erasure := congrArg (fun config : Configuration (Sum (Option Bool) G) β (ReentryCell ι η) => config.tree.shape.leaves) cachedErases
      simp only [Configuration.mapRecords,Source.mapRecords_shape] at erasure
      have attachedLeaves : (MultiSourcePacketPrefix.attached saved tree outside global).tree.shape.leaves = global.tree.shape.leaves := by
        rw [entryRep.1]
        exact (SourcePointer.Step.write tree (tree.rootRecord.1,saved++tree.rootRecord.2) outside).leaves.symm
      rw [erasure,attachedLeaves]
      exact distinct
    have finalDistinct : middleCached.tree.shape.leaves.Nodup := front.leaves ▸ initialDistinct
    rw [← middleErases]
    simpa only [Configuration.mapRecords,Source.mapRecords_shape] using finalDistinct
  obtain ⟨incomingPrefix,incomingPrefixLength,incomingView⟩ := attachment
  rw [attached] at incomingView
  obtain ⟨incomingRight,incomingHigh,incomingHighId,incomingTerminalId,incomingTail,incomingFinalForest,incomingFinalConfig,incomingFinalComponent,
    finalRaw,backReads,backCost,actualFinal,lastReached,activeFinalForest,activeFinalConfig,returnedActive,
    incomingHighKey,incomingClean,incomingMarked,incomingSplit,incomingTailEq,back,finalErases,incomingOutputErases,incomingFinalLocated,
    incomingHeaderCorrect,finalValid,backRetained,incomingIds,incomingLeaves,incomingFinalRep,incomingFinalUnique,incomingFinalAssembly,
    incomingPresence,incomingComponentErases,incomingReturned,finalIds,finalPhysical,finalReserved,finalWellFormed,
    finalOrder,finalAnchors,backBound,updatedErases,updatedRep,updatedUnique,updatedAssembly,updatedPresence,
    activeReturned,activeView,activeFinalIdentity,activeCache,activeAncestors⟩ :=
    incoming_cached_with_active markerId reference incomingPreferences d ⟨by omega,by omega⟩ incomingTerminal upper
      incomingComponent incomingRepresented incomingColor incomingDecorated incomingErases incomingLogicalUnique
      incomingForest incomingForestRep incomingUnique headerKey incomingPayloads incomingConfig incomingAssembly
      incomingTarget incomingPrefix incomingPrefixLength incomingProper incomingView parkedRaw
      (copy_wellFormed middleRaw middleWellFormed _ _) middlePhysical middleReserved (.inr anchor) copiedRawIncoming
      incomingHeader incomingRootId incomingLeftWing incomingRightWing parkedCached copiedErases incomingReached copiedIncoming
      (incomingCache.trans incomingCachedHeader) color
      (.fork (lowId,low) taggedHead (.fork (highId,high) (.leaf d (terminalId,(terminalLeaf d).rootRecord)) taggedTail))
      middleForest middleRep middleUnique headerKey payload middleConfig middleAssembly activeComponent.tree activeTreeErases
      outside saved tree.rootRecord.1 neutral activeAnchor activeCursor copiedActive activeErased
      (by simp [Source.shape,RouterProjection.Router.leaves]) real attached middleDistinct
  have composed := PreparedPairController.compose entry saved.length (!outside.isEmpty) activeAnchor anchor d
    cached middleCached actualFinal header incomingHeader lowId incomingHighId _ _ front back
  let incomingAttachment := PacketPrefixTransfer.reidentify incomingFinalComponent.tree.rootRecord.1 incomingPrefix
  have incomingAttachmentLength : incomingAttachment.length = 2 := by
    simpa only [incomingAttachment,PacketPrefixTransfer.reidentify,List.length_map] using incomingPrefixLength
  have incomingAttachedView :
      ((PrimaryHeaderRefresh.refreshed incomingHeader incomingHighId lastReached).focus.mapRecords Prod.fst).mapRecords Prod.snd =
        incomingFinalConfig.tree.setRoot (incomingAttachment ++ incomingFinalConfig.tree.rootRecord) := by
    have rawFocus := congrArg Cursor.focus
      ((PrimaryHeaderRefresh.refreshed_erases incomingHeader incomingHighId lastReached).trans incomingOutputErases)
    change (PrimaryHeaderRefresh.refreshed incomingHeader incomingHighId lastReached).focus.mapRecords Prod.fst = _ at rawFocus
    rw [rawFocus]
    change (PacketPrefixTransfer.output incomingPrefix incomingFinalComponent.tree).mapRecords Prod.snd = _
    rw [PacketPrefixTransfer.output,PacketPrefixTransfer.attach,Source.mapRecords_setRoot]
    have componentTree : incomingFinalComponent.tree.mapRecords Prod.snd = incomingFinalConfig.tree :=
      congrArg Configuration.tree incomingComponentErases
    have componentRoot := congrArg Source.rootRecord componentTree
    simp only [Source.mapRecords_root] at componentRoot
    rw [componentTree,componentRoot]
  have incomingViewFinal : CanonicalRetainedPayloadHandoff.PayloadAt incomingFinalConfig.tree
      ((PrimaryHeaderRefresh.refreshed incomingHeader incomingHighId lastReached).mapRecords Prod.fst) := by
    unfold CanonicalRetainedPayloadHandoff.PayloadAt
    rw [PrimaryHeaderRefresh.refreshed_erases,incomingOutputErases]
    change ((PacketPrefixTransfer.output incomingPrefix incomingFinalComponent.tree).mapRecords Prod.snd).setRoot _ = _
    rw [PacketPrefixTransfer.output,PacketPrefixTransfer.attach,Source.mapRecords_setRoot]
    have componentTree : incomingFinalComponent.tree.mapRecords Prod.snd = incomingFinalConfig.tree :=
      congrArg Configuration.tree incomingComponentErases
    rw [componentTree]
    cases incomingFinalConfig.tree <;> rfl
  have cachedIds : cached.tree.inventory (Prod.fst ∘ Prod.fst) = global.tree.inventory Prod.fst := by
    rw [← mapRecords_inventory Prod.fst Prod.fst cached.tree]
    change (cached.mapRecords Prod.fst).tree.inventory Prod.fst = _
    rw [cachedErases,MultiSourcePacketPrefix.attached_inventory saved tree outside global entryRep.1]
  have middleCacheIds : middleCached.tree.inventory (Prod.fst ∘ Prod.fst) = cached.tree.inventory (Prod.fst ∘ Prod.fst) := by
    rw [← mapRecords_inventory Prod.fst Prod.fst middleCached.tree]
    change (middleCached.mapRecords Prod.fst).tree.inventory Prod.fst = _
    rw [middleErases,middleIds,cachedIds]
  have finalCacheIds : actualFinal.tree.inventory (Prod.fst ∘ Prod.fst) = parkedCached.tree.inventory (Prod.fst ∘ Prod.fst) := by
    rw [← mapRecords_inventory Prod.fst Prod.fst actualFinal.tree,
      ← mapRecords_inventory Prod.fst Prod.fst parkedCached.tree]
    change (actualFinal.mapRecords Prod.fst).tree.inventory Prod.fst = (parkedCached.mapRecords Prod.fst).tree.inventory Prod.fst
    rw [finalErases,finalIds,copiedErases]
  have frontFrame := HeadCacheFrame.MetadataFrame.of_retained Prod.fst activeComponent.tree.rootRecord.1
    cached.tree middleCached.tree middleCacheIds frontRetained
  have backFrame := HeadCacheFrame.MetadataFrame.of_retained Prod.fst incomingFinalComponent.tree.rootRecord.1
    parkedCached.tree actualFinal.tree finalCacheIds backRetained
  have incomingIdentity : (PrimaryHeaderRefresh.refreshed incomingHeader incomingHighId lastReached).focus.rootRecord.1.1 =
      incomingFinalComponent.tree.rootRecord.1 := by
    have same := congrArg (fun cursor : Cursor β (ReentryCell ι η) => cursor.focus.rootRecord.1)
      ((PrimaryHeaderRefresh.refreshed_erases incomingHeader incomingHighId lastReached).trans incomingOutputErases)
    simpa only [Cursor.mapRecords,Source.mapRecords_root,EnclosingPacketOperation.output,PacketPrefixTransfer.output_root_id] using same
  have frame : HeadCacheFrame.MetadataFrame Prod.fst
      [activeComponent.tree.rootRecord.1,(PrimaryHeaderRefresh.refreshed incomingHeader incomingHighId lastReached).focus.rootRecord.1.1]
      cached.tree actualFinal.tree := by
    rw [incomingIdentity]
    exact frontFrame.trans backFrame
  have totalOrder : (actualFinal.mapRecords Prod.fst).tree.inorderLabels Prod.fst = global.tree.inorderLabels Prod.fst := by
    rw [finalErases,finalOrder]
    exact middleOrder
  refine ⟨left,right,incomingRight,low,high,incomingHigh,lowId,highId,terminalId,incomingHighId,incomingTerminalId,
    taggedHead,taggedTail,incomingTail,activeFinalForest,incomingFinalForest,activeFinalConfig,incomingFinalConfig,
    actualFinal,returnedActive,PrimaryHeaderRefresh.refreshed incomingHeader incomingHighId lastReached,
    activeComponent.tree.rootRecord.1,incomingAttachment,frontReads++backReads,frontCost+backCost+1,
    lowKey,highKey,incomingHighKey,leftClean,leftMarked,rightClean,rightMarked,incomingClean,incomingMarked,
    headEq,tailEq,incomingTailEq,composed,updatedRep,updatedUnique,incomingFinalRep,incomingFinalUnique,
    incomingFinalAssembly,incomingPresence,activeReturned,activeView,activeFinalIdentity.trans activeIdentity,
    activeCache.trans activeHeaderCorrect,incomingFinalLocated,incomingHeaderCorrect,incomingAttachmentLength,incomingAttachedView,incomingViewFinal,finalValid,
    finalErases.symm ▸ finalPhysical,finalErases.symm ▸ finalReserved,?_,frame,totalOrder,by omega,updatedAssembly,?_,activeLeaves,incomingLeaves,?_,activeSplit,incomingSplit,activeIds,incomingIds⟩
  · rw [finalErases,finalIds]
    exact middleIds
  · intro q
    exact (updatedPresence q).trans (middlePresence q)

  · have context := activeAncestors.trans (congrArg Cursor.ancestors activeErased)
    cases outside <;> simpa only [Cursor.mapRecords,List.isEmpty_map,EnclosingPacketOperation.output,
      List.isEmpty_nil,List.isEmpty_cons] using congrArg List.isEmpty context

end ChaCha.Paper20261030.SecondaryDecomposition.PreparedPairExecution
