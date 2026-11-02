import ChaCha.Paper20261030.CachedObservedPreparation
import ChaCha.Paper20261030.CanonicalRetainedPayloadHandoff
import ChaCha.Paper20261030.CachedObservedComponent
import ChaCha.Paper20261030.CachedAnchorHandoff
import ChaCha.Paper20261030.AttachedPacketIdentifiers

set_option autoImplicit false

/-! Preparing a minimum-depth active component uses the sentinel split.
The actual cached run retains the parked incoming payload and its cache,
so the incoming phase can start at that same finger. The theorem is
stated for any suffix representation and real boundary color. -/

namespace ChaCha.Paper20261030.SecondaryDecomposition.ObservedPreparedExposure

open ColoredStorage SourcePointer Structural PhysicalForestMetadata Auxiliary AuxiliaryComponent BoundaryObservations PathDecomposition
open LocalComponentForestCompiler LocalComponentCompiler ForestConnector.ThreeColors MultiSourceProgram
open PreparedExposureExecution (Logical Datum)

variable {β ι η G : Type*} [DecidableEq ι] [DecidableEq η] [DecidableEq G]

local instance sentinelPreparationHandoffColorOrder : LinearOrder (Option Bool) := inferInstanceAs (LinearOrder (WithBot Bool))

theorem sentinel_cached_handoff (markerId : ι) {a b : Nat} (reference : DepthTree a b) (preferences : DepthSplit → Bool)
    (d : Nat) (valid : a ≤ d ∧ d ≤ b) (terminal : (Secondary.decodeDepth reference preferences).terminal = d) (upper : d < b)
    (component : AuxiliaryComponent Nat Nat (Tagged Payload))
    (represented : Represents followsRight (suffixSource reference preferences d valid) component)
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
    (header : PrimaryHeaderController.Header η)
    (rootId : header.rootId = decorated.rootRecord.1)
    (leftWing : header.leftWing = (representation none wingOrientation headerKey payload forest (some true)).isSome)
    (rightWing : header.rightWing = (representation none wingOrientation headerKey payload forest (some false)).isSome)
    (cached : MultiSourceProgram.Configuration (Sum (Option Bool) G) β (CachedCell ι η))
    (cachedErases : cached.mapRecords Prod.fst = MultiSourcePacketPrefix.attached saved tree outside global)
    (cachedCurrent : Cursor β (CachedCell ι η))
    (cachedAtRoot : MultiSourceSingleCursor.Represents entry cachedCurrent cached)
    (cachedHeader : cachedCurrent.focus.rootRecord.2 = some header)
    (anchor : G) (incoming : Cursor β (ReentryCell ι η))
    (incomingRep : MultiSourceSingleCursor.Represents (.inr anchor) incoming global)
    (incomingPayload : CanonicalRetainedPayloadHandoff.PayloadAt (payload (color d) d) incoming)
    (real : color d ≠ none) (distinct : global.tree.shape.leaves.Nodup)
    (cachedIncoming : Cursor β (CachedCell ι η))
    (cachedIncomingRep : MultiSourceSingleCursor.Represents (.inr anchor) cachedIncoming cached) :
    ∃ (right : AuxiliaryComponent Nat Nat (Tagged Payload)) (high : Cached),
      ∃ highId terminalId, ∃ taggedTail : Source Nat (η × Cached), ∃ finalForest finalConfig,
      ∃ (finalComponent : MultiSourceProgram.Configuration (Option Bool) β (ReentryCell ι η)), ∃ target reads cost, ∃ actualConfig, ∃ reached actualIncoming : Cursor β (CachedCell ι η),
      ∃ incomingTarget : Cursor β (ReentryCell ι η),
      high.2.1 = d ∧ Clean right.core ∧ MarkedPorts right ∧
      PreparedSplitWitnesses.Sentinel component d right high ∧ taggedTail.mapRecords Prod.snd = right.tree ∧
      MultiSourceProgram.Run
        (CachedObservedComponent.program entry saved.length (!outside.isEmpty) false
          (fun _ => OpenSplitController.program d) (fun _ => .start))
        (.first .start) cached
        (.second (some (header,highId,.inl none,some
          (BoundaryReadController.sentinelResult Prod.fst color (highId,high)
            (terminalId,(terminalLeaf d).rootRecord) d taggedTail))) (some .done)) actualConfig reads cost ∧
      actualConfig.mapRecords Prod.fst = target ∧
      reached.mapRecords Prod.fst = EnclosingPacketOperation.output saved tree.rootRecord.1 ⟨finalComponent.tree,outside⟩ ∧
      MultiSourceSingleCursor.Represents (.inl none) (PrimaryHeaderRefresh.refreshed header highId reached) actualConfig ∧
      (PrimaryHeaderRefresh.refreshed header highId reached).focus.rootRecord.2 = some {header with rootId := highId} ∧
      MultiSourceProgram.WellFormed actualConfig ∧
      CachedRootOperation.RetainedMetadata Prod.fst finalComponent.tree.rootRecord.1 cached.tree actualConfig.tree ∧
      (Source.fork (highId,high) (.leaf d (terminalId,(terminalLeaf d).rootRecord)) taggedTail).inventory Prod.fst =
        decorated.inventory Prod.fst ∧
      (Source.fork (highId,high) (.leaf d (terminalId,(terminalLeaf d).rootRecord)) taggedTail).shape.leaves =
        decorated.shape.leaves ∧
      ProjectionForest.Represents color
        ⟨annotate Prod.fst color none (.fork (highId,high) (.leaf d (terminalId,(terminalLeaf d).rootRecord)) taggedTail),[]⟩ (erase finalForest) ∧
      Unique finalForest ∧
      ForestConnector.assemble (representation none wingOrientation headerKey payload finalForest)
        (layout (representation none wingOrientation headerKey payload finalForest)) = some finalConfig ∧
      (∀ q, (representation none wingOrientation headerKey payload finalForest q).isSome =
        (representation none wingOrientation headerKey payload forest q).isSome) ∧
      finalComponent.mapRecords Prod.snd = finalConfig ∧
      MultiSourceSingleCursor.Represents (.inl none)
        (EnclosingPacketOperation.output saved tree.rootRecord.1 ⟨finalComponent.tree,outside⟩) target ∧
      target.tree.inventory Prod.fst = global.tree.inventory Prod.fst ∧
      CanonicalComponentUniqueness.Valid markerId target.tree ∧
      markerId ∉ target.tree.inventory Prod.fst ∧ MultiSourceProgram.WellFormed target ∧
      target.tree.inorderLabels Prod.fst = global.tree.inorderLabels Prod.fst ∧
      (∀ extra : G, MultiSourceProgram.fingerLabel Prod.fst target (.inr extra) =
        MultiSourceProgram.fingerLabel Prod.fst global (.inr extra)) ∧
      MultiSourceSingleCursor.Represents (.inr anchor) actualIncoming actualConfig ∧
      actualIncoming.mapRecords Prod.fst = incomingTarget ∧
      actualIncoming.focus.rootRecord.2 = cachedIncoming.focus.rootRecord.2 ∧
      CanonicalRetainedPayloadHandoff.PayloadAt (payload (color d) d) incomingTarget ∧
      incomingTarget.focus.rootRecord.1 ≠ finalComponent.tree.rootRecord.1 ∧ incomingTarget.ancestors ≠ [] ∧
      (∃ packet : List (Option (Datum ι η)), packet.length = 2 ∧ incomingTarget.focus.mapRecords Prod.snd =
        (payload (color d) d).setRoot (packet ++ (payload (color d) d).rootRecord)) ∧
      (SubtreeMetadata.replacePayload incoming (payload (color d) d).rootRecord).focus =
        (SubtreeMetadata.replacePayload incomingTarget (payload (color d) d).rootRecord).focus ∧
      cost ≤ 4*(474240*(40110*Nat.clog 2 ((LocalReferences.depthReference reference).height+1)+2)+49920)+45 := by
  obtain ⟨right,high,highId,terminalId,taggedTail,finalForest,finalConfig,finalComponent,
    target,reads,cost,actualConfig,reached,highKey,rightClean,rightMarked,splitWitness,tailEq,
    actual,cacheErases,reachedErases,finalLocated,finalHeader,cacheValid,retained,
    ids,sourceLeaves,finalRep,finalUnique,finalAssembly,presence,componentErases,returned,globalIds,
    finalPhysical,finalReserved,finalValid,order,anchors,bound⟩ :=
    sentinel_cached markerId reference preferences d valid terminal upper component represented color decorated erases logicalUnique
      forest forestRep physicalUnique headerKey payload config assembled tree treeErases outside global wellFormed physical reserved
      entry entryRep saved header rootId leftWing rightWing cached cachedErases cachedCurrent cachedAtRoot cachedHeader
  have attachedLeaves : (MultiSourcePacketPrefix.attached saved tree outside global).tree.shape.leaves = global.tree.shape.leaves := by
    rw [entryRep.1]
    exact (SourcePointer.Step.write tree (tree.rootRecord.1,saved++tree.rootRecord.2) outside).leaves.symm
  have leafWord : global.tree.shape.leaves = target.tree.shape.leaves := by
    have same : (cached.mapRecords Prod.fst).tree.shape.leaves = (actualConfig.mapRecords Prod.fst).tree.shape.leaves := by
      simpa only [Configuration.mapRecords,Source.mapRecords_shape] using actual.leaves
    rw [cachedErases,cacheErases,attachedLeaves] at same
    exact same
  have componentTree : finalComponent.tree.mapRecords Prod.snd = finalConfig.tree := congrArg Configuration.tree componentErases
  obtain ⟨incomingTarget,positioned,payloadRep,differentRoots,incomingProper,attachment,samePayload⟩ :=
    CanonicalRetainedPayloadHandoff.handoff color
      (.fork (highId,high) (.leaf d (terminalId,(terminalLeaf d).rootRecord)) taggedTail)
      finalForest finalRep headerKey payload finalConfig finalAssembly finalComponent.tree componentTree outside saved tree.rootRecord.1
      global target (.inl none) returned leafWord order distinct finalPhysical.2.2 (.inr anchor) (anchors anchor)
      incoming incomingRep d (by simp [Source.shape,RouterProjection.Router.leaves]) real incomingPayload
  have cachedIncomingRaw := cachedIncomingRep.mapRecords Prod.fst
  have originalLabel := fingerLabel_of_represents Prod.fst (cached.mapRecords Prod.fst) (.inr anchor) _ cachedIncomingRaw
  rw [cachedErases,MultiSourcePacketPrefix.attached_fingerLabel saved tree outside global entryRep.1] at originalLabel
  have newLabel := fingerLabel_of_represents Prod.fst target (.inr anchor) incomingTarget positioned
  rw [anchors anchor,originalLabel] at newLabel
  have sameId : incomingTarget.focus.rootRecord.1 = cachedIncoming.focus.rootRecord.1.1 := by
    simpa only [Cursor.mapRecords,Source.mapRecords_root] using (Option.some.inj newLabel).symm
  have incomingAfter : MultiSourceSingleCursor.Represents (.inr anchor) incomingTarget (actualConfig.mapRecords Prod.fst) := by
    rw [cacheErases]
    exact positioned
  obtain ⟨actualIncoming,actualIncomingRep,incomingErases,incomingHeader⟩ := CachedRootOperation.retained_anchor
    Prod.fst finalComponent.tree.rootRecord.1 cached actualConfig retained (.inr anchor) cachedIncoming cachedIncomingRep
      incomingTarget incomingAfter sameId differentRoots
  exact ⟨right,high,highId,terminalId,taggedTail,finalForest,finalConfig,finalComponent,
    target,reads,cost,actualConfig,reached,actualIncoming,incomingTarget,highKey,rightClean,rightMarked,splitWitness,tailEq,
    actual,cacheErases,reachedErases,finalLocated,finalHeader,cacheValid,retained,
    ids,sourceLeaves,finalRep,finalUnique,finalAssembly,presence,componentErases,returned,globalIds,
    finalPhysical,finalReserved,finalValid,order,anchors,actualIncomingRep,incomingErases,incomingHeader,
    payloadRep,differentRoots,incomingProper,attachment,samePayload,bound⟩

end ChaCha.Paper20261030.SecondaryDecomposition.ObservedPreparedExposure
