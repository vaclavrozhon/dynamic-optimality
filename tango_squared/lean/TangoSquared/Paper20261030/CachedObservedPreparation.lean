import TangoSquared.Paper20261030.CachedPreparedComponentHandoff
import TangoSquared.Paper20261030.CachedObservedComponent
import TangoSquared.Paper20261030.CachedAnchorHandoff
import TangoSquared.Paper20261030.AttachedPacketIdentifiers

set_option autoImplicit false

/-! Actual cache-driven preparation of an incoming suffix component.
The cached header supplies entry parameters, and the two observed boundary
records are retained in the final scalar state for the head exchange. -/

namespace TangoSquared.Paper20261030.SecondaryDecomposition.ObservedPreparedExposure

open ColoredStorage SourcePointer Structural PhysicalForestMetadata Auxiliary AuxiliaryComponent BoundaryObservations PathDecomposition
open LocalComponentForestCompiler LocalComponentCompiler ForestConnector.ThreeColors MultiSourceProgram
open PreparedExposureExecution (Logical Datum)

variable {β ι η G : Type*} [DecidableEq ι] [DecidableEq η] [DecidableEq G]

local instance cachedSentinelPreparationColorOrder : LinearOrder (Option Bool) := inferInstanceAs (LinearOrder (WithBot Bool))

theorem sentinel_cached (markerId : ι) {a b : Nat} (reference : DepthTree a b) (preferences : DepthSplit → Bool)
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
    (cachedHeader : cachedCurrent.focus.rootRecord.2 = some header) :
    ∃ (right : AuxiliaryComponent Nat Nat (Tagged Payload)) (high : Cached),
      ∃ highId terminalId, ∃ taggedTail : Source Nat (η × Cached), ∃ finalForest finalConfig,
      ∃ (finalComponent : MultiSourceProgram.Configuration (Option Bool) β (ReentryCell ι η)), ∃ target reads cost, ∃ actualConfig, ∃ reached : Cursor β (CachedCell ι η),
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
      cost ≤ 4*(474240*(40110*Nat.clog 2 ((LocalReferences.depthReference reference).height+1)+2)+49920)+45 := by
  obtain ⟨right,high,highId,terminalId,taggedTail,finalForest,finalConfig,finalComponent,
    entryBits,finalBits,target,reads,cost,highKey,rightClean,rightMarked,splitWitness,tailEq,
    rawRun,ids,sourceLeaves,finalRep,finalUnique,finalAssembly,presence,componentErases,returned,globalIds,
    finalPhysical,finalReserved,finalValid,order,anchors,bound⟩ :=
    sentinel_reentered markerId reference preferences d valid terminal upper component represented color decorated erases logicalUnique
      forest forestRep physicalUnique headerKey payload config assembled tree treeErases outside global wellFormed physical reserved entry entryRep saved
  have path : PrimaryHeaderRefresh.path header = headerPath (representation none wingOrientation headerKey payload forest) := by
    simp only [PrimaryHeaderRefresh.path,headerPath,leftWing,rightWing]
  have cachedValid : WellFormed cached := by
    apply WellFormed.of_mapRecords Prod.fst
    rw [cachedErases]
    exact MultiSourcePacketPrefix.attached_wellFormed saved tree outside global entryRep.1 wellFormed
  let result := BoundaryReadController.sentinelResult Prod.fst color (highId,high)
    (terminalId,(terminalLeaf d).rootRecord) d taggedTail
  let last : CachedObservedComponent.State (OpenSplitController.State Nat (DepthSplit × Bool)) Nat Cached ι η :=
    .second highId (ComponentObserverCompiler.ready result highId)
  have selected : Run
      (CachedReenteredComponent.kernel entry saved.length (!outside.isEmpty)
        (fun h => ComponentBoundaryContinuation.program (OpenSplitController.program d) false h.rootId)
        (fun h => ComponentBoundaryContinuation.initial (OpenSplitController.program d) false h.rootId .start) header)
      (.first .start) (cached.mapRecords Prod.fst)
      (.second (some ⟨tree.rootRecord.1,finalComponent.tree.rootRecord.1,.second entryBits (finalBits,.ready last)⟩)
        (some .done)) target reads cost := by
    simp only [CachedReenteredComponent.kernel,leftWing,rightWing,path,rootId,cachedErases]
    exact rawRun
  have loadedOrder : target.tree.inorderLabels Prod.fst = (cached.mapRecords Prod.fst).tree.inorderLabels Prod.fst := by
    rw [cachedErases,MultiSourcePacketPrefix.attached_inorder saved tree outside global entryRep.1]
    exact order
  have loadedUnique : (cached.tree.inventory (fun record => record.1.1)).Nodup := by
    have rawUnique : ((cached.mapRecords Prod.fst).tree.inventory Prod.fst).Nodup := by
      rw [cachedErases,MultiSourcePacketPrefix.attached_inventory saved tree outside global entryRep.1]
      exact physical.2.2
    simpa only [Configuration.mapRecords,mapRecords_inventory,Function.comp_def] using rawUnique
  obtain ⟨actualConfig,observed,total,reached,actual,cacheErases,reachedErases,finalLocated,finalHeader,cacheValid,metadata,bounded⟩ :=
    CachedReenteredContinuation.dispatch entry saved.length (!outside.isEmpty)
      (fun h => ComponentBoundaryContinuation.program (OpenSplitController.program d) false h.rootId)
      (fun h => ComponentBoundaryContinuation.initial (OpenSplitController.program d) false h.rootId .start)
      CachedObservedComponent.rootId CachedObservedComponent.observations header last highId rfl
      tree.rootRecord.1 finalComponent.tree.rootRecord.1 entryBits finalBits cached cachedCurrent cachedAtRoot cachedValid cachedHeader
      target selected _ returned loadedOrder loadedUnique
  have retained : CachedRootOperation.RetainedMetadata Prod.fst finalComponent.tree.rootRecord.1 cached.tree actualConfig.tree := by
    simpa only [EnclosingPacketOperation.output,PacketPrefixTransfer.output_root_id] using metadata
  exact ⟨right,high,highId,terminalId,taggedTail,finalForest,finalConfig,finalComponent,
    target,observed,total,actualConfig,reached,highKey,rightClean,rightMarked,splitWitness,tailEq,
    actual,cacheErases,reachedErases,finalLocated,finalHeader,cacheValid,retained,
    ids,sourceLeaves,finalRep,finalUnique,finalAssembly,presence,componentErases,returned,globalIds,
    finalPhysical,finalReserved,finalValid,order,anchors,by omega⟩

end TangoSquared.Paper20261030.SecondaryDecomposition.ObservedPreparedExposure
