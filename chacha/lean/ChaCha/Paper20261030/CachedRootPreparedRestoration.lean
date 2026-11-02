import ChaCha.Paper20261030.CachedReachedRootedOperation
import ChaCha.Paper20261030.RootPreparedSplitWitnesses

set_option autoImplicit false

/-! Cached shared-tree restoration for the minimum-depth head switch.
Both source routines omit the old-prefix join. The enclosing prefix,
physical parent repair, reached root, and refreshed root cache are handled
by the same shared compiler as in the interior case. -/

namespace ChaCha.Paper20261030.SecondaryDecomposition.CachedRootPreparedRestoration

open ColoredStorage SourcePointer Structural PhysicalForestMetadata MultiSourceProgram
open Auxiliary AuxiliaryComponent BoundaryObservations PathDecomposition
open LocalComponentForestCompiler LocalComponentCompiler ForestConnector.ThreeColors
open EnclosedRootedComponentExecution (Packet Cell)
open CachedRootedComponentExecution (CachedCell)

variable {β ι η G : Type*} [DecidableEq ι] [DecidableEq η] [DecidableEq G]

local instance cachedRootPreparedRestorationColorOrder : LinearOrder (Option Bool) :=
  inferInstanceAs (LinearOrder (WithBot Bool))

theorem sentinel (markerId : ι) {a b : Nat} (reference : DepthTree a b) (preferences : DepthSplit → Bool)
    (d : Nat) (depthValid : a ≤ d ∧ d ≤ b)
    (prepared : (Secondary.decodeDepth reference preferences).terminal = d)
    (old right : AuxiliaryComponent Nat Nat (Tagged Payload))
    (oldRep : Represents followsRight (suffixSource reference preferences d depthValid) old)
    (high : Cached) (split : PreparedSplitWitnesses.Sentinel old d right high)
    (color : Nat → Option Bool) (decorated : Source Nat (η × Cached)) (erases : decorated.mapRecords Prod.snd = .fork high (terminalLeaf d) right.tree)
    (logicalUnique : (decorated.inventory Prod.fst).Nodup)
    (forest : TaggedForest (Option Bool) Nat (LocalColoredCompiler.LogicalRecord Cached η (Option Bool)) ι)
    (represented : ProjectionForest.Represents color ⟨annotate Prod.fst color none decorated,[]⟩ (erase forest))
    (physicalUnique : Unique forest) (headerKey : Nat) (payload : Option Bool → Nat → Source β (Packet Nat Cached ι η))
    (config : Configuration (Option Bool) β (Packet Nat Cached ι η))
    (assembled : ForestConnector.assemble (representation none wingOrientation headerKey payload forest)
      (layout (representation none wingOrientation headerKey payload forest)) = some config)
    (current : Cursor β (Cell Nat Cached ι η)) (saved : Packet Nat Cached ι η)
    (view : current.focus.mapRecords Prod.snd = config.tree.setRoot (saved ++ config.tree.rootRecord))
    (global : Configuration (Sum (Option Bool) G) β (Cell Nat Cached ι η))
    (valid : WellFormed global) (physical : CanonicalComponentUniqueness.Valid markerId global.tree)
    (reserved : markerId ∉ global.tree.inventory Prod.fst)
    (entry : Sum (Option Bool) G) (entryRep : MultiSourceSingleCursor.Represents entry current global)
    (header : PrimaryHeaderController.Header η) (bottom : Int) (start : Nat)
    (headerRep : PrimaryHeaderController.Represents header bottom start decorated forest headerKey payload)
    (cached : Configuration (Sum (Option Bool) G) β (CachedCell Nat Cached ι η))
    (cachedErases : cached.mapRecords Prod.fst = global)
    (cachedCurrent : Cursor β (CachedCell Nat Cached ι η))
    (cachedAtRoot : MultiSourceSingleCursor.Represents entry cachedCurrent cached)
    (cachedHeader : cachedCurrent.focus.rootRecord.2 = some header) :
    ∃ (out : AuxiliaryComponent Nat Nat (Tagged Payload)) (target : Source Nat (η × Cached)), ∃ finalForest finalConfig,
      ∃ (finalComponent : Configuration (Option Bool) β (Cell Nat Cached ι η)), ∃ actualConfig reads cost,
      ∃ reached : Cursor β (CachedCell Nat Cached ι η),
      Represents followsRight (suffixSource reference preferences d depthValid) out ∧
      Run (CachedRootedComponentExecution.program entry saved.length (!current.ancestors.isEmpty) (fun _ => HeadRestoreController.program false) (fun _ => HeadRestoreController.initial false))
        (.first .start) cached (.second (some (header,target.rootRecord.1,.inl none)) (some .done)) actualConfig reads cost ∧
      target.mapRecords Prod.snd = closed out ∧ target.inventory Prod.fst = decorated.inventory Prod.fst ∧
      ProjectionForest.Represents color ⟨annotate Prod.fst color none target,[]⟩ (erase finalForest) ∧ Unique finalForest ∧
      ForestConnector.assemble (representation none wingOrientation headerKey payload finalForest)
        (layout (representation none wingOrientation headerKey payload finalForest)) = some finalConfig ∧
      (∀ q, (representation none wingOrientation headerKey payload finalForest q).isSome =
        (representation none wingOrientation headerKey payload forest q).isSome) ∧
      finalComponent.mapRecords Prod.snd = finalConfig ∧
      reached.mapRecords Prod.fst = EnclosingPacketOperation.output saved current.focus.rootRecord.1 ⟨finalComponent.tree,current.ancestors⟩ ∧
      MultiSourceSingleCursor.Represents (.inl none) (PrimaryHeaderRefresh.refreshed header target.rootRecord.1 reached) actualConfig ∧
      (PrimaryHeaderRefresh.refreshed header target.rootRecord.1 reached).focus.rootRecord.2 = some {header with rootId := target.rootRecord.1} ∧
      (actualConfig.mapRecords Prod.fst).tree.inventory Prod.fst = global.tree.inventory Prod.fst ∧
      CanonicalComponentUniqueness.Valid markerId (actualConfig.mapRecords Prod.fst).tree ∧
      markerId ∉ (actualConfig.mapRecords Prod.fst).tree.inventory Prod.fst ∧ WellFormed actualConfig ∧
      CachedRootOperation.RetainedMetadata Prod.fst finalComponent.tree.rootRecord.1 cached.tree actualConfig.tree ∧
      (actualConfig.mapRecords Prod.fst).tree.inorderLabels Prod.fst = global.tree.inorderLabels Prod.fst ∧
      (∀ extra : G, fingerLabel Prod.fst (actualConfig.mapRecords Prod.fst) (.inr extra) = fingerLabel Prod.fst global (.inr extra)) ∧
      PrimaryHeaderController.Represents {header with rootId := target.rootRecord.1} bottom start target finalForest headerKey payload ∧
      cost ≤ 1896960*(2100*Nat.clog 2 ((LocalReferences.depthReference reference).height+1)+310)+45 := by
  obtain ⟨out,outRep,sourceReads,sourceCost,sourceRun,sourceBound⟩ :=
    PreparedSplitWitnesses.sentinel_restore reference preferences d depthValid prepared old right oldRep high split []
  obtain ⟨target,finalForest,finalConfig,finalComponent,actualConfig,reads,cost,reached,actual,targetErases,sourceIds,
    finalRep,finalUnique,finalAssembly,presence,componentErases,reachedErases,finalLocated,finalHeader,
    globalIds,finalPhysical,finalReserved,finalValid,metadata,order,anchors,finalCacheRep,bound⟩ :=
    CachedReachedRootedOperation.execute markerId (HeadRestoreController.program false) (HeadRestoreController.initial false) .done
      _ (closed out) sourceReads sourceCost sourceRun color decorated erases logicalUnique forest represented physicalUnique headerKey payload
      config assembled current saved view global valid physical reserved entry entryRep header bottom start headerRep
      cached cachedErases cachedCurrent cachedAtRoot cachedHeader
  exact ⟨out,target,finalForest,finalConfig,finalComponent,actualConfig,reads,cost,reached,outRep,actual,targetErases,sourceIds,
    finalRep,finalUnique,finalAssembly,presence,componentErases,reachedErases,finalLocated,finalHeader,
    globalIds,finalPhysical,finalReserved,finalValid,metadata,order,anchors,finalCacheRep,by omega⟩

theorem active (markerId : ι) {a b : Nat} (reference : DepthTree a b) (oldPreferences incomingPreferences : DepthSplit → Bool)
    (preparedOld : (Secondary.decodeDepth reference oldPreferences).terminal = a)
    (preparedIncoming : (Secondary.decodeDepth reference incomingPreferences).terminal = a)
    (old right : AuxiliaryComponent Nat Nat (Tagged Payload))
    (oldRep : Represents followsRight (suffixSource reference incomingPreferences a ⟨le_rfl,Secondary.reference_bounds reference⟩) old)
    (high : Cached) (split : PreparedSplitWitnesses.Sentinel old a right high)
    (color : Nat → Option Bool) (decorated : Source Nat (η × Cached)) (erases : decorated.mapRecords Prod.snd = .fork high (terminalLeaf a) right.tree)
    (logicalUnique : (decorated.inventory Prod.fst).Nodup)
    (forest : TaggedForest (Option Bool) Nat (LocalColoredCompiler.LogicalRecord Cached η (Option Bool)) ι)
    (represented : ProjectionForest.Represents color ⟨annotate Prod.fst color none decorated,[]⟩ (erase forest))
    (physicalUnique : Unique forest) (headerKey : Nat) (payload : Option Bool → Nat → Source β (Packet Nat Cached ι η))
    (config : Configuration (Option Bool) β (Packet Nat Cached ι η))
    (assembled : ForestConnector.assemble (representation none wingOrientation headerKey payload forest)
      (layout (representation none wingOrientation headerKey payload forest)) = some config)
    (current : Cursor β (Cell Nat Cached ι η)) (saved : Packet Nat Cached ι η)
    (view : current.focus.mapRecords Prod.snd = config.tree.setRoot (saved ++ config.tree.rootRecord))
    (global : Configuration (Sum (Option Bool) G) β (Cell Nat Cached ι η))
    (valid : WellFormed global) (physical : CanonicalComponentUniqueness.Valid markerId global.tree)
    (reserved : markerId ∉ global.tree.inventory Prod.fst)
    (entry : Sum (Option Bool) G) (entryRep : MultiSourceSingleCursor.Represents entry current global)
    (header : PrimaryHeaderController.Header η) (bottom : Int) (start : Nat)
    (headerRep : PrimaryHeaderController.Represents header bottom start decorated forest headerKey payload)
    (cached : Configuration (Sum (Option Bool) G) β (CachedCell Nat Cached ι η))
    (cachedErases : cached.mapRecords Prod.fst = global)
    (cachedCurrent : Cursor β (CachedCell Nat Cached ι η))
    (cachedAtRoot : MultiSourceSingleCursor.Represents entry cachedCurrent cached)
    (cachedHeader : cachedCurrent.focus.rootRecord.2 = some header) :
    ∃ (out : AuxiliaryComponent Nat Nat (Tagged Payload)) (target : Source Nat (η × Cached)), ∃ finalForest finalConfig,
      ∃ (finalComponent : Configuration (Option Bool) β (Cell Nat Cached ι η)), ∃ actualConfig reads cost,
      ∃ reached : Cursor β (CachedCell Nat Cached ι η),
      Represents followsRight (source reference (Secondary.spliceBits a oldPreferences incomingPreferences)) out ∧
      Run (CachedRootedComponentExecution.program entry saved.length (!current.ancestors.isEmpty) (fun _ => HeadRestoreController.program false) (fun _ => HeadRestoreController.initial false))
        (.first .start) cached (.second (some (header,target.rootRecord.1,.inl none)) (some .done)) actualConfig reads cost ∧
      target.mapRecords Prod.snd = closed out ∧ target.inventory Prod.fst = decorated.inventory Prod.fst ∧
      ProjectionForest.Represents color ⟨annotate Prod.fst color none target,[]⟩ (erase finalForest) ∧ Unique finalForest ∧
      ForestConnector.assemble (representation none wingOrientation headerKey payload finalForest)
        (layout (representation none wingOrientation headerKey payload finalForest)) = some finalConfig ∧
      (∀ q, (representation none wingOrientation headerKey payload finalForest q).isSome =
        (representation none wingOrientation headerKey payload forest q).isSome) ∧
      finalComponent.mapRecords Prod.snd = finalConfig ∧
      reached.mapRecords Prod.fst = EnclosingPacketOperation.output saved current.focus.rootRecord.1 ⟨finalComponent.tree,current.ancestors⟩ ∧
      MultiSourceSingleCursor.Represents (.inl none) (PrimaryHeaderRefresh.refreshed header target.rootRecord.1 reached) actualConfig ∧
      (PrimaryHeaderRefresh.refreshed header target.rootRecord.1 reached).focus.rootRecord.2 = some {header with rootId := target.rootRecord.1} ∧
      (actualConfig.mapRecords Prod.fst).tree.inventory Prod.fst = global.tree.inventory Prod.fst ∧
      CanonicalComponentUniqueness.Valid markerId (actualConfig.mapRecords Prod.fst).tree ∧
      markerId ∉ (actualConfig.mapRecords Prod.fst).tree.inventory Prod.fst ∧ WellFormed actualConfig ∧
      CachedRootOperation.RetainedMetadata Prod.fst finalComponent.tree.rootRecord.1 cached.tree actualConfig.tree ∧
      (actualConfig.mapRecords Prod.fst).tree.inorderLabels Prod.fst = global.tree.inorderLabels Prod.fst ∧
      (∀ extra : G, fingerLabel Prod.fst (actualConfig.mapRecords Prod.fst) (.inr extra) = fingerLabel Prod.fst global (.inr extra)) ∧
      PrimaryHeaderController.Represents {header with rootId := target.rootRecord.1} bottom start target finalForest headerKey payload ∧
      cost ≤ 1896960*(2100*Nat.clog 2 ((LocalReferences.depthReference reference).height+1)+310)+45 := by
  obtain ⟨out,outRep,sourceReads,sourceCost,sourceRun,sourceBound⟩ :=
    PreparedSplitWitnesses.root_active_restore reference oldPreferences incomingPreferences preparedOld preparedIncoming old right oldRep high split []
  obtain ⟨target,finalForest,finalConfig,finalComponent,actualConfig,reads,cost,reached,actual,targetErases,sourceIds,
    finalRep,finalUnique,finalAssembly,presence,componentErases,reachedErases,finalLocated,finalHeader,
    globalIds,finalPhysical,finalReserved,finalValid,metadata,order,anchors,finalCacheRep,bound⟩ :=
    CachedReachedRootedOperation.execute markerId (HeadRestoreController.program false) (HeadRestoreController.initial false) .done
      _ (closed out) sourceReads sourceCost sourceRun color decorated erases logicalUnique forest represented physicalUnique headerKey payload
      config assembled current saved view global valid physical reserved entry entryRep header bottom start headerRep
      cached cachedErases cachedCurrent cachedAtRoot cachedHeader
  exact ⟨out,target,finalForest,finalConfig,finalComponent,actualConfig,reads,cost,reached,outRep,actual,targetErases,sourceIds,
    finalRep,finalUnique,finalAssembly,presence,componentErases,reachedErases,finalLocated,finalHeader,
    globalIds,finalPhysical,finalReserved,finalValid,metadata,order,anchors,finalCacheRep,by omega⟩

end ChaCha.Paper20261030.SecondaryDecomposition.CachedRootPreparedRestoration
