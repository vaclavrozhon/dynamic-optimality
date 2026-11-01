import TangoSquared.Paper20261030.CachedPreparedRestoration
import TangoSquared.Paper20261030.CachedCanonicalIncomingUpdate

set_option autoImplicit false

/-! Executed dormant restoration preserves the enclosing active component.
Its boundary payload and physical routing ids are updated to the restored
child, and the parked active root retains its cache. This supplies the
representation required to begin active restoration. -/

namespace TangoSquared.Paper20261030.SecondaryDecomposition.DormantRestorationPreservesActive

open ColoredStorage SourcePointer Structural PhysicalForestMetadata MultiSourceProgram
open Auxiliary AuxiliaryComponent BoundaryObservations PathDecomposition
open LocalComponentForestCompiler LocalComponentCompiler ForestConnector.ThreeColors
open EnclosedRootedComponentExecution (Packet Cell)
open CachedRootedComponentExecution (CachedCell)

variable {β ι η G : Type*} [DecidableEq ι] [DecidableEq η] [DecidableEq G]

local instance dormantRestorationActiveColorOrder : LinearOrder (Option Bool) :=
  inferInstanceAs (LinearOrder (WithBot Bool))

theorem execute (markerId : ι) {a b : Nat} (reference : DepthTree a b) (preferences : DepthSplit → Bool)
    (d : Nat) (depthValid : a ≤ d ∧ d ≤ b) (lower : a < d)
    (prepared : (Secondary.decodeDepth reference preferences).terminal = d)
    (old left right : AuxiliaryComponent Nat Nat (Tagged Payload))
    (oldRep : Represents followsRight (source reference preferences) old)
    (low high : Cached) (split : PreparedSplitWitnesses.Active old d left right low high)
    (color : Nat → Option Bool) (decorated : Source Nat (η × Cached)) (erases : decorated.mapRecords Prod.snd = .fork high (terminalLeaf d) right.tree)
    (logicalUnique : (decorated.inventory Prod.fst).Nodup)
    (forest : TaggedForest (Option Bool) Nat (LocalColoredCompiler.LogicalRecord Cached η (Option Bool)) ι)
    (represented : ProjectionForest.Represents color ⟨annotate Prod.fst color none decorated,[]⟩ (erase forest))
    (physicalUnique : Unique forest) (headerKey : Nat) (payload : Option Bool → Nat → Source β (Packet Nat Cached ι η))
    (config : Configuration (Option Bool) β (Packet Nat Cached ι η))
    (assembled : ForestConnector.assemble (representation none wingOrientation headerKey payload forest)
      (layout (representation none wingOrientation headerKey payload forest)) = some config)
    (current : Cursor β (Cell Nat Cached ι η)) (saved : Packet Nat Cached ι η)
    (prefixLength : saved.length = 2) (proper : current.ancestors ≠ [])
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
    (cachedHeader : cachedCurrent.focus.rootRecord.2 = some header)
    (activeColor : Nat → Option Bool) (activeDecorated : Source Nat (η × Cached))
    (activeForest : TaggedForest (Option Bool) Nat (LocalColoredCompiler.LogicalRecord Cached η (Option Bool)) ι)
    (activeRep : ProjectionForest.Represents activeColor ⟨annotate Prod.fst activeColor none activeDecorated,[]⟩ (erase activeForest))
    (activeUnique : Unique activeForest) (activeHeaderKey : Nat)
    (activePayload : Option Bool → Nat → Source β (List (Option (PhysicalDatum Nat Cached ι η (Option Bool)))))
    (activeConfig : MultiSourceProgram.Configuration (Option Bool) β (List (Option (PhysicalDatum Nat Cached ι η (Option Bool)))))
    (activeAssembly : ForestConnector.assemble (representation none wingOrientation activeHeaderKey activePayload activeForest)
      (layout (representation none wingOrientation activeHeaderKey activePayload activeForest)) = some activeConfig)
    (activeTree : Source β (Cell Nat Cached ι η)) (activeTreeErases : activeTree.mapRecords Prod.snd = activeConfig.tree)
    (activeOutside : List (Frame β (Cell Nat Cached ι η))) (activeSaved : List (Option (PhysicalDatum Nat Cached ι η (Option Bool)))) (activeOld : ι)
    (activeNeutral : PacketParentNeutral.Neutral activeSaved)
    (activeAnchor : G) (activeCurrent : Cursor β (CachedCell Nat Cached ι η))
    (activeLocated : MultiSourceSingleCursor.Represents (.inr activeAnchor) activeCurrent cached)
    (activeErases : activeCurrent.mapRecords Prod.fst = EnclosingPacketOperation.output activeSaved activeOld ⟨activeTree,activeOutside⟩)
    (member : d ∈ activeDecorated.shape.leaves) (real : activeColor d ≠ none)
    (attached : activePayload (activeColor d) d = config.tree)
    (distinct : global.tree.shape.leaves.Nodup) :
    ∃ (out : AuxiliaryComponent Nat Nat (Tagged Payload)) (target : Source Nat (η × Cached)), ∃ finalForest finalConfig,
      ∃ (finalComponent : Configuration (Option Bool) β (Cell Nat Cached ι η)), ∃ actualConfig reads cost,
      ∃ reached : Cursor β (CachedCell Nat Cached ι η),
      ∃ updatedActiveForest updatedActiveConfig returnedActive,
      Represents followsRight (suffixSource reference preferences d depthValid) out ∧
      Run (CachedRootedComponentExecution.program entry 2 true (fun _ => HeadRestoreController.program false) (fun _ => HeadRestoreController.initial false))
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
      cost ≤ 1896960*(2100*Nat.clog 2 ((LocalReferences.depthReference reference).height+1)+310)+45 ∧
      let newPayload := Function.update activePayload (activeColor d)
        (Function.update (activePayload (activeColor d)) d finalConfig.tree)
      PhysicalForestMetadata.erase updatedActiveForest = erase activeForest ∧
      ProjectionForest.Represents activeColor ⟨annotate Prod.fst activeColor none activeDecorated,[]⟩ (erase updatedActiveForest) ∧
      Unique updatedActiveForest ∧
      ForestConnector.assemble (representation none wingOrientation activeHeaderKey newPayload updatedActiveForest)
        (layout (representation none wingOrientation activeHeaderKey newPayload updatedActiveForest)) = some updatedActiveConfig ∧
      (∀ q, (representation none wingOrientation activeHeaderKey newPayload updatedActiveForest q).isSome =
        (representation none wingOrientation activeHeaderKey activePayload activeForest q).isSome) ∧
      MultiSourceSingleCursor.Represents (.inr activeAnchor) returnedActive actualConfig ∧
      (returnedActive.focus.mapRecords Prod.fst).mapRecords Prod.snd =
        updatedActiveConfig.tree.setRoot
          (PacketPrefixTransfer.reidentify activeTree.rootRecord.1 activeSaved ++ updatedActiveConfig.tree.rootRecord) ∧
      returnedActive.focus.rootRecord.1.1 = activeCurrent.focus.rootRecord.1.1 ∧
      returnedActive.focus.rootRecord.2 = activeCurrent.focus.rootRecord.2 ∧
      (returnedActive.mapRecords Prod.fst).ancestors = (activeCurrent.mapRecords Prod.fst).ancestors := by
  obtain ⟨out,target,finalForest,finalConfig,finalComponent,actualConfig,reads,cost,reached,outRep,actual,targetErases,sourceIds,
    finalRep,finalUnique,finalAssembly,presence,componentErases,reachedErases,finalLocated,finalHeader,
    globalIds,finalPhysical,finalReserved,finalValid,metadata,order,anchors,finalCacheRep,bound⟩ :=
    CachedPreparedRestoration.dormant markerId reference preferences d depthValid lower prepared old left right oldRep low high split
      color decorated erases logicalUnique forest represented physicalUnique headerKey payload config assembled current saved view
      global valid physical reserved entry entryRep header bottom start headerRep cached cachedErases cachedCurrent cachedAtRoot cachedHeader
  have parent : (!current.ancestors.isEmpty) = true := by
    cases found : current.ancestors with
    | nil => exact False.elim (proper found)
    | cons => rfl
  rw [prefixLength,parent] at actual
  have prefixEq : current.focus.rootRecord.2.take 2 = saved := by
    rw [PacketPrefixErasure.root_packet current saved config.tree view]
    exact List.take_left' prefixLength
  have payloadAt : CanonicalRetainedPayloadHandoff.PayloadAt (activePayload (activeColor d) d) current := by
    unfold CanonicalRetainedPayloadHandoff.PayloadAt
    rw [attached,view]
    cases config.tree <;> rfl
  have actualReturned : MultiSourceSingleCursor.Represents (.inl none)
      (EnclosingPacketOperation.output (current.focus.rootRecord.2.take 2) current.focus.rootRecord.1
        ⟨finalComponent.tree,current.ancestors⟩) (actualConfig.mapRecords Prod.fst) := by
    have erasedReturn := finalLocated.mapRecords Prod.fst
    rw [PrimaryHeaderRefresh.refreshed_erases,reachedErases] at erasedReturn
    rw [prefixEq]
    exact erasedReturn
  have actualEntered : MultiSourceSingleCursor.Represents entry current (cached.mapRecords Prod.fst) := cachedErases.symm ▸ entryRep
  have parked : fingerLabel Prod.fst (actualConfig.mapRecords Prod.fst) (.inr activeAnchor) =
      fingerLabel Prod.fst (cached.mapRecords Prod.fst) (.inr activeAnchor) := by
    rw [cachedErases]
    exact anchors activeAnchor
  obtain ⟨updatedActiveForest,updatedActiveConfig,returnedActive,updatedErases,updatedRep,updatedUnique,updatedAssembly,
    updatedPresence,activeReturned,updatedView,activeIdentity,activeCache,activeAncestors⟩ :=
    CanonicalIncomingComponentUpdate.cached markerId activeColor activeDecorated activeForest activeRep activeUnique
      activeHeaderKey activePayload activeConfig activeAssembly activeTree activeTreeErases activeOutside activeSaved activeOld activeNeutral
      cached actualConfig entry (.inl none) (.inr activeAnchor) activeCurrent activeLocated activeErases
      (cachedErases.symm ▸ physical) (cachedErases.symm ▸ distinct) current actualEntered d member real payloadAt
      finalComponent.tree actualReturned metadata parked finalPhysical
  have componentTree : finalComponent.tree.mapRecords Prod.snd = finalConfig.tree := congrArg Configuration.tree componentErases
  rw [componentTree] at updatedAssembly updatedPresence
  exact ⟨out,target,finalForest,finalConfig,finalComponent,actualConfig,reads,cost,reached,updatedActiveForest,updatedActiveConfig,returnedActive,
    outRep,actual,targetErases,sourceIds,finalRep,finalUnique,finalAssembly,presence,componentErases,reachedErases,finalLocated,finalHeader,
    globalIds,finalPhysical,finalReserved,finalValid,metadata,order,anchors,finalCacheRep,bound,
    updatedErases,updatedRep,updatedUnique,updatedAssembly,updatedPresence,activeReturned,updatedView,activeIdentity,activeCache,activeAncestors⟩

end TangoSquared.Paper20261030.SecondaryDecomposition.DormantRestorationPreservesActive
