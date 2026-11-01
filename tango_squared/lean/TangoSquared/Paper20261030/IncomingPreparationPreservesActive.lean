import TangoSquared.Paper20261030.CachedIncomingPreparation
import TangoSquared.Paper20261030.CachedCanonicalIncomingUpdate

set_option autoImplicit false

/-! Executed incoming preparation in a shared canonical active component.
The controller reads the incoming cache and boundary records, prepares
that component, and returns both its canonical output and the enclosing
active component at its parked finger with its original cache. -/

namespace TangoSquared.Paper20261030.SecondaryDecomposition.ObservedPreparedExposure

open ColoredStorage SourcePointer Structural PhysicalForestMetadata Auxiliary AuxiliaryComponent BoundaryObservations PathDecomposition
open LocalComponentForestCompiler LocalComponentCompiler ForestConnector.ThreeColors MultiSourceProgram
open PreparedExposureExecution (Logical Datum)

variable {β ι η G : Type*} [DecidableEq ι] [DecidableEq η] [DecidableEq G]

local instance incomingPreparationActiveColorOrder : LinearOrder (Option Bool) := inferInstanceAs (LinearOrder (WithBot Bool))

theorem incoming_cached_with_active (markerId : ι) {a b : Nat} (reference : DepthTree a b) (preferences : DepthSplit → Bool)
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
    (current : Cursor β (ReentryCell ι η)) (saved : List (Option (Datum ι η)))
    (prefixLength : saved.length = 2) (proper : current.ancestors ≠ [])
    (view : current.focus.mapRecords Prod.snd = config.tree.setRoot (saved++config.tree.rootRecord))
    (global : MultiSourceProgram.Configuration (Sum (Option Bool) G) β (ReentryCell ι η))
    (wellFormed : MultiSourceProgram.WellFormed global)
    (physical : CanonicalComponentUniqueness.Valid markerId global.tree)
    (reserved : markerId ∉ global.tree.inventory Prod.fst)
    (entry : Sum (Option Bool) G)
    (entryRep : MultiSourceSingleCursor.Represents entry current global)
    (header : PrimaryHeaderController.Header η)
    (rootId : header.rootId = decorated.rootRecord.1)
    (leftWing : header.leftWing = (representation none wingOrientation headerKey payload forest (some true)).isSome)
    (rightWing : header.rightWing = (representation none wingOrientation headerKey payload forest (some false)).isSome)
    (cached : MultiSourceProgram.Configuration (Sum (Option Bool) G) β (CachedCell ι η))
    (cachedErases : cached.mapRecords Prod.fst = global)
    (cachedCurrent : Cursor β (CachedCell ι η))
    (cachedAtRoot : MultiSourceSingleCursor.Represents entry cachedCurrent cached)
    (cachedHeader : cachedCurrent.focus.rootRecord.2 = some header)
    (activeColor : Nat → Option Bool) (activeDecorated : Source Nat (η × Cached))
    (activeForest : TaggedForest (Option Bool) Nat (Logical η) ι)
    (activeRep : ProjectionForest.Represents activeColor ⟨annotate Prod.fst activeColor none activeDecorated,[]⟩ (erase activeForest))
    (activeUnique : Unique activeForest) (activeHeaderKey : Nat)
    (activePayload : Option Bool → Nat → Source β (List (Option (Datum ι η))))
    (activeConfig : MultiSourceProgram.Configuration (Option Bool) β (List (Option (Datum ι η))))
    (activeAssembly : ForestConnector.assemble (representation none wingOrientation activeHeaderKey activePayload activeForest)
      (layout (representation none wingOrientation activeHeaderKey activePayload activeForest)) = some activeConfig)
    (activeTree : Source β (ReentryCell ι η)) (activeTreeErases : activeTree.mapRecords Prod.snd = activeConfig.tree)
    (activeOutside : List (Frame β (ReentryCell ι η))) (activeSaved : List (Option (Datum ι η))) (activeOld : ι)
    (activeNeutral : PacketParentNeutral.Neutral activeSaved)
    (activeAnchor : G) (activeCurrent : Cursor β (CachedCell ι η))
    (activeLocated : MultiSourceSingleCursor.Represents (.inr activeAnchor) activeCurrent cached)
    (activeErases : activeCurrent.mapRecords Prod.fst = EnclosingPacketOperation.output activeSaved activeOld ⟨activeTree,activeOutside⟩)
    (member : d ∈ activeDecorated.shape.leaves) (real : activeColor d ≠ none)
    (attached : activePayload (activeColor d) d = config.tree)
    (distinct : global.tree.shape.leaves.Nodup) :
    ∃ (right : AuxiliaryComponent Nat Nat (Tagged Payload)) (high : Cached),
      ∃ highId terminalId, ∃ taggedTail : Source Nat (η × Cached), ∃ finalForest finalConfig,
      ∃ (finalComponent : MultiSourceProgram.Configuration (Option Bool) β (ReentryCell ι η)), ∃ target reads cost, ∃ actualConfig, ∃ reached : Cursor β (CachedCell ι η),
      ∃ updatedActiveForest updatedActiveConfig returnedActive,
      high.2.1 = d ∧ Clean right.core ∧ MarkedPorts right ∧
      PreparedSplitWitnesses.Sentinel component d right high ∧ taggedTail.mapRecords Prod.snd = right.tree ∧
      MultiSourceProgram.Run
        (CachedObservedComponent.program entry 2 true false
          (fun _ => OpenSplitController.program d) (fun _ => .start))
        (.first .start) cached
        (.second (some (header,highId,.inl none,some
          (BoundaryReadController.sentinelResult Prod.fst color (highId,high)
            (terminalId,(terminalLeaf d).rootRecord) d taggedTail))) (some .done)) actualConfig reads cost ∧
      actualConfig.mapRecords Prod.fst = target ∧
      reached.mapRecords Prod.fst = EnclosingPacketOperation.output saved current.focus.rootRecord.1 ⟨finalComponent.tree,current.ancestors⟩ ∧
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
        (EnclosingPacketOperation.output saved current.focus.rootRecord.1 ⟨finalComponent.tree,current.ancestors⟩) target ∧
      target.tree.inventory Prod.fst = global.tree.inventory Prod.fst ∧
      CanonicalComponentUniqueness.Valid markerId target.tree ∧
      markerId ∉ target.tree.inventory Prod.fst ∧ MultiSourceProgram.WellFormed target ∧
      target.tree.inorderLabels Prod.fst = global.tree.inorderLabels Prod.fst ∧
      (∀ extra : G, MultiSourceProgram.fingerLabel Prod.fst target (.inr extra) =
        MultiSourceProgram.fingerLabel Prod.fst global (.inr extra)) ∧
      cost ≤ 4*(474240*(40110*Nat.clog 2 ((LocalReferences.depthReference reference).height+1)+2)+49920)+45 ∧
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
  obtain ⟨right,high,highId,terminalId,taggedTail,finalForest,finalConfig,finalComponent,
    target,reads,cost,actualConfig,reached,highKey,rightClean,rightMarked,splitWitness,tailEq,
    actual,cacheErases,reachedErases,finalLocated,finalHeader,cacheValid,retained,
    sourceIds,sourceLeaves,finalRep,finalUnique,finalAssembly,presence,componentErases,returned,globalIds,
    finalPhysical,finalReserved,finalValid,order,anchors,bound⟩ :=
    incoming_cached markerId reference preferences d valid terminal upper component represented color decorated erases logicalUnique
      forest forestRep physicalUnique headerKey payload config assembled current saved prefixLength proper view global wellFormed physical reserved
      entry entryRep header rootId leftWing rightWing cached cachedErases cachedCurrent cachedAtRoot cachedHeader
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
    rw [prefixEq,cacheErases]
    exact returned
  have actualEntered : MultiSourceSingleCursor.Represents entry current (cached.mapRecords Prod.fst) := by
    rw [cachedErases]
    exact entryRep
  have parked : fingerLabel Prod.fst (actualConfig.mapRecords Prod.fst) (.inr activeAnchor) =
      fingerLabel Prod.fst (cached.mapRecords Prod.fst) (.inr activeAnchor) := by
    rw [cacheErases,cachedErases]
    exact anchors activeAnchor
  obtain ⟨updatedActiveForest,updatedActiveConfig,returnedActive,updatedErases,updatedRep,updatedUnique,updatedAssembly,
    updatedPresence,activeReturned,updatedView,activeIdentity,activeCache,activeAncestors⟩ :=
    CanonicalIncomingComponentUpdate.cached markerId activeColor activeDecorated activeForest activeRep activeUnique
      activeHeaderKey activePayload activeConfig activeAssembly activeTree activeTreeErases activeOutside activeSaved activeOld activeNeutral
      cached actualConfig entry (.inl none) (.inr activeAnchor) activeCurrent activeLocated activeErases
      (cachedErases.symm ▸ physical) (cachedErases.symm ▸ distinct) current actualEntered d member real payloadAt
      finalComponent.tree actualReturned retained parked (cacheErases.symm ▸ finalPhysical)
  have componentTree : finalComponent.tree.mapRecords Prod.snd = finalConfig.tree := congrArg Configuration.tree componentErases
  rw [componentTree] at updatedAssembly updatedPresence
  exact ⟨right,high,highId,terminalId,taggedTail,finalForest,finalConfig,finalComponent,
    target,reads,cost,actualConfig,reached,updatedActiveForest,updatedActiveConfig,returnedActive,
    highKey,rightClean,rightMarked,splitWitness,tailEq,actual,cacheErases,reachedErases,finalLocated,finalHeader,cacheValid,retained,
    sourceIds,sourceLeaves,finalRep,finalUnique,finalAssembly,presence,componentErases,returned,globalIds,finalPhysical,finalReserved,
    finalValid,order,anchors,bound,updatedErases,updatedRep,updatedUnique,updatedAssembly,updatedPresence,
    activeReturned,updatedView,activeIdentity,activeCache,activeAncestors⟩

end TangoSquared.Paper20261030.SecondaryDecomposition.ObservedPreparedExposure
