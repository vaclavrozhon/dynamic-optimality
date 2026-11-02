import ChaCha.Paper20261030.CachedObservedPreparation
import ChaCha.Paper20261030.PacketPrefixErasure
import ChaCha.Paper20261030.CachedObservedComponent
import ChaCha.Paper20261030.CachedAnchorHandoff
import ChaCha.Paper20261030.AttachedPacketIdentifiers

set_option autoImplicit false

/-! Starting incoming preparation directly in the shared configuration
returned by active preparation. A proper real port has a two-datum
attachment. The stripping witness is ghost data; the executed cached
controller performs the actual read and removal, then repairs the parent
and returns with its newly read boundary records. -/

namespace ChaCha.Paper20261030.SecondaryDecomposition.ObservedPreparedExposure

open ColoredStorage SourcePointer Structural PhysicalForestMetadata Auxiliary AuxiliaryComponent BoundaryObservations PathDecomposition
open LocalComponentForestCompiler LocalComponentCompiler ForestConnector.ThreeColors MultiSourceProgram
open PreparedExposureExecution (Logical Datum)

variable {β ι η G : Type*} [DecidableEq ι] [DecidableEq η] [DecidableEq G]

local instance cachedIncomingPreparationColorOrder : LinearOrder (Option Bool) := inferInstanceAs (LinearOrder (WithBot Bool))

theorem incoming_cached (markerId : ι) {a b : Nat} (reference : DepthTree a b) (preferences : DepthSplit → Bool)
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
    (cachedHeader : cachedCurrent.focus.rootRecord.2 = some header) :
    ∃ (right : AuxiliaryComponent Nat Nat (Tagged Payload)) (high : Cached),
      ∃ highId terminalId, ∃ taggedTail : Source Nat (η × Cached), ∃ finalForest finalConfig,
      ∃ (finalComponent : MultiSourceProgram.Configuration (Option Bool) β (ReentryCell ι η)), ∃ target reads cost, ∃ actualConfig, ∃ reached : Cursor β (CachedCell ι η),
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
      cost ≤ 4*(474240*(40110*Nat.clog 2 ((LocalReferences.depthReference reference).height+1)+2)+49920)+45 := by
  let normalized := SubtreeMetadata.replacePayload current config.tree.rootRecord
  let raw := PacketPrefixErasure.stripped current config.tree.rootRecord global
  have split := PacketPrefixErasure.root_packet current saved config.tree view
  have rawRep := PacketPrefixErasure.represented entry current config.tree.rootRecord global entryRep
  have rawErases := PacketPrefixErasure.payload current saved config.tree view
  have rawValid := PacketPrefixErasure.wellFormed current config.tree.rootRecord global entryRep.1 wellFormed
  have rawPhysical := PacketPrefixErasure.physical markerId current saved config.tree.rootRecord global entryRep.1 split physical
  have ids := PacketPrefixErasure.inventory current config.tree.rootRecord global entryRep.1
  have rawReserved : markerId ∉ raw.tree.inventory Prod.fst := by
    rw [ids]
    exact reserved
  have attached : cached.mapRecords Prod.fst = MultiSourcePacketPrefix.attached saved normalized.focus current.ancestors raw := by
    rw [PacketPrefixErasure.reattach current saved config.tree.rootRecord global entryRep.1 split]
    exact cachedErases
  have parent : (!current.ancestors.isEmpty) = true := by
    cases found : current.ancestors with
    | nil => exact False.elim (proper found)
    | cons => rfl
  obtain ⟨right,high,highId,terminalId,taggedTail,finalForest,finalConfig,finalComponent,
    target,reads,cost,actualConfig,reached,highKey,rightClean,rightMarked,splitWitness,tailEq,
    actual,cacheErases,reachedErases,finalLocated,finalHeader,cacheValid,retained,
    sourceIds,sourceLeaves,finalRep,finalUnique,finalAssembly,presence,componentErases,returned,globalIds,
    finalPhysical,finalReserved,finalValid,order,anchors,bound⟩ :=
    sentinel_cached markerId reference preferences d valid terminal upper component represented color decorated erases logicalUnique
      forest forestRep physicalUnique headerKey payload config assembled normalized.focus rawErases current.ancestors raw rawValid rawPhysical rawReserved
      entry rawRep saved header rootId leftWing rightWing cached attached cachedCurrent cachedAtRoot cachedHeader
  rw [prefixLength,parent] at actual
  have outputId : normalized.focus.rootRecord.1 = current.focus.rootRecord.1 := PacketPrefixErasure.root_id current config.tree.rootRecord
  rw [outputId] at reachedErases returned
  have rawOrder := PacketPrefixErasure.inorder current config.tree.rootRecord global entryRep.1
  have rawAnchors := PacketPrefixErasure.fingerLabel current config.tree.rootRecord global entryRep.1
  exact ⟨right,high,highId,terminalId,taggedTail,finalForest,finalConfig,finalComponent,
    target,reads,cost,actualConfig,reached,highKey,rightClean,rightMarked,splitWitness,tailEq,
    actual,cacheErases,reachedErases,finalLocated,finalHeader,cacheValid,retained,
    sourceIds,sourceLeaves,finalRep,finalUnique,finalAssembly,presence,componentErases,returned,globalIds.trans ids,
    finalPhysical,finalReserved,finalValid,order.trans rawOrder,(fun extra => (anchors extra).trans (rawAnchors (.inr extra))),bound⟩

end ChaCha.Paper20261030.SecondaryDecomposition.ObservedPreparedExposure
