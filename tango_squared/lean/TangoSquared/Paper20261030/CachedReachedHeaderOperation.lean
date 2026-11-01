import TangoSquared.Paper20261030.CachedRootedComponent
import TangoSquared.Paper20261030.PacketPrefixErasure
import TangoSquared.Paper20261030.PrimaryHeaderRepresentationTransport

set_option autoImplicit false

/-! Dispatch a root-to-root source operation using the header actually
read at a reached component. The runtime family may compute a request
depth from the loaded bottom key. Prefix transfer, parent repair, and
final root-cache refresh are all charged operations. -/

namespace TangoSquared.Paper20261030.CachedReachedHeaderOperation

open ColoredStorage SourcePointer Structural PhysicalForestMetadata MultiSourceProgram
open LocalComponentForestCompiler LocalComponentCompiler ForestConnector.ThreeColors
open EnclosedRootedComponentExecution (Packet Cell)
open CachedRootedComponentExecution (CachedCell)

variable {α β ρ ι η G σ : Type*} [DecidableEq α] [DecidableEq ι] [DecidableEq η] [DecidableEq G]

local instance cachedReachedHeaderOperationColorOrder : LinearOrder (Option Bool) :=
  inferInstanceAs (LinearOrder (WithBot Bool))

theorem execute (markerId : ι) (source : PrimaryHeaderController.Header η → SourceLocalProgram.Program σ ρ)
    (initial : PrimaryHeaderController.Header η → σ) (header : PrimaryHeaderController.Header η) (last : σ) (before after : Source α ρ) (sourceReads : List ρ) (sourceCost : Nat)
    (run : SourceLocalProgram.Run (source header) (initial header) ⟨before,[]⟩ last ⟨after,[]⟩ sourceReads sourceCost)
    (color : α → Option Bool) (decorated : Source α (η × ρ)) (erases : decorated.mapRecords Prod.snd = before)
    (logicalUnique : (decorated.inventory Prod.fst).Nodup)
    (forest : TaggedForest (Option Bool) α (LocalColoredCompiler.LogicalRecord ρ η (Option Bool)) ι)
    (represented : ProjectionForest.Represents color ⟨annotate Prod.fst color none decorated,[]⟩ (erase forest))
    (physicalUnique : Unique forest) (headerKey : α) (payload : Option Bool → α → Source β (Packet α ρ ι η))
    (config : Configuration (Option Bool) β (Packet α ρ ι η))
    (assembled : ForestConnector.assemble (representation none wingOrientation headerKey payload forest)
      (layout (representation none wingOrientation headerKey payload forest)) = some config)
    (current : Cursor β (Cell α ρ ι η)) (saved : Packet α ρ ι η)
    (view : current.focus.mapRecords Prod.snd = config.tree.setRoot (saved ++ config.tree.rootRecord))
    (global : Configuration (Sum (Option Bool) G) β (Cell α ρ ι η))
    (valid : WellFormed global) (physical : CanonicalComponentUniqueness.Valid markerId global.tree)
    (reserved : markerId ∉ global.tree.inventory Prod.fst)
    (entry : Sum (Option Bool) G) (entryRep : MultiSourceSingleCursor.Represents entry current global)
    (bottom : Int) (start : Nat)
    (headerRep : PrimaryHeaderController.Represents header bottom start decorated forest headerKey payload)
    (cached : Configuration (Sum (Option Bool) G) β (CachedCell α ρ ι η))
    (cachedErases : cached.mapRecords Prod.fst = global)
    (cachedCurrent : Cursor β (CachedCell α ρ ι η))
    (cachedAtRoot : MultiSourceSingleCursor.Represents entry cachedCurrent cached)
    (cachedHeader : cachedCurrent.focus.rootRecord.2 = some header) :
    ∃ (target : Source α (η × ρ)), ∃ finalForest finalConfig,
      ∃ (finalComponent : Configuration (Option Bool) β (Cell α ρ ι η)), ∃ actualConfig reads cost,
      ∃ reached : Cursor β (CachedCell α ρ ι η),
      Run (CachedRootedComponentExecution.program entry saved.length (!current.ancestors.isEmpty) source initial)
        (.first .start) cached (.second (some (header,target.rootRecord.1,.inl none)) (some .done)) actualConfig reads cost ∧
      target.mapRecords Prod.snd = after ∧ target.inventory Prod.fst = decorated.inventory Prod.fst ∧
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
      cost ≤ 1896960*sourceCost+45 := by
  let normalized := SubtreeMetadata.replacePayload current config.tree.rootRecord
  let raw := PacketPrefixErasure.stripped current config.tree.rootRecord global
  have split := PacketPrefixErasure.root_packet current saved config.tree view
  have rawErases := PacketPrefixErasure.payload current saved config.tree view
  have rawRep := PacketPrefixErasure.represented entry current config.tree.rootRecord global entryRep
  have rawValid := PacketPrefixErasure.wellFormed current config.tree.rootRecord global entryRep.1 valid
  have rawPhysical := PacketPrefixErasure.physical markerId current saved config.tree.rootRecord global entryRep.1 split physical
  have ids := PacketPrefixErasure.inventory current config.tree.rootRecord global entryRep.1
  have rawReserved : markerId ∉ raw.tree.inventory Prod.fst := by rw [ids]; exact reserved
  have attached : cached.mapRecords Prod.fst = MultiSourcePacketPrefix.attached saved normalized.focus current.ancestors raw := by
    rw [PacketPrefixErasure.reattach current saved config.tree.rootRecord global entryRep.1 split]
    exact cachedErases
  obtain ⟨target,finalForest,finalConfig,finalComponent,actualConfig,reads,cost,reached,actual,targetErases,sourceIds,
    finalRep,finalUnique,finalAssembly,presence,componentErases,reachedErases,finalLocated,finalHeader,
    globalIds,finalPhysical,finalReserved,finalValid,metadata,order,anchors,bound⟩ :=
    CachedRootedComponentExecution.execute markerId source initial header color headerKey payload run
      decorated erases logicalUnique forest represented physicalUnique config assembled normalized.focus rawErases current.ancestors
      raw rawValid rawPhysical rawReserved entry rawRep saved headerRep.2.2.1 headerRep.2.2.2.1 headerRep.2.2.2.2
      cached attached cachedCurrent cachedAtRoot cachedHeader
  have outputId : normalized.focus.rootRecord.1 = current.focus.rootRecord.1 := PacketPrefixErasure.root_id current config.tree.rootRecord
  rw [outputId] at reachedErases
  have rawOrder := PacketPrefixErasure.inorder current config.tree.rootRecord global entryRep.1
  have rawAnchors := PacketPrefixErasure.fingerLabel current config.tree.rootRecord global entryRep.1
  exact ⟨target,finalForest,finalConfig,finalComponent,actualConfig,reads,cost,reached,actual,targetErases,sourceIds,
    finalRep,finalUnique,finalAssembly,presence,componentErases,reachedErases,finalLocated,finalHeader,
    globalIds.trans ids,finalPhysical,finalReserved,finalValid,metadata,order.trans rawOrder,
    (fun extra => (anchors extra).trans (rawAnchors (.inr extra))),
    PrimaryHeaderController.Represents.refresh header bottom start decorated target forest finalForest headerKey payload headerRep presence,bound⟩

end TangoSquared.Paper20261030.CachedReachedHeaderOperation
