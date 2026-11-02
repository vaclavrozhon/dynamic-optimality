import ChaCha.Paper20261030.CachedReenteredComponent
import ChaCha.Paper20261030.ReenteredRootedComponent
import ChaCha.Paper20261030.ComponentRootRegister
import ChaCha.Paper20261030.AttachedPacketIdentifiers

set_option autoImplicit false

/-! A root-to-root source operation dispatched from a stored primary
header. The actual read supplies the wing bits and logical root id;
charged setup places the fingers. The final scalar root register repairs
the cache at the reached output root. The full physical payload invariant
is preserved under the cache erasure. Initialization of correct primary
headers and their transfer at a head switch are separate obligations. -/

namespace ChaCha.Paper20261030.CachedRootedComponentExecution

open ColoredStorage SourcePointer Structural PhysicalForestMetadata
open LocalComponentForestCompiler LocalComponentCompiler ForestConnector.ThreeColors
open MultiSourceProgram
open EnclosedRootedComponentExecution (Packet Cell)

variable {α β ρ ι η G σ : Type*} [DecidableEq α] [DecidableEq ι] [DecidableEq η] [DecidableEq G]

local instance : LinearOrder (Option Bool) := inferInstanceAs (LinearOrder (WithBot Bool))

abbrev CachedCell (α ρ ι η : Type*) := PrimaryHeaderController.Record (Cell α ρ ι η) η

def program (entry : Sum (Option Bool) G) (count : Nat) (hasParent : Bool)
    (source : PrimaryHeaderController.Header η → SourceLocalProgram.Program σ ρ)
    (initial : PrimaryHeaderController.Header η → σ) :=
  CachedReenteredComponent.program entry count hasParent
    (fun header => LocalComponentCompiler.program (α := α) (ι := ι) (source header) none wingOrientation)
    (fun header => ready (initial header) header.rootId) rootRegister

theorem execute (markerId : ι) (source : PrimaryHeaderController.Header η → SourceLocalProgram.Program σ ρ)
    (initial : PrimaryHeaderController.Header η → σ) (header : PrimaryHeaderController.Header η) (color : α → Option Bool) (headerKey : α)
    (payload : Option Bool → α → Source β (Packet α ρ ι η))
    {last : σ} {before after : Source α ρ} {sourceReads sourceCost}
    (run : SourceLocalProgram.Run (source header) (initial header) ⟨before,[]⟩ last ⟨after,[]⟩ sourceReads sourceCost)
    (decorated : Source α (η × ρ)) (erases : decorated.mapRecords Prod.snd = before)
    (logicalUnique : (decorated.inventory Prod.fst).Nodup)
    (forest : TaggedForest (Option Bool) α (LocalColoredCompiler.LogicalRecord ρ η (Option Bool)) ι)
    (represented : ProjectionForest.Represents color ⟨annotate Prod.fst color none decorated,[]⟩ (erase forest))
    (physicalUnique : Unique forest)
    (config : Configuration (Option Bool) β (Packet α ρ ι η))
    (assembled : ForestConnector.assemble (representation none wingOrientation headerKey payload forest)
      (layout (representation none wingOrientation headerKey payload forest)) = some config)
    (tree : Source β (Cell α ρ ι η)) (treeErases : tree.mapRecords Prod.snd = config.tree)
    (outside : List (Frame β (Cell α ρ ι η)))
    (global : Configuration (Sum (Option Bool) G) β (Cell α ρ ι η))
    (valid : WellFormed global) (physical : CanonicalComponentUniqueness.Valid markerId global.tree)
    (reserved : markerId ∉ global.tree.inventory Prod.fst)
    (entry : Sum (Option Bool) G)
    (entryRep : MultiSourceSingleCursor.Represents entry ⟨tree,outside⟩ global)
    (saved : Packet α ρ ι η)
    (rootId : header.rootId = decorated.rootRecord.1)
    (leftWing : header.leftWing = (representation none wingOrientation headerKey payload forest (some true)).isSome)
    (rightWing : header.rightWing = (representation none wingOrientation headerKey payload forest (some false)).isSome)
    (cached : Configuration (Sum (Option Bool) G) β (CachedCell α ρ ι η))
    (cachedErases : cached.mapRecords Prod.fst = MultiSourcePacketPrefix.attached saved tree outside global)
    (cachedCurrent : Cursor β (CachedCell α ρ ι η))
    (cachedAtRoot : MultiSourceSingleCursor.Represents entry cachedCurrent cached)
    (cachedHeader : cachedCurrent.focus.rootRecord.2 = some header) :
    ∃ (target : Source α (η × ρ)), ∃ finalForest finalConfig,
      ∃ (finalComponent : Configuration (Option Bool) β (Cell α ρ ι η)), ∃ actualConfig reads cost, ∃ reached : Cursor β (CachedCell α ρ ι η),
      Run (program entry saved.length (!outside.isEmpty) source initial) (.first .start) cached
        (.second (some (header,target.rootRecord.1,.inl none)) (some .done)) actualConfig reads cost ∧
      target.mapRecords Prod.snd = after ∧ target.inventory Prod.fst = decorated.inventory Prod.fst ∧
      ProjectionForest.Represents color ⟨annotate Prod.fst color none target,[]⟩ (erase finalForest) ∧
      Unique finalForest ∧
      ForestConnector.assemble (representation none wingOrientation headerKey payload finalForest)
        (layout (representation none wingOrientation headerKey payload finalForest)) = some finalConfig ∧
      (∀ q, (representation none wingOrientation headerKey payload finalForest q).isSome =
        (representation none wingOrientation headerKey payload forest q).isSome) ∧
      finalComponent.mapRecords Prod.snd = finalConfig ∧
      reached.mapRecords Prod.fst = EnclosingPacketOperation.output saved tree.rootRecord.1 ⟨finalComponent.tree,outside⟩ ∧
      MultiSourceSingleCursor.Represents (.inl none) (PrimaryHeaderRefresh.refreshed header target.rootRecord.1 reached) actualConfig ∧
      (PrimaryHeaderRefresh.refreshed header target.rootRecord.1 reached).focus.rootRecord.2 =
        some {header with rootId := target.rootRecord.1} ∧
      (actualConfig.mapRecords Prod.fst).tree.inventory Prod.fst = global.tree.inventory Prod.fst ∧
      CanonicalComponentUniqueness.Valid markerId (actualConfig.mapRecords Prod.fst).tree ∧
      markerId ∉ (actualConfig.mapRecords Prod.fst).tree.inventory Prod.fst ∧
      WellFormed actualConfig ∧
      CachedRootOperation.RetainedMetadata Prod.fst finalComponent.tree.rootRecord.1 cached.tree actualConfig.tree ∧
      (actualConfig.mapRecords Prod.fst).tree.inorderLabels Prod.fst = global.tree.inorderLabels Prod.fst ∧
      (∀ extra : G, fingerLabel Prod.fst (actualConfig.mapRecords Prod.fst) (.inr extra) =
        fingerLabel Prod.fst global (.inr extra)) ∧
      cost ≤ 1896960*sourceCost+45 := by
  obtain ⟨target,finalForest,finalConfig,finalComponent,entryBits,finalBits,rawTarget,rawReads,rawCost,rawRun,targetErases,ids,
    finalRep,finalUnique,finalAssembly,presence,componentErases,returned,globalIds,finalPhysical,finalReserved,_,order,anchors,bound⟩ :=
    ReenteredRootedComponentExecution.execute markerId (source header) color headerKey payload run decorated erases logicalUnique
      forest represented physicalUnique config assembled tree treeErases outside global valid physical reserved entry entryRep saved
  have path : PrimaryHeaderRefresh.path header = headerPath (representation none wingOrientation headerKey payload forest) := by
    simp only [PrimaryHeaderRefresh.path,headerPath,leftWing,rightWing]
  have cachedValid : WellFormed cached := by
    apply WellFormed.of_mapRecords Prod.fst
    rw [cachedErases]
    exact MultiSourcePacketPrefix.attached_wellFormed saved tree outside global entryRep.1 valid
  have selected : Run
      (CachedReenteredComponent.kernel entry saved.length (!outside.isEmpty)
        (fun h => LocalComponentCompiler.program (source h) none wingOrientation)
        (fun h => ready (initial h) h.rootId) header)
      (.first .start) (cached.mapRecords Prod.fst)
      (.second (some ⟨tree.rootRecord.1,finalComponent.tree.rootRecord.1,.second entryBits (finalBits,.ready (ready last target.rootRecord.1))⟩)
        (some .done)) rawTarget rawReads rawCost := by
    simp only [CachedReenteredComponent.kernel,leftWing,rightWing,path,rootId,cachedErases]
    exact rawRun
  have loadedOrder : rawTarget.tree.inorderLabels Prod.fst = (cached.mapRecords Prod.fst).tree.inorderLabels Prod.fst := by
    rw [cachedErases,MultiSourcePacketPrefix.attached_inorder saved tree outside global entryRep.1]
    exact order
  have loadedUnique : (cached.tree.inventory (fun record => record.1.1)).Nodup := by
    have rawUnique : ((cached.mapRecords Prod.fst).tree.inventory Prod.fst).Nodup := by
      rw [cachedErases,MultiSourcePacketPrefix.attached_inventory saved tree outside global entryRep.1]
      exact physical.2.2
    simpa only [Configuration.mapRecords,mapRecords_inventory,Function.comp_def] using rawUnique
  obtain ⟨actualConfig,observed,total,reached,actual,cacheErases,reachedErases,finalLocated,finalHeader,finalValid,metadata,bounded⟩ :=
    CachedReenteredComponent.dispatch_with_metadata entry saved.length (!outside.isEmpty)
      (fun h => LocalComponentCompiler.program (source h) none wingOrientation)
      (fun h => ready (initial h) h.rootId) rootRegister header (ready last target.rootRecord.1) target.rootRecord.1
      (rootRegister_ready last target.rootRecord.1) tree.rootRecord.1 finalComponent.tree.rootRecord.1 entryBits finalBits
      cached cachedCurrent cachedAtRoot cachedValid cachedHeader rawTarget selected _ returned loadedOrder loadedUnique
  refine ⟨target,finalForest,finalConfig,finalComponent,actualConfig,observed,total,reached,actual,targetErases,ids,
    finalRep,finalUnique,finalAssembly,presence,componentErases,reachedErases,finalLocated,finalHeader,
    ?_,?_,?_,finalValid,?_,?_,?_,by omega⟩
  · rw [cacheErases]
    exact globalIds
  · rw [cacheErases]
    exact finalPhysical
  · rw [cacheErases]
    exact finalReserved
  · simpa only [EnclosingPacketOperation.output,PacketPrefixTransfer.output_root_id] using metadata
  · rw [cacheErases]
    exact order
  · rw [cacheErases]
    exact anchors

end ChaCha.Paper20261030.CachedRootedComponentExecution
