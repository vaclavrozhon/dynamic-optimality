import ChaCha.Paper20261030.LocalComponentCompiler
import ChaCha.Paper20261030.IdentifiedHeadExchange

/-! Compilation of root-to-root source kernels with a global logical
identifier invariant. The untouched inventory accounts for all other
components, including a second component participating in a head switch.
The actual program still takes only its source control state and the
reached root identifier; the inventory is used solely in the proof.
-/

namespace ChaCha.Paper20261030.LocalComponentCompiler

open ColoredStorage SourcePointer SourceLocalProgram Structural PhysicalForestMetadata
open LocalComponentForestCompiler

variable {α β ρ ι η C σ : Type*} [DecidableEq α] [DecidableEq ι] [DecidableEq η] [LinearOrder C] [Fintype C]

theorem compile_root_run (source : SourceLocalProgram.Program σ ρ) (color : α → C)
    (virtualColor : C) (orientation : C → Bool) (headerKey : α)
    (payload : C → α → Source β (List (Option (PhysicalDatum α ρ ι η C))))
    {initial last : σ} {before after : Source α ρ} {sourceReads sourceCost}
    (run : Run source initial ⟨before,[]⟩ last ⟨after,[]⟩ sourceReads sourceCost)
    (decorated : Source α (η × ρ)) (erases : decorated.mapRecords Prod.snd = before)
    (untouched : Multiset η) (globalUnique : (decorated.inventory Prod.fst + untouched).Nodup)
    (forest : TaggedForest C α (LocalColoredCompiler.LogicalRecord ρ η C) ι)
    (represented : ProjectionForest.Represents color ⟨annotate Prod.fst color none decorated,[]⟩ (erase forest))
    (physicalUnique : Unique forest)
    (layout : Source C Unit) (distinct : (ForestConnector.colors layout).Nodup)
    (covers : ForestConnector.Covers layout (representation virtualColor orientation headerKey payload forest))
    (config : MultiSourceProgram.Configuration C β (List (Option (PhysicalDatum α ρ ι η C))))
    (assembled : ForestConnector.assemble (representation virtualColor orientation headerKey payload forest) layout = some config) :
    ∃ (target : Source α (η × ρ)), ∃ finalForest finalConfig reads cost,
      MultiSourceProgram.Run (program source virtualColor orientation) (ready initial decorated.rootRecord.1)
        config (ready last target.rootRecord.1) finalConfig reads cost ∧
      target.mapRecords Prod.snd = after ∧
      target.inventory Prod.fst = decorated.inventory Prod.fst ∧
      (target.inventory Prod.fst + untouched).Nodup ∧
      ProjectionForest.Represents color ⟨annotate Prod.fst color none target,[]⟩ (erase finalForest) ∧
      Unique finalForest ∧
      ForestConnector.assemble (representation virtualColor orientation headerKey payload finalForest) layout = some finalConfig ∧
      ForestConnector.Covers layout (representation virtualColor orientation headerKey payload finalForest) ∧
      MultiSourceProgram.WellFormed finalConfig ∧
      cost ≤ (118560*(Fintype.card C+1))*sourceCost := by
  have cursorErases : (Cursor.mapRecords Prod.snd ⟨decorated,[]⟩ : Cursor α ρ) = ⟨before,[]⟩ := by
    simp only [Cursor.mapRecords,erases,List.map_nil]
  obtain ⟨target,finalForest,finalConfig,reads,cost,actual,targetErases,inventory,targetRep,targetUnique,
      finalRep,finalCovers,wellFormed,bounded⟩ :=
    compile_run source color virtualColor orientation headerKey payload run ⟨decorated,[]⟩ cursorErases
      (Multiset.nodup_add.mp globalUnique).1 forest represented physicalUnique layout distinct covers config assembled
  have atRoot : target.ancestors = [] := by
    have same := congrArg Cursor.ancestors targetErases
    simpa only [Cursor.mapRecords,List.map_eq_nil_iff] using same
  have sameInventory : target.focus.inventory Prod.fst = decorated.inventory Prod.fst := by
    simpa only [Cursor.tree,plug,atRoot] using inventory
  refine ⟨target.focus,finalForest,finalConfig,reads,cost,actual,congrArg Cursor.focus targetErases,
    sameInventory,?_,?_,targetUnique,finalRep,finalCovers,wellFormed,bounded⟩
  · rw [sameInventory]; exact globalUnique
  · simpa only [cursor,atRoot,frames,parentId] using targetRep

end ChaCha.Paper20261030.LocalComponentCompiler
