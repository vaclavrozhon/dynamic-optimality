import TangoSquared.Paper20261030.ComponentWriteLabels
import TangoSquared.Paper20261030.RootedComponentExecution
import TangoSquared.Paper20261030.ThreeColorLayoutStability
import TangoSquared.Paper20261030.ComponentOriginalKeys

set_option autoImplicit false

/-! Root-to-root component compilation retaining per-write physical
labels through the canonical three-piece assembly. -/

namespace TangoSquared.Paper20261030.RootedComponentExecution

open ColoredStorage SourcePointer Structural PhysicalForestMetadata
open LocalComponentForestCompiler LocalComponentCompiler ForestConnector.ThreeColors

variable {α β ρ ι η σ : Type*} [DecidableEq α] [DecidableEq ι] [DecidableEq η]

local instance : LinearOrder (Option Bool) := inferInstanceAs (LinearOrder (WithBot Bool))

theorem compile_write_labels (source : SourceLocalProgram.Program σ ρ) (color : α → Option Bool) (headerKey : α)
    (payload : Option Bool → α → Source β (List (Option (PhysicalDatum α ρ ι η (Option Bool)))))
    {initial last : σ} {before after : Source α ρ} {sourceReads sourceCost}
    (run : SourceLocalProgram.Run source initial ⟨before,[]⟩ last ⟨after,[]⟩ sourceReads sourceCost)
    (decorated : Source α (η × ρ)) (erases : decorated.mapRecords Prod.snd = before)
    (logicalUnique : (decorated.inventory Prod.fst).Nodup)
    (forest : TaggedForest (Option Bool) α (LocalColoredCompiler.LogicalRecord ρ η (Option Bool)) ι)
    (represented : ProjectionForest.Represents color ⟨annotate Prod.fst color none decorated,[]⟩ (erase forest))
    (physicalUnique : Unique forest)
    (config : MultiSourceProgram.Configuration (Option Bool) β (List (Option (PhysicalDatum α ρ ι η (Option Bool)))))
    (assembled : ForestConnector.assemble (representation none wingOrientation headerKey payload forest)
      (layout (representation none wingOrientation headerKey payload forest)) = some config) :
    ∃ (target : Source α (η × ρ)), ∃ finalForest finalConfig reads cost,
      MultiSourceWriteLabels.Run (List.map physicalLabel) (LocalComponentCompiler.program source none wingOrientation)
        (ready initial decorated.rootRecord.1) config (ready last target.rootRecord.1) finalConfig reads cost ∧
      target.mapRecords Prod.snd = after ∧ target.inventory Prod.fst = decorated.inventory Prod.fst ∧
      ProjectionForest.Represents color ⟨annotate Prod.fst color none target,[]⟩ (erase finalForest) ∧
      Unique finalForest ∧
      ForestConnector.assemble (representation none wingOrientation headerKey payload finalForest)
        (layout (representation none wingOrientation headerKey payload finalForest)) = some finalConfig ∧
      (∀ q, (representation none wingOrientation headerKey payload finalForest q).isSome =
        (representation none wingOrientation headerKey payload forest q).isSome) ∧
      MultiSourceProgram.WellFormed finalConfig ∧ cost ≤ 474240*sourceCost := by
  let physical := representation none wingOrientation headerKey payload forest
  have cursorErases : (Cursor.mapRecords Prod.snd ⟨decorated,[]⟩ : Cursor α ρ) = ⟨before,[]⟩ := by
    simp only [Cursor.mapRecords,erases,List.map_nil]
  obtain ⟨target,finalForest,finalConfig,reads,cost,actual,targetErases,ids,finalRep,finalUnique,finalAssembly,finalCovered,valid,bound⟩ :=
    LocalComponentCompiler.compile_write_labels source color none wingOrientation headerKey payload run
      ⟨decorated,[]⟩ cursorErases logicalUnique forest represented physicalUnique
      (layout physical) (distinct physical) (covers physical) config assembled
  have atRoot : target.ancestors = [] := by
    have equal := congrArg Cursor.ancestors targetErases
    simpa only [Cursor.mapRecords,List.map_eq_nil_iff] using equal
  have presence := ForestConnector.same_presence (layout physical) physical
    (representation none wingOrientation headerKey payload finalForest) config finalConfig
    assembled finalAssembly (covers physical) finalCovered
  refine ⟨target.focus,finalForest,finalConfig,reads,cost,actual,congrArg Cursor.focus targetErases,?_,?_,finalUnique,?_,presence,valid,?_⟩
  · simpa only [Cursor.tree,plug,atRoot] using ids
  · simpa only [cursor,atRoot,frames,parentId] using finalRep
  · rw [layout_congr physical (representation none wingOrientation headerKey payload finalForest) presence]
    exact finalAssembly
  · simpa only [Fintype.card_option,Fintype.card_bool] using bound

end TangoSquared.Paper20261030.RootedComponentExecution
