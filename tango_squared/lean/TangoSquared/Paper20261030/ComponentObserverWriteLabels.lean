import TangoSquared.Paper20261030.ComponentObserverCompiler
import TangoSquared.Paper20261030.ComponentWriteLabels
import TangoSquared.Paper20261030.LocalComponentCompiler

/-! A read-only observer of logical identifiers, payloads, and structural
fields, executed in the actual shared component tree. It uses the packed
read/navigation compiler directly. Stored annotations are observable
records, not a tree-valued input to the controller.
-/

namespace TangoSquared.Paper20261030.ComponentObserverCompiler

open ColoredStorage SourcePointer Structural PhysicalForestMetadata
open LocalComponentForestCompiler

variable {α β ρ ι η C σ : Type*} [DecidableEq α] [DecidableEq ι] [DecidableEq η] [LinearOrder C] [Fintype C]

theorem compile_write_labels (source : SourceLocalProgram.Program σ (LocalColoredCompiler.LogicalRecord ρ η C))
    (readonly : ImmutableSource.ReadOnly source) (color : α → C)
    (virtualColor : C) (orientation : C → Bool) (headerKey : α)
    (payload : C → α → Source β (List (Option (PhysicalDatum α ρ ι η C))))
    {initial last : σ} {before after : Cursor α (η × ρ)} {sourceReads sourceCost}
    (run : SourceLocalProgram.Run source initial (cursor Prod.fst color before)
      last (cursor Prod.fst color after) sourceReads sourceCost)
    (logicalUnique : (before.tree.inventory Prod.fst).Nodup)
    (forest : TaggedForest C α (LocalColoredCompiler.LogicalRecord ρ η C) ι)
    (represented : ProjectionForest.Represents color (cursor Prod.fst color before) (erase forest))
    (physicalUnique : Unique forest)
    (layout : Source C Unit) (distinct : (ForestConnector.colors layout).Nodup)
    (covers : ForestConnector.Covers layout (representation virtualColor orientation headerKey payload forest))
    (config : MultiSourceProgram.Configuration C β (List (Option (PhysicalDatum α ρ ι η C))))
    (assembled : ForestConnector.assemble (representation virtualColor orientation headerKey payload forest) layout = some config) :
    ∃ finalForest finalConfig reads cost,
      MultiSourceWriteLabels.Run (List.map physicalLabel) (program source virtualColor orientation) (ready initial before.focus.rootRecord.1)
        config (ready last after.focus.rootRecord.1) finalConfig reads cost ∧
      ProjectionForest.Represents color (cursor Prod.fst color after) (erase finalForest) ∧
      Unique finalForest ∧
      ForestConnector.assemble (representation virtualColor orientation headerKey payload finalForest) layout = some finalConfig ∧
      ForestConnector.Covers layout (representation virtualColor orientation headerKey payload finalForest) ∧
      MultiSourceProgram.WellFormed finalConfig ∧
      cost ≤ (3120*(Fintype.card C+1))*sourceCost := by
  have checked := observer_checked Prod.fst color source readonly run before rfl
  have annotatedUnique : ((cursor Prod.fst color before).tree.inventory (fun record => record.1.1)).Nodup := by
    rw [cursor_tree,annotate_inventory]
    exact logicalUnique
  obtain ⟨finalForest,packedReads,packedCost,packedRun,targetRep,targetUnique,packedBound⟩ :=
    PackedSourceCompiler.compile_write_labels Prod.fst color source checked forest represented physicalUnique annotatedUnique
  have mirrored := ForestMirrorController.compile_write_labels _ orientation _ packedRun
  obtain ⟨headerReads,headerCost,headerRun,headerBound⟩ := VirtualHeaderController.compile_write_labels _ virtualColor _ headerKey mirrored
  obtain ⟨reads,cost,actual,bounded⟩ := PayloadForestController.compile_write_labels _ _ payload headerRun
  obtain ⟨finalConfig,finalRep,joined⟩ := ForestConnector.compile_write_labels _ _ actual layout distinct covers config assembled
  refine ⟨finalForest,finalConfig,reads,cost,?_,targetRep,targetUnique,finalRep,covers.run actual.run,
    ForestConnector.assemble_wellFormed _ _ _ finalRep,?_⟩
  · simp only [program,ready,cursor,annotate_root] at joined ⊢
    exact joined
  · calc
      cost ≤ 2*(2*packedCost) := bounded.trans (Nat.mul_le_mul_left 2 headerBound)
      _ ≤ 2*(2*((780*(Fintype.card C+1))*sourceCost)) := Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left 2 packedBound)
      _ = (3120*(Fintype.card C+1))*sourceCost := by simp only [← Nat.mul_assoc]

end TangoSquared.Paper20261030.ComponentObserverCompiler
