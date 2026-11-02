import ChaCha.Paper20261030.ColoredCompilerWriteLabels
import ChaCha.Paper20261030.ForestMirrorWriteLabels
import ChaCha.Paper20261030.VirtualHeaderWriteLabels
import ChaCha.Paper20261030.PayloadForestWriteLabels
import ChaCha.Paper20261030.ForestConnectorWriteLabels
import ChaCha.Paper20261030.LocalComponentCompiler

set_option autoImplicit false

/-! The complete component compiler with per-write physical-id labels.
The labels ignore virtual-header contents and delimiters. The proof
passes through physical primitives, packed source operations, mirrored
wings, virtual headers, payload attachment, and shared-tree assembly.
No physical-id agreement is inferred from inventory preservation alone. -/

namespace ChaCha.Paper20261030.LocalComponentForestCompiler

open ColoredStorage SourcePointer Structural PhysicalForestMetadata

variable {α β ρ ι η C σ : Type*} [DecidableEq α] [DecidableEq ι] [DecidableEq η] [LinearOrder C] [Fintype C]

def physicalLabel : Option (PhysicalDatum α ρ ι η C) → Option (Option ι) :=
  Option.map (VirtualHeaderController.physicalLabel (fun record => record.1.1))

theorem compile_write_labels (source : SourceLocalProgram.Program σ ρ) (color : α → C)
    (virtualColor : C) (orientation : C → Bool) (headerKey : α)
    (payload : C → α → Source β (List (Option (PhysicalDatum α ρ ι η C))))
    {initial last : σ} {before after : Cursor α ρ} {sourceReads sourceCost}
    (run : SourceLocalProgram.Run source initial before last after sourceReads sourceCost)
    (decorated : Cursor α (η × ρ)) (erases : decorated.mapRecords Prod.snd = before)
    (logicalUnique : (decorated.tree.inventory Prod.fst).Nodup)
    (forest : TaggedForest C α (LocalColoredCompiler.LogicalRecord ρ η C) ι)
    (represented : ProjectionForest.Represents color (cursor Prod.fst color decorated) (erase forest))
    (physicalUnique : Unique forest) :
    ∃ target finalForest reads cost,
      ForestWriteLabels.Run physicalLabel (program source virtualColor orientation) (ready initial decorated.focus.rootRecord.1)
        (representation virtualColor orientation headerKey payload forest)
        (ready last target.focus.rootRecord.1) (representation virtualColor orientation headerKey payload finalForest) reads cost ∧
      target.mapRecords Prod.snd = after ∧
      target.tree.inventory Prod.fst = decorated.tree.inventory Prod.fst ∧
      ProjectionForest.Represents color (cursor Prod.fst color target) (erase finalForest) ∧
      Unique finalForest ∧ cost ≤ (118560*(Fintype.card C+1))*sourceCost := by
  obtain ⟨target,finalForest,packedReads,packedCost,packedRun,targetErases,inventory,targetRep,targetUnique,packedBound⟩ :=
    LocalColoredCompiler.compile_write_labels source color run decorated erases logicalUnique forest represented physicalUnique
  have mirrored := ForestMirrorController.compile_write_labels _ orientation _ packedRun
  obtain ⟨headerReads,headerCost,headerRun,headerBound⟩ := VirtualHeaderController.compile_write_labels _ virtualColor _ headerKey mirrored
  obtain ⟨reads,cost,actual,bounded⟩ := PayloadForestController.compile_write_labels _ _ payload headerRun
  refine ⟨target,finalForest,reads,cost,actual,targetErases,inventory,targetRep,targetUnique,?_⟩
  calc
    cost ≤ 2*(2*packedCost) := bounded.trans (Nat.mul_le_mul_left 2 headerBound)
    _ ≤ 2*(2*((29640*(Fintype.card C+1))*sourceCost)) := Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left 2 packedBound)
    _ = (118560*(Fintype.card C+1))*sourceCost := by simp only [← Nat.mul_assoc]

end ChaCha.Paper20261030.LocalComponentForestCompiler

namespace ChaCha.Paper20261030.LocalComponentCompiler

open ColoredStorage SourcePointer Structural PhysicalForestMetadata LocalComponentForestCompiler

variable {α β ρ ι η C σ : Type*} [DecidableEq α] [DecidableEq ι] [DecidableEq η] [LinearOrder C] [Fintype C]

theorem compile_write_labels (source : SourceLocalProgram.Program σ ρ) (color : α → C)
    (virtualColor : C) (orientation : C → Bool) (headerKey : α)
    (payload : C → α → Source β (List (Option (PhysicalDatum α ρ ι η C))))
    {initial last : σ} {before after : Cursor α ρ} {sourceReads sourceCost}
    (run : SourceLocalProgram.Run source initial before last after sourceReads sourceCost)
    (decorated : Cursor α (η × ρ)) (erases : decorated.mapRecords Prod.snd = before)
    (logicalUnique : (decorated.tree.inventory Prod.fst).Nodup)
    (forest : TaggedForest C α (LocalColoredCompiler.LogicalRecord ρ η C) ι)
    (represented : ProjectionForest.Represents color (cursor Prod.fst color decorated) (erase forest))
    (physicalUnique : Unique forest)
    (layout : Source C Unit) (distinct : (ForestConnector.colors layout).Nodup)
    (covers : ForestConnector.Covers layout (representation virtualColor orientation headerKey payload forest))
    (config : MultiSourceProgram.Configuration C β (List (Option (PhysicalDatum α ρ ι η C))))
    (assembled : ForestConnector.assemble (representation virtualColor orientation headerKey payload forest) layout = some config) :
    ∃ target finalForest finalConfig reads cost,
      MultiSourceWriteLabels.Run (List.map physicalLabel) (program source virtualColor orientation) (ready initial decorated.focus.rootRecord.1)
        config (ready last target.focus.rootRecord.1) finalConfig reads cost ∧
      target.mapRecords Prod.snd = after ∧
      target.tree.inventory Prod.fst = decorated.tree.inventory Prod.fst ∧
      ProjectionForest.Represents color (cursor Prod.fst color target) (erase finalForest) ∧
      Unique finalForest ∧
      ForestConnector.assemble (representation virtualColor orientation headerKey payload finalForest) layout = some finalConfig ∧
      ForestConnector.Covers layout (representation virtualColor orientation headerKey payload finalForest) ∧
      MultiSourceProgram.WellFormed finalConfig ∧
      cost ≤ (118560*(Fintype.card C+1))*sourceCost := by
  obtain ⟨target,finalForest,reads,cost,actual,targetErases,inventory,targetRep,targetUnique,bounded⟩ :=
    LocalComponentForestCompiler.compile_write_labels source color virtualColor orientation headerKey payload run
      decorated erases logicalUnique forest represented physicalUnique
  obtain ⟨finalConfig,finalRep,joined⟩ := ForestConnector.compile_write_labels _ _ actual layout distinct covers config assembled
  exact ⟨target,finalForest,finalConfig,reads,cost,joined,targetErases,inventory,targetRep,targetUnique,
    finalRep,covers.run actual.run,ForestConnector.assemble_wellFormed _ _ _ finalRep,bounded⟩

end ChaCha.Paper20261030.LocalComponentCompiler
