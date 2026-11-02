import ChaCha.Paper20261030.LocalComponentForestCompiler
import ChaCha.Paper20261030.ThreeColorConnectors

/-! The colored local program executed in one shared component tree.
The connector layout is used only in the representation proof. The
running program receives neither this layout nor any source/payload
tree. Initial finger setup, primary head changes, and the workspace and
single-finger simulation bounds remain separate obligations.
-/

namespace ChaCha.Paper20261030.LocalComponentCompiler

open ColoredStorage SourcePointer Structural PhysicalForestMetadata
open LocalComponentForestCompiler

variable {α β ρ ι η C σ : Type*} [DecidableEq α] [DecidableEq ι] [DecidableEq η] [LinearOrder C] [Fintype C]

def program (source : SourceLocalProgram.Program σ ρ) (virtualColor : C) (orientation : C → Bool) :
    MultiSourceProgram.Program (State σ α ρ ι η C) C (List (Option (PhysicalDatum α ρ ι η C))) :=
  ForestConnector.program (LocalComponentForestCompiler.program source virtualColor orientation)

theorem compile_run (source : SourceLocalProgram.Program σ ρ) (color : α → C)
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
      MultiSourceProgram.Run (program source virtualColor orientation) (ready initial decorated.focus.rootRecord.1)
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
    LocalComponentForestCompiler.compile_run source color virtualColor orientation headerKey payload run
      decorated erases logicalUnique forest represented physicalUnique
  obtain ⟨finalConfig,finalRep,joined⟩ := ForestConnector.compile_run _ actual layout distinct covers config assembled
  exact ⟨target,finalForest,finalConfig,reads,cost,joined,targetErases,inventory,targetRep,targetUnique,
    finalRep,covers.run actual,ForestConnector.assemble_wellFormed _ _ _ finalRep,bounded⟩

theorem virtual_present (virtualColor : C) (orientation : C → Bool) (headerKey : α)
    (payload : C → α → Source β (List (Option (PhysicalDatum α ρ ι η C))))
    (forest : TaggedForest C α (LocalColoredCompiler.LogicalRecord ρ η C) ι) :
    ∃ header, representation virtualColor orientation headerKey payload forest virtualColor = some header := by
  simp [representation,PayloadForestController.transform,VirtualHeaderController.encode]

end ChaCha.Paper20261030.LocalComponentCompiler
