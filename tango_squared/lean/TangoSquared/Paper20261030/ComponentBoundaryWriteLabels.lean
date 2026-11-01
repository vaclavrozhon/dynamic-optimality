import TangoSquared.Paper20261030.LocalComponentBoundaryRead
import TangoSquared.Paper20261030.ComponentObserverWriteLabels

set_option autoImplicit false

/-! Boundary observation retains physical labels at every write of the
compiled observer, including changes to the virtual header. -/

namespace TangoSquared.Paper20261030.ComponentBoundaryReadController

open ColoredStorage SourcePointer Structural PhysicalForestMetadata
open LocalComponentForestCompiler

variable {α β ρ ι η C : Type*} [DecidableEq α] [DecidableEq ι] [DecidableEq η] [LinearOrder C] [Fintype C]

theorem active_labels (color : α → C) (low high terminal : η × ρ) (key : α)
    (prefixTree tail : Source α (η × ρ))
    (logicalUnique : ((Source.fork low prefixTree (.fork high (.leaf key terminal) tail)).inventory Prod.fst).Nodup)
    (forest : TaggedForest C α (LocalColoredCompiler.LogicalRecord ρ η C) ι)
    (represented : ProjectionForest.Represents color
      (cursor Prod.fst color ⟨.fork low prefixTree (.fork high (.leaf key terminal) tail),[]⟩) (erase forest))
    (physicalUnique : Unique forest)
    (virtualColor : C) (orientation : C → Bool) (headerKey : α)
    (payload : C → α → Source β (List (Option (PhysicalDatum α ρ ι η C))))
    (layout : Source C Unit) (distinct : (ForestConnector.colors layout).Nodup)
    (covers : ForestConnector.Covers layout (representation virtualColor orientation headerKey payload forest))
    (config : MultiSourceProgram.Configuration C β (List (Option (PhysicalDatum α ρ ι η C))))
    (assembled : ForestConnector.assemble (representation virtualColor orientation headerKey payload forest) layout = some config) :
    ∃ finalForest finalConfig reads cost,
      MultiSourceWriteLabels.Run (List.map physicalLabel) (program virtualColor orientation) (ComponentObserverCompiler.ready .start low.1)
        config (ComponentObserverCompiler.ready
          (BoundaryReadController.activeResult Prod.fst color low high terminal key prefixTree tail) low.1)
        finalConfig reads cost ∧
      ProjectionForest.Represents color
        (cursor Prod.fst color ⟨.fork low prefixTree (.fork high (.leaf key terminal) tail),[]⟩) (erase finalForest) ∧
      Unique finalForest ∧
      ForestConnector.assemble (representation virtualColor orientation headerKey payload finalForest) layout = some finalConfig ∧
      ForestConnector.Covers layout (representation virtualColor orientation headerKey payload finalForest) ∧
      MultiSourceProgram.WellFormed finalConfig ∧ cost ≤ (3120*(Fintype.card C+1))*7 := by
  obtain ⟨sourceReads,sourceRun⟩ := BoundaryReadController.active_annotated Prod.fst color low high terminal key prefixTree tail
  exact ComponentObserverCompiler.compile_write_labels BoundaryReadController.program BoundaryReadController.readonly color
    virtualColor orientation headerKey payload sourceRun logicalUnique forest represented physicalUnique
    layout distinct covers config assembled

theorem sentinel_labels (color : α → C) (high terminal : η × ρ) (key : α) (tail : Source α (η × ρ))
    (logicalUnique : ((Source.fork high (.leaf key terminal) tail).inventory Prod.fst).Nodup)
    (forest : TaggedForest C α (LocalColoredCompiler.LogicalRecord ρ η C) ι)
    (represented : ProjectionForest.Represents color
      (cursor Prod.fst color ⟨.fork high (.leaf key terminal) tail,[]⟩) (erase forest))
    (physicalUnique : Unique forest)
    (virtualColor : C) (orientation : C → Bool) (headerKey : α)
    (payload : C → α → Source β (List (Option (PhysicalDatum α ρ ι η C))))
    (layout : Source C Unit) (distinct : (ForestConnector.colors layout).Nodup)
    (covers : ForestConnector.Covers layout (representation virtualColor orientation headerKey payload forest))
    (config : MultiSourceProgram.Configuration C β (List (Option (PhysicalDatum α ρ ι η C))))
    (assembled : ForestConnector.assemble (representation virtualColor orientation headerKey payload forest) layout = some config) :
    ∃ finalForest finalConfig reads cost,
      MultiSourceWriteLabels.Run (List.map physicalLabel) (program virtualColor orientation) (ComponentObserverCompiler.ready (.readHigh none) high.1)
        config (ComponentObserverCompiler.ready (BoundaryReadController.sentinelResult Prod.fst color high terminal key tail) high.1)
        finalConfig reads cost ∧
      ProjectionForest.Represents color
        (cursor Prod.fst color ⟨.fork high (.leaf key terminal) tail,[]⟩) (erase finalForest) ∧
      Unique finalForest ∧
      ForestConnector.assemble (representation virtualColor orientation headerKey payload finalForest) layout = some finalConfig ∧
      ForestConnector.Covers layout (representation virtualColor orientation headerKey payload finalForest) ∧
      MultiSourceProgram.WellFormed finalConfig ∧ cost ≤ (3120*(Fintype.card C+1))*4 := by
  obtain ⟨sourceReads,sourceRun⟩ := BoundaryReadController.sentinel_annotated Prod.fst color high terminal key tail
  exact ComponentObserverCompiler.compile_write_labels BoundaryReadController.program BoundaryReadController.readonly color
    virtualColor orientation headerKey payload sourceRun logicalUnique forest represented physicalUnique
    layout distinct covers config assembled

end TangoSquared.Paper20261030.ComponentBoundaryReadController
