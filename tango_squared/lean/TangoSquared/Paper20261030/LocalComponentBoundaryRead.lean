import TangoSquared.Paper20261030.LocalBoundaryRead
import TangoSquared.Paper20261030.ComponentObserverCompiler
import TangoSquared.Paper20261030.HeadBoundaryMetadata

/-! The exposed logical boundary records are acquired by a program in
the shared physical component tree. Its only initial data are the root
identifier and whether the component has a retained prefix. The source
trees and annotated record values below specify the checked result;
they are not runtime arguments.
-/

namespace TangoSquared.Paper20261030.BoundaryReadController

open ColoredStorage SourcePointer SourceLocalProgram Structural

variable {α ρ η C : Type*} [DecidableEq C]

def activeResult (identifier : ρ → η) (color : α → C) (low high terminal : ρ)
    (key : α) (prefixTree tail : Source α ρ) : State (ρ × Fields η C) :=
  let boundary := Source.fork high (.leaf key terminal) tail
  .done (some (low,fields identifier color none (.fork low prefixTree boundary)))
    (high,fields identifier color (some (identifier low)) boundary)
    (terminal,fields identifier color (some (identifier high)) (.leaf key terminal))

def sentinelResult (identifier : ρ → η) (color : α → C) (high terminal : ρ)
    (key : α) (tail : Source α ρ) : State (ρ × Fields η C) :=
  .done none (high,fields identifier color none (.fork high (.leaf key terminal) tail))
    (terminal,fields identifier color (some (identifier high)) (.leaf key terminal))

theorem active_annotated (identifier : ρ → η) (color : α → C) (low high terminal : ρ)
    (key : α) (prefixTree tail : Source α ρ) :
    ∃ reads, Run program .start
      (cursor identifier color ⟨.fork low prefixTree (.fork high (.leaf key terminal) tail),[]⟩)
      (activeResult identifier color low high terminal key prefixTree tail)
      (cursor identifier color ⟨.fork low prefixTree (.fork high (.leaf key terminal) tail),[]⟩) reads 7 := by
  let boundary := Source.fork high (.leaf key terminal) tail
  let lowRecord := (low,fields identifier color none (.fork low prefixTree boundary))
  let highRecord := (high,fields identifier color (some (identifier low)) boundary)
  let terminalRecord := (terminal,fields identifier color (some (identifier high)) (.leaf key terminal))
  exact ⟨_,active lowRecord highRecord terminalRecord
    (annotate identifier color (some (identifier low)) prefixTree)
    (annotate identifier color (some (identifier high)) tail) key []⟩

theorem sentinel_annotated (identifier : ρ → η) (color : α → C) (high terminal : ρ)
    (key : α) (tail : Source α ρ) :
    ∃ reads, Run program (.readHigh none)
      (cursor identifier color ⟨.fork high (.leaf key terminal) tail,[]⟩)
      (sentinelResult identifier color high terminal key tail)
      (cursor identifier color ⟨.fork high (.leaf key terminal) tail,[]⟩) reads 4 := by
  let highRecord := (high,fields identifier color none (.fork high (.leaf key terminal) tail))
  let terminalRecord := (terminal,fields identifier color (some (identifier high)) (.leaf key terminal))
  exact ⟨_,sentinel highRecord terminalRecord (annotate identifier color (some (identifier high)) tail) key []⟩

end TangoSquared.Paper20261030.BoundaryReadController

namespace TangoSquared.Paper20261030.ComponentBoundaryReadController

open ColoredStorage SourcePointer Structural PhysicalForestMetadata
open LocalComponentForestCompiler

variable {α β ρ ι η C : Type*} [DecidableEq α] [DecidableEq ι] [DecidableEq η] [LinearOrder C] [Fintype C]

abbrev State (α ρ ι η C : Type*) := ComponentObserverCompiler.State
  (BoundaryReadController.State (LocalColoredCompiler.LogicalRecord ρ η C)) α ρ ι η C

def program (virtualColor : C) (orientation : C → Bool) :
    MultiSourceProgram.Program (State α ρ ι η C) C (List (Option (PhysicalDatum α ρ ι η C))) :=
  ComponentObserverCompiler.program BoundaryReadController.program virtualColor orientation

theorem active (color : α → C) (low high terminal : η × ρ) (key : α)
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
      MultiSourceProgram.Run (program virtualColor orientation) (ComponentObserverCompiler.ready .start low.1)
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
  exact ComponentObserverCompiler.compile_run BoundaryReadController.program BoundaryReadController.readonly color
    virtualColor orientation headerKey payload sourceRun logicalUnique forest represented physicalUnique
    layout distinct covers config assembled

theorem sentinel (color : α → C) (high terminal : η × ρ) (key : α) (tail : Source α (η × ρ))
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
      MultiSourceProgram.Run (program virtualColor orientation) (ComponentObserverCompiler.ready (.readHigh none) high.1)
        config (ComponentObserverCompiler.ready (BoundaryReadController.sentinelResult Prod.fst color high terminal key tail) high.1)
        finalConfig reads cost ∧
      ProjectionForest.Represents color
        (cursor Prod.fst color ⟨.fork high (.leaf key terminal) tail,[]⟩) (erase finalForest) ∧
      Unique finalForest ∧
      ForestConnector.assemble (representation virtualColor orientation headerKey payload finalForest) layout = some finalConfig ∧
      ForestConnector.Covers layout (representation virtualColor orientation headerKey payload finalForest) ∧
      MultiSourceProgram.WellFormed finalConfig ∧ cost ≤ (3120*(Fintype.card C+1))*4 := by
  obtain ⟨sourceReads,sourceRun⟩ := BoundaryReadController.sentinel_annotated Prod.fst color high terminal key tail
  exact ComponentObserverCompiler.compile_run BoundaryReadController.program BoundaryReadController.readonly color
    virtualColor orientation headerKey payload sourceRun logicalUnique forest represented physicalUnique
    layout distinct covers config assembled

end TangoSquared.Paper20261030.ComponentBoundaryReadController
