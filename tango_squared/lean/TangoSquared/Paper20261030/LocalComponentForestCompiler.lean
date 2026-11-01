import TangoSquared.Paper20261030.LocalColoredCompiler
import TangoSquared.Paper20261030.ForestMirrorProgram
import TangoSquared.Paper20261030.VirtualHeaderCompiler
import TangoSquared.Paper20261030.PayloadForestCompiler
import TangoSquared.Paper20261030.ForestLeafInvariant

/-! Combining the local colored simulation with mirrored wings, a
physical header for the virtual projection, and unchanged leaf payloads.
The result is an actual program on the component's separate physical
pieces. Concatenating those pieces in one tree, controlling primary head
switches, and the complete workspace proof remain separate obligations.
-/

namespace TangoSquared.Paper20261030.LocalComponentForestCompiler

open ColoredStorage SourcePointer Structural PhysicalForestMetadata

variable {α β ρ ι η C σ : Type*} [DecidableEq α] [DecidableEq ι] [DecidableEq η] [LinearOrder C] [Fintype C]

abbrev PackedRecord (ρ ι η C : Type*) := Record (LocalColoredCompiler.LogicalRecord ρ η C) ι
abbrev PhysicalDatum (α ρ ι η C : Type*) := VirtualHeaderController.Datum α (PackedRecord ρ ι η C)
abbrev HeaderState (σ α ρ ι η C : Type*) := VirtualHeaderController.State
  (LocalColoredCompiler.State σ ρ ι η C) α (PackedRecord ρ ι η C)
abbrev State (σ α ρ ι η C : Type*) := PayloadForestController.State
  (HeaderState σ α ρ ι η C) C (PhysicalDatum α ρ ι η C)

def program (source : SourceLocalProgram.Program σ ρ) (virtualColor : C) (orientation : C → Bool) :
    ForestLocalProgram.Program (State σ α ρ ι η C) C (Option (PhysicalDatum α ρ ι η C)) :=
  PayloadForestController.program (VirtualHeaderController.program virtualColor
    (ForestMirrorController.program orientation (LocalColoredCompiler.program source)))

def ready (state : σ) (id : η) : State σ α ρ ι η C :=
  .ready (.ready (LocalColoredCompiler.ready state id))

def representation (virtualColor : C) (orientation : C → Bool) (headerKey : α)
    (payload : C → α → Source β (List (Option (PhysicalDatum α ρ ι η C))))
    (forest : TaggedForest C α (LocalColoredCompiler.LogicalRecord ρ η C) ι) :
    ProjectionForest.State C β (Option (PhysicalDatum α ρ ι η C)) :=
  PayloadForestController.transform payload (VirtualHeaderController.encode virtualColor headerKey
    (ForestMirrorController.transform orientation (encode forest)))

theorem compile_run (source : SourceLocalProgram.Program σ ρ) (color : α → C)
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
      ForestLocalProgram.Run (program source virtualColor orientation) (ready initial decorated.focus.rootRecord.1)
        (representation virtualColor orientation headerKey payload forest)
        (ready last target.focus.rootRecord.1) (representation virtualColor orientation headerKey payload finalForest) reads cost ∧
      target.mapRecords Prod.snd = after ∧
      target.tree.inventory Prod.fst = decorated.tree.inventory Prod.fst ∧
      ProjectionForest.Represents color (cursor Prod.fst color target) (erase finalForest) ∧
      Unique finalForest ∧ cost ≤ (118560*(Fintype.card C+1))*sourceCost := by
  obtain ⟨target,finalForest,packedReads,packedCost,packedRun,targetErases,inventory,targetRep,targetUnique,packedBound⟩ :=
    LocalColoredCompiler.compile_run source color run decorated erases logicalUnique forest represented physicalUnique
  have mirrored := ForestMirrorController.compile_run orientation _ packedRun
  obtain ⟨headerReads,headerCost,headerRun,headerBound⟩ := VirtualHeaderController.compile_run virtualColor _ headerKey mirrored
  obtain ⟨reads,cost,actual,bounded⟩ := PayloadForestController.compile_run _ payload headerRun
  refine ⟨target,finalForest,reads,cost,actual,targetErases,inventory,targetRep,targetUnique,?_⟩
  calc
    cost ≤ 2*(2*packedCost) := bounded.trans (Nat.mul_le_mul_left 2 headerBound)
    _ ≤ 2*(2*((29640*(Fintype.card C+1))*sourceCost)) := Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left 2 packedBound)
    _ = (118560*(Fintype.card C+1))*sourceCost := by simp only [← Nat.mul_assoc]

end TangoSquared.Paper20261030.LocalComponentForestCompiler
