import TangoSquared.Paper20261030.LocalComponentCompiler

/-! Compiling an explicitly identified source run into the shared
component tree. The logical target is supplied by a checked immutable
source execution, so stronger properties of that execution, such as
complete tree preservation during a read-only search, remain available.
All structural and physical metadata obligations are discharged by the
same existing compiler stages.
-/

namespace TangoSquared.Paper20261030.LocalComponentCompiler

open ColoredStorage SourcePointer SourceLocalProgram Structural PhysicalForestMetadata
open LocalComponentForestCompiler

variable {α β ρ ι η C σ : Type*} [DecidableEq α] [DecidableEq ι] [DecidableEq η] [LinearOrder C] [Fintype C]

theorem compile_tagged_run (source : SourceLocalProgram.Program σ ρ) (color : α → C)
    (virtualColor : C) (orientation : C → Bool) (headerKey : α)
    (payload : C → α → Source β (List (Option (PhysicalDatum α ρ ι η C))))
    {initial last : σ} {before after : Cursor α (η × ρ)} {sourceReads sourceCost}
    (run : Run (ImmutableSource.program source) (.ready initial) before (.ready last) after sourceReads sourceCost)
    (logicalUnique : (before.tree.inventory Prod.fst).Nodup)
    (forest : TaggedForest C α (LocalColoredCompiler.LogicalRecord ρ η C) ι)
    (represented : ProjectionForest.Represents color (cursor Prod.fst color before) (erase forest))
    (physicalUnique : Unique forest)
    (layout : Source C Unit) (distinct : (ForestConnector.colors layout).Nodup)
    (covers : ForestConnector.Covers layout (representation virtualColor orientation headerKey payload forest))
    (config : MultiSourceProgram.Configuration C β (List (Option (PhysicalDatum α ρ ι η C))))
    (assembled : ForestConnector.assemble (representation virtualColor orientation headerKey payload forest) layout = some config) :
    ∃ finalForest finalConfig reads cost,
      MultiSourceProgram.Run (program source virtualColor orientation) (ready initial before.focus.rootRecord.1)
        config (ready last after.focus.rootRecord.1) finalConfig reads cost ∧
      ProjectionForest.Represents color (cursor Prod.fst color after) (erase finalForest) ∧
      Unique finalForest ∧
      ForestConnector.assemble (representation virtualColor orientation headerKey payload finalForest) layout = some finalConfig ∧
      ForestConnector.Covers layout (representation virtualColor orientation headerKey payload finalForest) ∧
      MultiSourceProgram.WellFormed finalConfig ∧
      cost ≤ (59280*(Fintype.card C+1))*sourceCost := by
  obtain ⟨logicalReads,logicalCost,checked,logicalBound⟩ :=
    ImmutableStructural.checked_tagged_run source color run trivial logicalUnique
  have annotatedUnique : ((cursor Prod.fst color before).tree.inventory (fun record => record.1.1)).Nodup := by
    rw [cursor_tree,annotate_inventory]
    exact logicalUnique
  obtain ⟨finalForest,packedReads,packedCost,packedRun,targetRep,targetUnique,packedBound⟩ :=
    PackedSourceCompiler.compile_run Prod.fst color (ImmutableStructural.program source) checked forest represented physicalUnique annotatedUnique
  have coloredRun : ForestLocalProgram.Run (LocalColoredCompiler.program source)
      (LocalColoredCompiler.ready initial before.focus.rootRecord.1) (encode forest)
      (LocalColoredCompiler.ready last after.focus.rootRecord.1) (encode finalForest) packedReads packedCost := by
    simpa only [LocalColoredCompiler.program,LocalColoredCompiler.ready,ImmutableStructural.ready,cursor,annotate_root] using packedRun
  have mirrored := ForestMirrorController.compile_run orientation _ coloredRun
  obtain ⟨headerReads,headerCost,headerRun,headerBound⟩ := VirtualHeaderController.compile_run virtualColor _ headerKey mirrored
  obtain ⟨reads,cost,actual,bounded⟩ := PayloadForestController.compile_run _ payload headerRun
  obtain ⟨finalConfig,finalRep,joined⟩ := ForestConnector.compile_run _ actual layout distinct covers config assembled
  refine ⟨finalForest,finalConfig,reads,cost,joined,targetRep,targetUnique,finalRep,covers.run actual,
    ForestConnector.assemble_wellFormed _ _ _ finalRep,?_⟩
  calc
    cost ≤ 2*(2*packedCost) := bounded.trans (Nat.mul_le_mul_left 2 headerBound)
    _ ≤ 2*(2*((780*(Fintype.card C+1))*logicalCost)) := Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left 2 packedBound)
    _ ≤ 2*(2*((780*(Fintype.card C+1))*(19*sourceCost))) :=
      Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left _ logicalBound))
    _ = (59280*(Fintype.card C+1))*sourceCost := by
      rw [← Nat.mul_assoc (780*(Fintype.card C+1)) 19 sourceCost,
        Nat.mul_right_comm 780 (Fintype.card C+1) 19]
      simp only [← Nat.mul_assoc]

end TangoSquared.Paper20261030.LocalComponentCompiler
