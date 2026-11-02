import ChaCha.Paper20261030.PackedSourceWriteLabels
import ChaCha.Paper20261030.LocalColoredCompiler

set_option autoImplicit false

/-! The colored source compiler retains the physical id of the reached
vertex in every write, including intermediate logical repairs. The same
controller, final forest invariant, and cost bound are reused. -/

namespace ChaCha.Paper20261030.LocalColoredCompiler

open ColoredStorage SourcePointer Structural PhysicalForestMetadata

variable {α ρ ι η C σ : Type*} [DecidableEq α] [DecidableEq ι] [DecidableEq η] [LinearOrder C] [Fintype C]

theorem compile_write_labels (source : SourceLocalProgram.Program σ ρ) (color : α → C)
    {initial last : σ} {before after : Cursor α ρ} {sourceReads sourceCost}
    (run : SourceLocalProgram.Run source initial before last after sourceReads sourceCost)
    (decorated : Cursor α (η × ρ)) (erases : decorated.mapRecords Prod.snd = before)
    (logicalUnique : (decorated.tree.inventory Prod.fst).Nodup)
    (forest : TaggedForest C α (LogicalRecord ρ η C) ι)
    (represented : ProjectionForest.Represents color (cursor Prod.fst color decorated) (erase forest))
    (physicalUnique : Unique forest) :
    ∃ target finalForest reads cost,
      ForestWriteLabels.Run (fun record => record.1.1) (program source) (ready initial decorated.focus.rootRecord.1) (encode forest)
        (ready last target.focus.rootRecord.1) (encode finalForest) reads cost ∧
      target.mapRecords Prod.snd = after ∧
      target.tree.inventory Prod.fst = decorated.tree.inventory Prod.fst ∧
      ProjectionForest.Represents color (cursor Prod.fst color target) (erase finalForest) ∧
      Unique finalForest ∧ cost ≤ (29640*(Fintype.card C+1))*sourceCost := by
  obtain ⟨target,logicalReads,logicalCost,checked,targetErases,inventory,logicalBound⟩ :=
    ImmutableStructural.checked_compile_run source color run decorated erases logicalUnique
  have annotatedUnique : ((cursor Prod.fst color decorated).tree.inventory (fun record => record.1.1)).Nodup := by
    rw [cursor_tree,annotate_inventory]
    exact logicalUnique
  obtain ⟨finalForest,reads,cost,actual,targetRep,targetUnique,bounded⟩ :=
    PackedSourceCompiler.compile_write_labels Prod.fst color (ImmutableStructural.program source) checked
      forest represented physicalUnique annotatedUnique
  refine ⟨target,finalForest,reads,cost,?_,targetErases,inventory,targetRep,targetUnique,?_⟩
  · simp only [program,ready,cursor,annotate_root] at actual ⊢
    exact actual
  · calc
      cost ≤ (780*(Fintype.card C+1))*logicalCost := bounded
      _ ≤ (780*(Fintype.card C+1))*(38*sourceCost) := Nat.mul_le_mul_left _ logicalBound
      _ = (29640*(Fintype.card C+1))*sourceCost := by
        rw [← Nat.mul_assoc, Nat.mul_right_comm 780 (Fintype.card C+1) 38]

end ChaCha.Paper20261030.LocalColoredCompiler
