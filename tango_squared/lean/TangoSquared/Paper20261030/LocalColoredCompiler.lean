import TangoSquared.Paper20261030.CheckedImmutableStructural
import TangoSquared.Paper20261030.PackedSourceCompiler

/-! An executable one-source-finger colored simulator.

An arbitrary source program is compiled through immutable identifiers,
maintained logical fields, packed color projections, and maintained
physical fields. Each color has one physical finger. The running program
receives neither a logical tree nor its prescribed execution. The theorem
requires a correctly initialized representation and distinct initial
identifiers, and proves all subsequent metadata and uniqueness invariants.

Initialization, virtual-header placement in a shared physical tree, the
full application workspace bound, and the final one-finger BST simulation
are separate obligations.
-/

namespace TangoSquared.Paper20261030.LocalColoredCompiler

open ColoredStorage SourcePointer Structural PhysicalForestMetadata

variable {α ρ ι η C σ : Type*} [DecidableEq α] [DecidableEq ι] [DecidableEq η] [LinearOrder C] [Fintype C]

abbrev LogicalRecord (ρ η C : Type*) := (η × ρ) × Fields η C
abbrev State (σ ρ ι η C : Type*) := PackedSourceCompiler.State
  (ImmutableStructural.State σ ρ η C) (η × ρ) ι η C

def program (source : SourceLocalProgram.Program σ ρ) :
    ForestLocalProgram.Program (State σ ρ ι η C) C (Record (LogicalRecord ρ η C) ι) :=
  PackedSourceCompiler.program Prod.fst (ImmutableStructural.program source)

def ready (state : σ) (id : η) : State σ ρ ι η C :=
  .ready (ImmutableStructural.ready state) id

theorem compile_run (source : SourceLocalProgram.Program σ ρ) (color : α → C)
    {initial last : σ} {before after : Cursor α ρ} {sourceReads sourceCost}
    (run : SourceLocalProgram.Run source initial before last after sourceReads sourceCost)
    (decorated : Cursor α (η × ρ)) (erases : decorated.mapRecords Prod.snd = before)
    (logicalUnique : (decorated.tree.inventory Prod.fst).Nodup)
    (forest : TaggedForest C α (LogicalRecord ρ η C) ι)
    (represented : ProjectionForest.Represents color (cursor Prod.fst color decorated) (erase forest))
    (physicalUnique : Unique forest) :
    ∃ target finalForest reads cost,
      ForestLocalProgram.Run (program source) (ready initial decorated.focus.rootRecord.1) (encode forest)
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
    PackedSourceCompiler.compile_run Prod.fst color (ImmutableStructural.program source) checked
      forest represented physicalUnique annotatedUnique
  refine ⟨target,finalForest,reads,cost,?_,targetErases,inventory,targetRep,targetUnique,?_⟩
  · simpa only [program,ready,cursor,annotate_root] using actual
  · calc
      cost ≤ (780*(Fintype.card C+1))*logicalCost := bounded
      _ ≤ (780*(Fintype.card C+1))*(38*sourceCost) := Nat.mul_le_mul_left _ logicalBound
      _ = (29640*(Fintype.card C+1))*sourceCost := by
        rw [← Nat.mul_assoc, Nat.mul_right_comm 780 (Fintype.card C+1) 38]

end TangoSquared.Paper20261030.LocalColoredCompiler
