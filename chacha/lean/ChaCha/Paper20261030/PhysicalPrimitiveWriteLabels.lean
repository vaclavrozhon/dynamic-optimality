import ChaCha.Paper20261030.SourceForestWriteLabels
import ChaCha.Paper20261030.PhysicalForestPrimitive

set_option autoImplicit false

/-! Actual physical primitives preserve each reached packet's physical
id at every write, including the structural-maintenance writes. This
uses the existing checked immutable compiler, with the same factor 38.
It is the base guarantee to carry through component compilation. -/

namespace ChaCha.Paper20261030.PhysicalForestMetadata

open ColoredStorage SourcePointer ForestLocalProgram Structural

variable {α ρ ι C : Type*} [DecidableEq ι] [DecidableEq C]

theorem execute_write_labels (q : C) (operation : Operation ρ) (forest : TaggedForest C α ρ ι)
    (current : Cursor α (Payload ρ ι)) (present : forest q = some current) (unique : Unique forest)
    (after : Cursor α (List ρ)) (effect : Effect operation (current.mapRecords Prod.snd) after) :
    ∃ target reads cost,
      ForestWriteLabels.Run (fun record => record.1.1) (operationProgram q operation)
        operationInitial (encode forest) operationFinal (encode (Function.update forest q (some target))) reads cost ∧
      target.mapRecords Prod.snd = after ∧
      target.tree.inventory Prod.fst = current.tree.inventory Prod.fst ∧
      Unique (Function.update forest q (some target)) ∧ cost ≤ 38 := by
  obtain ⟨target,reads,cost,checked,erases,ids,bound⟩ :=
    ImmutableStructural.checked_compile_run (primitive operation) (fun _ : α => (() : Unit))
      (primitive_run operation (current.mapRecords Prod.snd) after effect) current rfl (unique q current present)
  have atCursor : encode forest q = some (SourceForestLift.packet (cursor Prod.fst (fun _ : α => (() : Unit)) current)) := by
    simp only [encode,present,Option.map_some,encodeCursor]
  have actual := SourceForestWriteLabels.lift Prod.fst (fun _ : α => (() : Unit)) q checked (encode forest) atCursor
  have targetUnique : (target.tree.inventory Prod.fst).Nodup := by rw [ids]; exact unique q current present
  refine ⟨target,reads.map (fun record => (q,[record])),cost,?_,erases,ids,unique.update q target targetUnique,?_⟩
  · simp only [operationProgram,operationInitial,operationFinal,encode_update,encodeCursor] at actual ⊢
    exact actual
  · simpa only [Nat.mul_one] using bound

end ChaCha.Paper20261030.PhysicalForestMetadata
