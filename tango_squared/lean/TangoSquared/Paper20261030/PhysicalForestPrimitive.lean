import TangoSquared.Paper20261030.PhysicalForestMetadata
import TangoSquared.Paper20261030.ImmutableStructuralCompiler

/-! Maintaining the physical pointer annotations under a forest update.
Each adjacent move, rotation, or payload-list write is a fixed local
program. The generic immutable structural compiler supplies its fields;
the source-to-forest lift runs it at the selected finger. Distinct physical
identifiers and every other finger are preserved. Initialization remains
separate, but maintenance is not an assumed contract.
-/

namespace TangoSquared.Paper20261030.PhysicalForestMetadata

open ColoredStorage SourcePointer ForestLocalProgram Structural
open DynamicOptimality.LocalProgram (Move)

variable {α ρ ι C : Type*} [DecidableEq ι] [DecidableEq C]

inductive Operation (ρ : Type*) where
  | nav (action : Move)
  | write (records : List ρ)

def primitive (operation : Operation ρ) : SourceLocalProgram.Program Bool (List ρ)
  | true => .halt
  | false => match operation with
    | .nav action => .nav action true
    | .write records => .write records true

abbrev OperationState (ρ ι : Type*) := SourceForestLift.State (ImmutableStructural.State Bool (List ρ) ι Unit)

def operationProgram (q : C) (operation : Operation ρ) : Program (OperationState ρ ι) C (Record ρ ι) :=
  SourceForestLift.program q (ImmutableStructural.program (primitive operation))

def operationInitial : OperationState ρ ι := .running (ImmutableStructural.ready false)
def operationFinal : OperationState ρ ι := .running (ImmutableStructural.ready true)

def Effect : Operation ρ → Cursor α (List ρ) → Cursor α (List ρ) → Prop
  | .nav action,before,after => SourceLocalProgram.navigate action before = some after
  | .write records,before,after => after = ⟨before.focus.setRoot records,before.ancestors⟩

theorem primitive_run (operation : Operation ρ) (before after : Cursor α (List ρ))
    (effect : Effect operation before after) :
    SourceLocalProgram.Run (primitive operation) false before true after [] 1 := by
  cases operation with
  | nav action =>
    exact SourceLocalProgram.Run.next (program := primitive (.nav action)) (.nav rfl effect) (.halt rfl)
  | write records =>
    cases effect
    exact SourceLocalProgram.Run.next (program := primitive (.write records)) (.write rfl) (.halt rfl)

theorem encode_update (forest : TaggedForest C α ρ ι) (q : C) (current : Cursor α (Payload ρ ι)) :
    encode (Function.update forest q (some current)) = Function.update (encode forest) q (some (encodeCursor current)) := by
  funext i
  by_cases equal : i = q
  · subst i; simp only [encode,Function.update_self,Option.map_some]
  · simp only [encode,Function.update_of_ne equal]

theorem erase_update (forest : TaggedForest C α ρ ι) (q : C) (current : Cursor α (Payload ρ ι)) :
    erase (Function.update forest q (some current)) =
      Function.update (erase forest) q (some (current.mapRecords Prod.snd)) := by
  funext i
  by_cases equal : i = q
  · subst i; simp only [erase,Function.update_self,Option.map_some]
  · simp only [erase,Function.update_of_ne equal]

theorem Unique.update {forest : TaggedForest C α ρ ι} (unique : Unique forest) (q : C)
    (current : Cursor α (Payload ρ ι)) (currentUnique : (current.tree.inventory Prod.fst).Nodup) :
    Unique (Function.update forest q (some current)) := by
  intro i actual present
  by_cases equal : i = q
  · subst i
    simp only [Function.update_self,Option.some.injEq] at present
    subst actual
    exact currentUnique
  · exact unique i actual (by simpa only [Function.update_of_ne equal] using present)

theorem execute (q : C) (operation : Operation ρ) (forest : TaggedForest C α ρ ι)
    (current : Cursor α (Payload ρ ι)) (present : forest q = some current) (unique : Unique forest)
    (after : Cursor α (List ρ)) (effect : Effect operation (current.mapRecords Prod.snd) after) :
    ∃ target reads cost,
      Run (operationProgram q operation) operationInitial (encode forest) operationFinal
        (encode (Function.update forest q (some target))) reads cost ∧
      target.mapRecords Prod.snd = after ∧
      target.tree.inventory Prod.fst = current.tree.inventory Prod.fst ∧
      Unique (Function.update forest q (some target)) ∧ cost ≤ 38 := by
  have sourceRun := primitive_run operation (current.mapRecords Prod.snd) after effect
  obtain ⟨target,reads,cost,run,erases,inventory,bounded⟩ :=
    ImmutableStructural.compile_run (primitive operation) (fun _ : α => (() : Unit)) sourceRun current rfl (unique q current present)
  have atCursor : encode forest q = some (SourceForestLift.packet (cursor Prod.fst (fun _ : α => (() : Unit)) current)) := by
    simp only [encode,present,Option.map_some,encodeCursor]
  have actual := SourceForestLift.run q run (encode forest) atCursor
  have targetUnique : (target.tree.inventory Prod.fst).Nodup := by rw [inventory]; exact unique q current present
  refine ⟨target,reads.map (fun record => (q,[record])),cost,?_,erases,inventory,
    unique.update q target targetUnique,?_⟩
  · simpa only [operationProgram,operationInitial,operationFinal,encode_update,encodeCursor] using actual
  · simpa only [Nat.mul_one] using bounded

end TangoSquared.Paper20261030.PhysicalForestMetadata
