import TangoSquared.Paper20261030.SourceForestLift
import TangoSquared.Paper20261030.LocalParentObservation

/-! Physical pointer metadata for the forest observation routines.

The packed payload at one physical vertex is a bounded list of logical
records. A distinct physical identifier and the existing structural fields
make its null-parent test and return-edge comparison available through
ordinary record reads. The one-color masks in these physical fields have
constant size. `PhysicalForestCompiler` maintains this layer under forest
updates. Initializing its identifiers and records remains separate.

Parent observations below are actual local forest programs, implemented
by the existing source controller, not new observation primitives.
-/

namespace TangoSquared.Paper20261030.PhysicalForestMetadata

open ColoredStorage SourcePointer ForestLocalProgram Structural

variable {α ρ ι C : Type*} [DecidableEq ι] [DecidableEq C]

abbrev Payload (ρ ι : Type*) := ι × List ρ
abbrev Record (ρ ι : Type*) := Payload ρ ι × Fields ι Unit
abbrev TaggedForest (C α ρ ι : Type*) := C → Option (Cursor α (Payload ρ ι))

def encodeCursor (current : Cursor α (Payload ρ ι)) : Cursor α (List (Record ρ ι)) :=
  SourceForestLift.packet (cursor Prod.fst (fun _ => (() : Unit)) current)

def encode (forest : TaggedForest C α ρ ι) : ProjectionForest.State C α (Record ρ ι) :=
  fun q => (forest q).map encodeCursor

def erase (forest : TaggedForest C α ρ ι) : ProjectionForest.State C α ρ :=
  fun q => (forest q).map (Cursor.mapRecords Prod.snd)

def Unique (forest : TaggedForest C α ρ ι) : Prop :=
  ∀ q current, forest q = some current → (current.tree.inventory Prod.fst).Nodup

abbrev ParentState (ρ ι : Type*) := SourceForestLift.State (ParentObservationController.State (Payload ρ ι) ι)

def parentProgram (q : C) : Program (ParentState ρ ι) C (Record ρ ι) :=
  SourceForestLift.program q (ParentObservationController.program Prod.fst)

theorem parent_present (q : C) (forest : TaggedForest C α ρ ι) (current : Cursor α (Payload ρ ι))
    (present : forest q = some current) (unique : (current.tree.inventory Prod.fst).Nodup) :
    ∃ reads cost, Run (parentProgram q) (.running .start) (encode forest)
      (.running (.done (ParentObservationController.parentPayload current.ancestors))) (encode forest) reads cost ∧ cost ≤ 4 := by
  obtain ⟨reads,cost,sourceRun,bounded⟩ := ParentObservationController.observe Prod.fst (fun _ : α => (() : Unit))
    current.focus current.ancestors unique
  have atCursor : encode forest q = some (SourceForestLift.packet (cursor Prod.fst (fun _ : α => (() : Unit)) current)) := by
    simp only [encode,present,Option.map_some,encodeCursor]
  have actual := SourceForestLift.run q sourceRun (encode forest) atCursor
  have unchanged : Function.update (encode forest) q
      (some (SourceForestLift.packet (cursor Prod.fst (fun _ : α => (() : Unit)) current))) = encode forest := by
    rw [← atCursor,Function.update_eq_self]
  exact ⟨_,cost,by simpa only [unchanged,parentProgram] using actual,bounded⟩

theorem parent_absent (q : C) (forest : TaggedForest C α ρ ι) (absent : forest q = none) :
    Run (parentProgram q) (.running .start) (encode forest) .error (encode forest) [] 1 := by
  have atCursor : encode forest q = none := by simp only [encode,absent,Option.map_none]
  have first : Step (parentProgram q) (.running .start) (encode forest) .error (encode forest) none := by
    apply Step.readNone (next := SourceForestLift.readNext (fun record _ => ParentObservationController.fromRoot Prod.fst record))
    · rfl
    · exact atCursor
  exact .next first (.halt rfl)

omit [DecidableEq ι] [DecidableEq C] in
theorem parent_erases (current : Cursor α (Payload ρ ι)) :
    ParentObservationController.parentPayload (current.mapRecords Prod.snd).ancestors =
      (ParentObservationController.parentPayload current.ancestors).map Prod.snd := by
  rcases current with ⟨focus,outside⟩
  cases outside with
  | nil => rfl
  | cons frame rest => cases frame <;> rfl

end TangoSquared.Paper20261030.PhysicalForestMetadata
