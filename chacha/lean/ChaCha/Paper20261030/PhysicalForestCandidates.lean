import ChaCha.Paper20261030.PhysicalForestMetadata
import ChaCha.Paper20261030.PackedParentLocation

/-! Soundness and completeness of the physical parent-observation
neighborhood. Its candidate records come from the actual logical source
tree. When the source cursor has a parent, at least one candidate is that
parent's record, including when the owning finger is parked.
-/

namespace ChaCha.Paper20261030.PhysicalForestMetadata

open ColoredStorage SourcePointer SourceLocalProgram Structural

variable {α ρ ι C : Type*} [DecidableEq α] [DecidableEq ι] [LinearOrder C]

def Candidates (current : Cursor α (Payload ρ ι)) (record : ρ) : Prop :=
  record ∈ current.focus.rootRecord.2 ∨
    ∃ parent, ParentObservationController.parentPayload current.ancestors = some parent ∧ record ∈ parent.2

omit [DecidableEq α] [DecidableEq ι] in
theorem parent_payload_up {before after : Cursor α ρ} (moved : navigate .up before = some after) :
    ParentObservationController.parentPayload before.ancestors = some after.focus.rootRecord := by
  rcases before with ⟨focus,outside⟩
  cases outside with
  | nil => simp [navigate] at moved
  | cons frame rest => cases frame <;> cases Option.some.inj moved <;> rfl

omit [DecidableEq α] [DecidableEq ι] in
theorem parent_payload_mem (physical : Cursor α (List ρ)) (parent : List ρ)
    (observed : ParentObservationController.parentPayload physical.ancestors = some parent)
    {record : ρ} (member : record ∈ parent) : record ∈ physical.tree.toStored.records := by
  rcases physical with ⟨focus,outside⟩
  cases outside with
  | nil => simp only [ParentObservationController.parentPayload,reduceCtorEq] at observed
  | cons frame rest =>
    cases frame with
    | left value sibling =>
      cases Option.some.inj observed
      exact stored_records_focus (.fork parent focus sibling) rest (Source.rootRecords_mem _ member)
    | right sibling value =>
      cases Option.some.inj observed
      exact stored_records_focus (.fork parent sibling focus) rest (Source.rootRecords_mem _ member)

omit [DecidableEq ι] in
theorem candidates_inside (color : α → C) (source : Cursor α ρ) (forest : TaggedForest C α ρ ι)
    (represented : ProjectionForest.Represents color source (erase forest))
    (q : C) (current : Cursor α (Payload ρ ι)) (present : forest q = some current)
    (record : ρ) (candidate : Candidates current record) : record ∈ source.tree.records := by
  have atRep : ColoredStorage.Represents color q source (current.mapRecords Prod.snd) := by
    have viewRep := represented q
    simpa only [erase,present,Option.map_some,ProjectionForest.RepresentsAt] using viewRep
  rcases candidate with here | ⟨parent,observed,there⟩
  · apply represented_record_mem color q source atRep
    simpa only [Cursor.mapRecords,Source.mapRecords_root] using here
  · have parentObserved : ParentObservationController.parentPayload (current.mapRecords Prod.snd).ancestors = some parent.2 := by
      rw [parent_erases,observed]
      rfl
    have member := parent_payload_mem (current.mapRecords Prod.snd) parent.2 parentObserved there
    rw [packed_toStored color q source.tree atRep.1] at member
    exact pack_records_mem color q source.tree member

omit [DecidableEq ι] in
theorem parent_candidate [Fintype C] (color : α → C) (right : Bool)
    (l r : Source α ρ) (record : ρ) (outside) (forest : TaggedForest C α ρ ι)
    (represented : ProjectionForest.Represents color
      (if right then ⟨r,.right l record::outside⟩ else ⟨l,.left record r::outside⟩) (erase forest)) :
    ∃ q current, forest q = some current ∧ Candidates current record := by
  obtain ⟨q,physical,atCursor,location⟩ := forest_parent_record color right l r record outside (erase forest) represented
  cases present : forest q with
  | none => simp only [erase,present,Option.map_none,reduceCtorEq] at atCursor
  | some current =>
    have equal : current.mapRecords Prod.snd = physical := by
      simpa only [erase,present,Option.map_some,Option.some.injEq] using atCursor
    subst physical
    refine ⟨q,current,present,?_⟩
    rcases location with ⟨here,_⟩ | ⟨parent,moved,there,_⟩
    · exact Or.inl (by simpa only [Cursor.mapRecords,Source.mapRecords_root] using here)
    · have observed := parent_payload_up moved
      rw [parent_erases] at observed
      cases stored : ParentObservationController.parentPayload current.ancestors with
      | none => simp only [stored,Option.map_none,reduceCtorEq] at observed
      | some payload =>
        have equal : payload.2 = parent.focus.rootRecord := by
          simpa only [stored,Option.map_some,Option.some.injEq] using observed
        exact Or.inr ⟨payload,stored,equal ▸ there⟩

end ChaCha.Paper20261030.PhysicalForestMetadata
