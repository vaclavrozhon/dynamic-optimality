import ChaCha.Paper20261030.PhysicalRecordFinderProgram

/-! Only actual source records can be returned by the physical search.
An unsuccessful lookup rules out the wanted record in that candidate
list. Together these facts justify progressing to the next color.
-/

namespace ChaCha.Paper20261030.PhysicalRecordFinder

open ColoredStorage SourcePointer Structural PhysicalForestMetadata

variable {α ρ ι η C : Type*} [DecidableEq ι] [DecidableEq η] [LinearOrder C]

omit [DecidableEq ι] [LinearOrder C] in
theorem lookup_sound (identifier : ρ → η) (source : Source α ρ) (wanted : ρ)
    (wantedInside : wanted ∈ source.records) (unique : Distinguishes identifier source)
    (entries : Option (List ρ))
    (inside : ∀ records, entries = some records → ∀ record ∈ records, record ∈ source.records)
    (record : ρ) (found : lookup identifier (identifier wanted) entries = some record) : record = wanted := by
  cases entries with
  | none => simp only [lookup,Option.bind_none,reduceCtorEq] at found
  | some records =>
    have member := List.mem_of_find?_eq_some found
    have same := List.find?_some found
    exact unique record (inside records rfl record member) wanted wantedInside
      (by simpa only [decide_eq_true_eq] using same)

omit [DecidableEq ι] [LinearOrder C] in
theorem lookup_none_absent (identifier : ρ → η) (wanted : ρ) (entries : Option (List ρ))
    (missing : lookup identifier (identifier wanted) entries = none)
    (records : List ρ) (observed : entries = some records) : wanted ∉ records := by
  subst entries
  intro member
  exact (List.find?_eq_none.mp missing wanted member) (by simp)

omit [DecidableEq ι] [DecidableEq η] [LinearOrder C] in
theorem current_candidate (current : Option (Cursor α (Payload ρ ι))) (records : List ρ)
    (observed : currentEntries current = some records) (record : ρ) (member : record ∈ records) :
    ∃ cursor, current = some cursor ∧ Candidates cursor record := by
  cases current with
  | none => simp only [currentEntries,Option.map_none,reduceCtorEq] at observed
  | some cursor =>
    have equal : cursor.focus.rootRecord.2 = records := Option.some.inj observed
    exact ⟨cursor,rfl,Or.inl (equal ▸ member)⟩

omit [DecidableEq ι] [DecidableEq η] [LinearOrder C] in
theorem parent_candidate (current : Option (Cursor α (Payload ρ ι))) (records : List ρ)
    (observed : parentEntries current = some records) (record : ρ) (member : record ∈ records) :
    ∃ cursor, current = some cursor ∧ Candidates cursor record := by
  cases current with
  | none => simp only [parentEntries,Option.bind_none,reduceCtorEq] at observed
  | some cursor =>
    cases stored : ParentObservationController.parentPayload cursor.ancestors with
    | none => simp only [parentEntries,Option.bind_some,stored,Option.map_none,reduceCtorEq] at observed
    | some payload =>
      have equal : payload.2 = records := by
        simpa only [parentEntries,Option.bind_some,stored,Option.map_some,Option.some.injEq] using observed
      exact ⟨cursor,rfl,Or.inr ⟨payload,stored,equal ▸ member⟩⟩

omit [DecidableEq ι] [DecidableEq η] in
theorem current_inside [DecidableEq α] (color : α → C) (source : Cursor α ρ)
    (forest : TaggedForest C α ρ ι) (represented : ProjectionForest.Represents color source (erase forest))
    (q : C) (records : List ρ) (observed : currentEntries (forest q) = some records)
    (record : ρ) (member : record ∈ records) : record ∈ source.tree.records := by
  obtain ⟨cursor,present,candidate⟩ := current_candidate (forest q) records observed record member
  exact candidates_inside color source forest represented q cursor present record candidate

omit [DecidableEq ι] [DecidableEq η] in
theorem parent_inside [DecidableEq α] (color : α → C) (source : Cursor α ρ)
    (forest : TaggedForest C α ρ ι) (represented : ProjectionForest.Represents color source (erase forest))
    (q : C) (records : List ρ) (observed : parentEntries (forest q) = some records)
    (record : ρ) (member : record ∈ records) : record ∈ source.tree.records := by
  obtain ⟨cursor,present,candidate⟩ := parent_candidate (forest q) records observed record member
  exact candidates_inside color source forest represented q cursor present record candidate

omit [DecidableEq ι] [LinearOrder C] in
theorem not_candidate (identifier : ρ → η) (wanted : ρ) (current : Cursor α (Payload ρ ι))
    (noCurrent : lookup identifier (identifier wanted) (currentEntries (some current)) = none)
    (noParent : lookup identifier (identifier wanted) (parentEntries (some current)) = none) :
    ¬Candidates current wanted := by
  intro candidate
  rcases candidate with here | ⟨parent,observed,there⟩
  · exact lookup_none_absent identifier wanted _ noCurrent _ rfl here
  · exact lookup_none_absent identifier wanted _ noParent _
      (by simp only [parentEntries,Option.bind_some,observed,Option.map_some]) there

end ChaCha.Paper20261030.PhysicalRecordFinder
