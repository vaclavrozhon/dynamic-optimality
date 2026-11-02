import ChaCha.Paper20261030.PackedForest

/-!
# Decoding a source record from its actual bounded physical read

The source cursor carries an immutable record identifier. When identifiers
distinguish the records in the maintained component, searching the reached
record list returns exactly the current source record. Every candidate in
that list is proved to be a record of the actual source component, and the
list has length at most the number of colors. Establishing and maintaining
the identifiers and child identifiers in Tango's metadata is separate.
-/

namespace ChaCha.Paper20261030.ColoredStorage

open SourcePointer

variable {α ρ C : Type*} [LinearOrder C]

theorem pack_records_mem (color : α → C) (q : C) (source : Source α ρ) {record : ρ}
    (member : record ∈ (pack color q source).records) : record ∈ source.records := by
  induction source with
  | leaf key value =>
    by_cases equal : color key = q
    · simpa only [pack,if_pos equal,Stored.records,Source.records,Multiset.mem_coe,List.mem_singleton,
        Multiset.mem_singleton] using member
    · simp only [pack,if_neg equal,Stored.records,Multiset.notMem_zero] at member
  | fork value l r ihl ihr =>
    rw [pack_fork_records] at member
    rcases Multiset.mem_add.mp member with member | member
    · rcases Multiset.mem_add.mp member with member | member
      · simp only [Source.records,Multiset.mem_add]
        exact Or.inl (Or.inr (ihl member))
      · simp only [Source.records,Multiset.mem_add]
        exact Or.inr (ihr member)
    · split_ifs at member with owner
      · simpa only [Source.records,Multiset.mem_add] using Or.inl (Or.inl member)
      · exact False.elim (Multiset.notMem_zero _ member)

theorem Source.rootRecord_mem (source : Source α ρ) : source.rootRecord ∈ source.records := by
  cases source <;> simp [Source.rootRecord,Source.records]

theorem records_focus (focus : Source α ρ) (ancestors : List (Frame α ρ)) {record : ρ}
    (member : record ∈ focus.records) : record ∈ (plug focus ancestors).records := by
  induction ancestors generalizing focus with
  | nil => exact member
  | cons frame rest ih =>
    cases frame with
    | left value sibling => exact ih (.fork value focus sibling) (by simp [Source.records,member])
    | right sibling value => exact ih (.fork value sibling focus) (by simp [Source.records,member])

theorem Source.rootRecords_mem (source : Source α (List ρ)) {record : ρ}
    (member : record ∈ source.rootRecord) : record ∈ source.toStored.records := by
  cases source <;> simp_all [Source.rootRecord,Source.toStored,Stored.records]

theorem stored_records_focus (focus : Source α (List ρ)) (ancestors : List (Frame α (List ρ))) {record : ρ}
    (member : record ∈ focus.toStored.records) : record ∈ (plug focus ancestors).toStored.records := by
  induction ancestors generalizing focus with
  | nil => exact member
  | cons frame rest ih =>
    cases frame with
    | left value sibling => exact ih (.fork value focus sibling) (by simp [Source.toStored,Stored.records,member])
    | right sibling value => exact ih (.fork value sibling focus) (by simp [Source.toStored,Stored.records,member])

theorem represented_record_mem [DecidableEq α] (color : α → C) (q : C) (source : Cursor α ρ)
    {physical : Cursor α (List ρ)} (represented : Represents color q source physical)
    {record : ρ} (member : record ∈ physical.focus.rootRecord) : record ∈ source.tree.records := by
  have full := stored_records_focus physical.focus physical.ancestors (Source.rootRecords_mem _ member)
  change record ∈ physical.tree.toStored.records at full
  rw [packed_toStored color q source.tree represented.1] at full
  exact pack_records_mem color q source.tree full

def Distinguishes {ι : Type*} (identifier : ρ → ι) (source : Source α ρ) : Prop :=
  ∀ a ∈ source.records, ∀ b ∈ source.records, identifier a = identifier b → a = b

def decodeRecord {ι : Type*} [DecidableEq ι] (identifier : ρ → ι) (wanted : ι) (records : List ρ) : Option ρ :=
  records.find? (fun record => decide (identifier record = wanted))

theorem decodeRecord_exact {ι : Type*} [DecidableEq ι] (identifier : ρ → ι)
    (source : Source α ρ) (unique : Distinguishes identifier source)
    (records : List ρ) (inside : ∀ record ∈ records, record ∈ source.records)
    (wanted : ρ) (present : wanted ∈ records) :
    decodeRecord identifier (identifier wanted) records = some wanted := by
  unfold decodeRecord
  cases result : records.find? (fun record => decide (identifier record = identifier wanted)) with
  | none =>
    have absent := List.find?_eq_none.mp result wanted present
    exact False.elim (absent (by simp))
  | some actual =>
    have member := List.mem_of_find?_eq_some result
    have same := List.find?_some result
    have equality : actual = wanted := unique actual (inside actual member) wanted (inside wanted present)
      (by simpa only [decide_eq_true_eq] using same)
    rw [equality]

theorem read_decodes [DecidableEq α] [Fintype C] {ι : Type*} [DecidableEq ι]
    (identifier : ρ → ι) (color : α → C) (source : Cursor α ρ)
    (unique : Distinguishes identifier source.tree)
    {physical : Cursor α (List ρ)}
    (represented : Represents color (source.focus.rootOwner color) source physical) :
    SourcePointer.Trace physical [physical.focus.rootRecord] physical 1 ∧
      decodeRecord identifier (identifier source.focus.rootRecord) physical.focus.rootRecord = some source.focus.rootRecord ∧
      physical.focus.rootRecord.length ≤ Fintype.card C := by
  obtain ⟨trace,present,bounded⟩ := read_record color source represented
  exact ⟨trace,decodeRecord_exact identifier source.tree unique physical.focus.rootRecord
    (fun record member => represented_record_mem color _ source represented member) _ present,bounded⟩

end ChaCha.Paper20261030.ColoredStorage
