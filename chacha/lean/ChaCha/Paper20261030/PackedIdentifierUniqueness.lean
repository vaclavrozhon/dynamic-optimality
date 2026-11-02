import ChaCha.Paper20261030.PackedRecordDecoding
import ChaCha.Paper20261030.SourceRecordInventory

/-! Immutable identifiers locate a single physical packed record. The
packing conserves the full multiset, so unique source identifiers imply
unique slots and disjoint identifier sets in distinct color trees.
These facts justify writes selected by an actual identifier comparison.
-/

namespace ChaCha.Paper20261030.ColoredStorage

open SourcePointer

variable {α ρ ι C : Type*} [LinearOrder C] [Fintype C]

theorem packed_inventory_sum (identifier : ρ → ι) (color : α → C) (source : Source α ρ) :
    ∑ q : C, (pack color q source).records.map identifier = source.inventory identifier := by
  induction source with
  | leaf key record => simp [pack,apply_ite,Stored.records,Source.inventory_leaf,eq_comm]
  | fork record l r ihl ihr =>
    simp only [pack_fork_records,Multiset.map_add,Finset.sum_add_distrib,ihl,ihr,Source.inventory_fork]
    simp [apply_ite,eq_comm,add_assoc,add_comm,add_left_comm]

theorem packed_inventory_le (identifier : ρ → ι) (color : α → C) (q : C) (source : Source α ρ) :
    (pack color q source).records.map identifier ≤ source.inventory identifier := by
  rw [← packed_inventory_sum identifier color source]
  exact Finset.single_le_sum (fun c _ => (show 0 ≤ (pack color c source).records.map identifier from zero_le)) (Finset.mem_univ q)

theorem packed_inventory_disjoint (identifier : ρ → ι) (color : α → C) (source : Source α ρ)
    (unique : (source.inventory identifier).Nodup) (q p : C) (different : q ≠ p) :
    Disjoint ((pack color q source).records.map identifier) ((pack color p source).records.map identifier) := by
  let parts := fun c => (pack color c source).records.map identifier
  have firstLe : parts q ≤ ∑ c ∈ Finset.univ.erase p, parts c :=
    Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_erase.mpr ⟨different,Finset.mem_univ _⟩)
  have pairLe : parts q + parts p ≤ source.inventory identifier := by
    calc
      parts q + parts p ≤ (∑ c ∈ Finset.univ.erase p, parts c) + parts p := add_le_add firstLe le_rfl
      _ = ∑ c : C, parts c := Finset.sum_erase_add _ _ (Finset.mem_univ p)
      _ = source.inventory identifier := packed_inventory_sum identifier color source
  exact (Multiset.nodup_add.mp (Multiset.nodup_of_le pairLe unique)).2.2

omit [LinearOrder C] [Fintype C] in
theorem stored_root_inventory_le (identifier : ρ → ι) (focus : Source α (List ρ)) :
    (focus.rootRecord : Multiset ρ).map identifier ≤ focus.toStored.records.map identifier := by
  apply Multiset.map_le_map
  cases focus with
  | leaf => exact le_rfl
  | fork records l r =>
    exact (le_add_of_nonneg_right (show 0 ≤ l.toStored.records from zero_le)).trans
      (le_add_of_nonneg_right zero_le)

omit [LinearOrder C] [Fintype C] in
theorem stored_inventory_le_plug (identifier : ρ → ι) (focus : Source α (List ρ)) (outside : List (Frame α (List ρ))) :
    focus.toStored.records.map identifier ≤ (plug focus outside).toStored.records.map identifier := by
  induction outside generalizing focus with
  | nil => exact le_rfl
  | cons frame rest ih =>
    cases frame with
    | left records sibling =>
      apply le_trans _ (ih (.fork records focus sibling))
      simp only [Source.toStored,Stored.records,Multiset.map_add]
      exact (le_add_of_nonneg_left zero_le).trans (le_add_of_nonneg_right zero_le)
    | right sibling records =>
      apply le_trans _ (ih (.fork records sibling focus))
      simp only [Source.toStored,Stored.records,Multiset.map_add]
      exact le_add_of_nonneg_left zero_le

theorem represented_root_inventory_le [DecidableEq α] (identifier : ρ → ι) (color : α → C) (q : C)
    (source : Cursor α ρ) (physical : Cursor α (List ρ))
    (represented : Represents color q source physical) :
    (physical.focus.rootRecord : Multiset ρ).map identifier ≤ source.tree.inventory identifier := by
  have rootLe := (stored_root_inventory_le identifier physical.focus).trans
    (stored_inventory_le_plug identifier physical.focus physical.ancestors)
  change _ ≤ physical.tree.toStored.records.map identifier at rootLe
  rw [packed_toStored color q source.tree represented.1] at rootLe
  exact rootLe.trans (packed_inventory_le identifier color q source.tree)

theorem represented_root_unique [DecidableEq α] (identifier : ρ → ι) (color : α → C) (q : C)
    (source : Cursor α ρ) (physical : Cursor α (List ρ))
    (represented : Represents color q source physical) (unique : (source.tree.inventory identifier).Nodup) :
    (physical.focus.rootRecord.map identifier).Nodup := by
  have small := Multiset.nodup_of_le (represented_root_inventory_le identifier color q source physical represented) unique
  simpa only [Multiset.map_coe,Multiset.coe_nodup] using small

theorem represented_record_color [DecidableEq α] (identifier : ρ → ι) (color : α → C)
    (source : Cursor α ρ) (forest : ProjectionForest.State C α ρ)
    (represented : ProjectionForest.Represents color source forest) (unique : (source.tree.inventory identifier).Nodup)
    (q : C) (physical : Cursor α (List ρ)) (present : forest q = some physical)
    (occurs : source.focus.rootRecord ∈ physical.focus.rootRecord) : q = source.focus.rootOwner color := by
  by_contra different
  let owner := source.focus.rootOwner color
  have inWhole : owner ∈ source.tree.support color :=
    ProjectionForest.support_focus color source.focus source.ancestors (Source.rootOwner_mem color source.focus)
  have ownerRep := represented owner
  cases location : forest owner with
  | none => rw [location] at ownerRep; exact ownerRep inWhole
  | some ownerCursor =>
    rw [location] at ownerRep
    have selectedRep := represented q
    rw [present] at selectedRep
    obtain ⟨_,ownerMember,_⟩ := read_record color source ownerRep
    have there := stored_records_focus physical.focus physical.ancestors (Source.rootRecords_mem _ occurs)
    have here := stored_records_focus ownerCursor.focus ownerCursor.ancestors (Source.rootRecords_mem _ ownerMember)
    change _ ∈ physical.tree.toStored.records at there
    change _ ∈ ownerCursor.tree.toStored.records at here
    rw [packed_toStored color q source.tree selectedRep.1] at there
    rw [packed_toStored color owner source.tree ownerRep.1] at here
    have separate := packed_inventory_disjoint identifier color source.tree unique q owner different
    exact Multiset.disjoint_left.mp separate (Multiset.mem_map.mpr ⟨_,there,rfl⟩)
      (Multiset.mem_map.mpr ⟨_,here,rfl⟩)

end ChaCha.Paper20261030.ColoredStorage
