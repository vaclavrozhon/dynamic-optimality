import ChaCha.Paper20261030.PackedColorClassification
import ChaCha.Paper20261030.SourceProgramComposition

/-! Locally detaching the ancestor prefix at a projected root. Two
commands read the actual packed list, classify its entries by color-mask
inclusion, and write only the subtree's entries. The saved prefix is a
bounded part of one physical record list; no ancestor traversal is used.
-/

namespace ChaCha.Paper20261030.PackedPrefixController

open ColoredStorage SourcePointer SourceLocalProgram ProjectionLocal

variable {α ρ C : Type*} [LinearOrder C]

def outerEntries (mask : ρ → Finset C) (inside : Finset C) (records : List ρ) : List ρ :=
  records.filter (fun record => decide (¬ mask record ⊆ inside))

def innerEntries (mask : ρ → Finset C) (inside : Finset C) (records : List ρ) : List ρ :=
  records.filter (fun record => decide (mask record ⊆ inside))

theorem classify [DecidableEq α] (mask : ρ → Finset C) (color : α → C) (q : C)
    (source : Cursor α ρ) (correct : ColorsCorrect mask color source.tree)
    (present : q ∈ source.focus.support color) (physical : Cursor α (List ρ))
    (represented : ColoredStorage.Represents color q source physical) :
    ∃ (actual : Source α (List ρ)) (extras : List ρ) (rest : List (Frame α (List ρ))),
      packed color q source.focus = some actual ∧ physical = ⟨prepend extras actual,rest⟩ ∧
      outerEntries mask (source.focus.support color) physical.focus.rootRecord = extras ∧
      innerEntries mask (source.focus.support color) physical.focus.rootRecord = actual.rootRecord := by
  obtain ⟨actual,packedSource⟩ := packed_exists color q source.focus present
  obtain ⟨extras,rest,whole,frames,outer⟩ := packed_cursor_prefix mask color q source.focus actual
    packedSource source.ancestors correct
  have contextRep := represents_of_context color q source.focus source.ancestors packedSource extras rest whole frames
  have equal := Represents.unique color q source represented contextRep
  have inside : ∀ record ∈ actual.rootRecord, mask record ⊆ source.focus.support color := by
    intro record member
    have occurs := Source.rootRecords_mem actual member
    rw [packed_toStored color q source.focus packedSource] at occurs
    exact (ColorsCorrect.focus source.focus source.ancestors correct).subset (pack_records_mem color q source.focus occurs)
  have root : (prepend extras actual).rootRecord = extras ++ actual.rootRecord := by cases actual <;> rfl
  have outerKeep : outerEntries mask (source.focus.support color) extras = extras :=
    List.filter_eq_self.mpr (fun record member => by simpa only [decide_eq_true_eq] using outer record member)
  have outerDrop : outerEntries mask (source.focus.support color) actual.rootRecord = [] :=
    List.filter_eq_nil_iff.mpr (fun record member => by simpa only [decide_eq_true_eq,not_not] using inside record member)
  have innerDrop : innerEntries mask (source.focus.support color) extras = [] :=
    List.filter_eq_nil_iff.mpr (fun record member => by simpa only [decide_eq_true_eq] using outer record member)
  have innerKeep : innerEntries mask (source.focus.support color) actual.rootRecord = actual.rootRecord :=
    List.filter_eq_self.mpr (fun record member => by simpa only [decide_eq_true_eq] using inside record member)
  simp only [outerEntries] at outerKeep outerDrop
  simp only [innerEntries] at innerKeep innerDrop
  refine ⟨actual,extras,rest,packedSource,equal,?_,?_⟩
  · rw [equal]
    change outerEntries mask (source.focus.support color) (prepend extras actual).rootRecord = _
    rw [root]
    change _ = extras
    simpa only [outerEntries,List.filter_append,outerKeep,outerDrop,List.append_nil]
  · rw [equal]
    change innerEntries mask (source.focus.support color) (prepend extras actual).rootRecord = _
    rw [root]
    simpa only [innerEntries,List.filter_append,innerDrop,innerKeep,List.nil_append]

inductive State (ρ : Type*) where
  | start
  | writing (extras inside : List ρ)
  | done (extras : List ρ)

def program (mask : ρ → Finset C) (inside : Finset C) : Program (State ρ) (List ρ)
  | .start => .read (fun records _ => .writing (outerEntries mask inside records) (innerEntries mask inside records))
  | .writing extras records => .write records (.done extras)
  | .done _ => .halt

theorem detach [DecidableEq α] (mask : ρ → Finset C) (color : α → C) (q : C)
    (source : Cursor α ρ) (correct : ColorsCorrect mask color source.tree)
    (present : q ∈ source.focus.support color) (physical : Cursor α (List ρ))
    (represented : ColoredStorage.Represents color q source physical) :
    ∃ (actual : Source α (List ρ)) (extras : List ρ) (rest : List (Frame α (List ρ))),
      packed color q source.focus = some actual ∧ physical = ⟨prepend extras actual,rest⟩ ∧
      Run (program mask (source.focus.support color)) .start physical (.done extras)
        ⟨actual,rest⟩ [physical.focus.rootRecord] 2 := by
  obtain ⟨actual,extras,rest,packedSource,equal,outer,inner⟩ := classify mask color q source correct present physical represented
  have read := Step.read (program := program mask (source.focus.support color)) (state := .start) (cursor := physical)
    (next := fun records _ => State.writing (outerEntries mask (source.focus.support color) records)
      (innerEntries mask (source.focus.support color) records)) rfl
  rw [outer,inner] at read
  have write : Step (program mask (source.focus.support color)) (.writing extras actual.rootRecord) physical
      (.done extras) ⟨physical.focus.setRoot actual.rootRecord,physical.ancestors⟩ none := .write rfl
  have target : (⟨physical.focus.setRoot actual.rootRecord,physical.ancestors⟩ : Cursor α (List ρ)) = ⟨actual,rest⟩ := by
    rw [equal]; cases actual <;> rfl
  rw [target] at write
  exact ⟨actual,extras,rest,packedSource,equal,Run.next read (Run.next write (.halt rfl))⟩

end ChaCha.Paper20261030.PackedPrefixController
