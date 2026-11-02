import Mathlib.Data.Finset.Sort
import ChaCha.Paper20261030.ForestLocalProgram
import ChaCha.Paper20261030.PackedRecordDecoding

/-! Reading a logical record through the bounded color fingers. The
controller receives only the wanted immutable identifier and scans the
fixed list of colors. It does not receive the record's owner or position.
Every candidate is read at the current active or parked physical finger.
The owner guarantees success; uniqueness prevents a false match elsewhere.
-/

namespace ChaCha.Paper20261030.PackedReadController

open ColoredStorage SourcePointer ForestLocalProgram

variable {α ρ ι C : Type*} [DecidableEq ι] [LinearOrder C]

inductive State (C ρ : Type*) where
  | scan (remaining : List C)
  | found (color : C) (record : ρ)

def observe (identifier : ρ → ι) (wanted : ι) (remaining : List C) (q : C) : View ρ → State C ρ
  | none => .scan remaining
  | some (records,_) => match decodeRecord identifier wanted records with
      | none => .scan remaining
      | some record => .found q record

def program (identifier : ρ → ι) (wanted : ι) : Program (State C ρ) C ρ
  | .scan [] => .halt
  | .scan (q::rest) => .read q (observe identifier wanted rest q)
  | .found _ _ => .halt

theorem decode_sound [DecidableEq α] (identifier : ρ → ι) (color : α → C) (q : C)
    (source : Cursor α ρ) (physical : Cursor α (List ρ))
    (represented : ColoredStorage.Represents color q source physical)
    (unique : Distinguishes identifier source.tree) (record : ρ)
    (decoded : decodeRecord identifier (identifier source.focus.rootRecord) physical.focus.rootRecord = some record) :
    record = source.focus.rootRecord := by
  have member := List.mem_of_find?_eq_some decoded
  have same := List.find?_some decoded
  exact unique record (represented_record_mem color q source represented member)
    source.focus.rootRecord (records_focus _ _ source.focus.rootRecord_mem)
    (by simpa only [decide_eq_true_eq] using same)

theorem scan [DecidableEq α] [Fintype C] (identifier : ρ → ι) (color : α → C)
    (source : Cursor α ρ) (forest : ProjectionForest.State C α ρ)
    (represented : ProjectionForest.Represents color source forest)
    (unique : Distinguishes identifier source.tree) (colors : List C)
    (owner : source.focus.rootOwner color ∈ colors) :
    ∃ q reads cost,
      Run (program identifier (identifier source.focus.rootRecord)) (.scan colors) forest
        (.found q source.focus.rootRecord) forest reads cost ∧ cost ≤ colors.length ∧
      ∀ entry ∈ reads, entry.2.length ≤ Fintype.card C := by
  induction colors with
  | nil => simp only [List.not_mem_nil] at owner
  | cons q rest ih =>
    let code := program (C := C) identifier (identifier source.focus.rootRecord)
    have member : source.focus.rootOwner color ∈ source.tree.support color :=
      ProjectionForest.support_focus color source.focus source.ancestors (Source.rootOwner_mem color source.focus)
    have atRep := represented q
    cases location : forest q with
    | none =>
      rw [location] at atRep
      have different : source.focus.rootOwner color ≠ q := by
        intro equal
        exact atRep (equal ▸ member)
      have remains : source.focus.rootOwner color ∈ rest := (List.mem_cons.mp owner).resolve_left different
      obtain ⟨selected,reads,cost,tail,bounded,capacity⟩ := ih remains
      have first : Step code (.scan (q::rest)) forest (.scan rest) forest none :=
        .readNone (next := observe identifier (identifier source.focus.rootRecord) rest q) rfl location
      exact ⟨selected,reads,cost+1,Run.next first tail,by simp only [List.length_cons]; omega,capacity⟩
    | some physical =>
      rw [location] at atRep
      have capacity := represented_capacity color q source atRep
      have first := Step.readSome (program := code) (state := .scan (q::rest))
        (next := observe identifier (identifier source.focus.rootRecord) rest q) rfl location
      cases decoded : decodeRecord identifier (identifier source.focus.rootRecord) physical.focus.rootRecord with
      | none =>
        have different : source.focus.rootOwner color ≠ q := by
          intro equal
          have atOwner : ColoredStorage.Represents color (source.focus.rootOwner color) source physical := equal ▸ atRep
          have found := (read_decodes identifier color source unique atOwner).2.1
          rw [decoded] at found
          cases found
        have remains : source.focus.rootOwner color ∈ rest := (List.mem_cons.mp owner).resolve_left different
        obtain ⟨selected,reads,cost,tail,bounded,tailCapacity⟩ := ih remains
        have read : Step code (.scan (q::rest)) forest (.scan rest) forest (some (q,physical.focus.rootRecord)) := by
          simpa only [observe,decoded] using first
        refine ⟨selected,(q,physical.focus.rootRecord)::reads,cost+1,Run.next read tail,
          by simp only [List.length_cons]; omega,?_⟩
        intro entry occurs
        rcases List.mem_cons.mp occurs with rfl | later
        · exact capacity
        · exact tailCapacity entry later
      | some record =>
        have exactRecord := decode_sound identifier color q source physical atRep unique record decoded
        subst record
        have read : Step code (.scan (q::rest)) forest (.found q source.focus.rootRecord) forest
            (some (q,physical.focus.rootRecord)) := by simpa only [observe,decoded] using first
        refine ⟨q,[(q,physical.focus.rootRecord)],1,Run.next read (.halt rfl),
          by simp only [List.length_cons]; omega,?_⟩
        intro entry occurs
        have equal := List.mem_singleton.mp occurs
        subst entry
        exact capacity

theorem read [DecidableEq α] [Fintype C] (identifier : ρ → ι) (color : α → C)
    (source : Cursor α ρ) (forest : ProjectionForest.State C α ρ)
    (represented : ProjectionForest.Represents color source forest)
    (unique : Distinguishes identifier source.tree) :
    ∃ q reads cost,
      Run (program identifier (identifier source.focus.rootRecord)) (.scan (Finset.univ.sort (· ≤ ·))) forest
        (.found q source.focus.rootRecord) forest reads cost ∧ cost ≤ Fintype.card C ∧
      ∀ entry ∈ reads, entry.2.length ≤ Fintype.card C := by
  simpa only [Finset.length_sort,Finset.card_univ] using
    scan identifier color source forest represented unique (Finset.univ.sort (· ≤ ·)) (by simp)

end ChaCha.Paper20261030.PackedReadController
