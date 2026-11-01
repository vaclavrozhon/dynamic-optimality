import TangoSquared.Paper20261030.PackedWriteDecision
import TangoSquared.Paper20261030.LocalPackedRead

/-! A complete read-driven packed-record write. The controller scans the
fixed color list, compares the immutable identifier with actual records,
and updates its unique matching slot. It neither receives the owning color
nor assumes a physical address for the logical record.
-/

namespace TangoSquared.Paper20261030.PackedWriteController

open ColoredStorage SourcePointer ForestLocalProgram

variable {α ρ ι C : Type*} [DecidableEq ι] [LinearOrder C]

inductive State (C ρ : Type*) where
  | scan (colors : List C)
  | writing (q : C) (records : List ρ)
  | done

def observe (identifier : ρ → ι) (wanted : ι) (fresh : ρ) (q : C) (rest : List C) : View ρ → State C ρ
  | none => .scan rest
  | some (records,_) => match decodeRecord identifier wanted records with
    | none => .scan rest
    | some _ => .writing q (updateEntries identifier wanted fresh records)

def program (identifier : ρ → ι) (wanted : ι) (fresh : ρ) : Program (State C ρ) C ρ
  | .scan [] => .halt
  | .scan (q::rest) => .read q (observe identifier wanted fresh q rest)
  | .writing q records => .write q records .done
  | .done => .halt

theorem write_forest [DecidableEq α] [Fintype C] (identifier : ρ → ι) (color : α → C)
    (source : Cursor α ρ) (fresh : ρ) (forest : ProjectionForest.State C α ρ)
    (represented : ProjectionForest.Represents color source forest) (unique : (source.tree.inventory identifier).Nodup)
    (q : C) (physical : Cursor α (List ρ)) (present : forest q = some physical)
    (member : source.focus.rootRecord ∈ physical.focus.rootRecord) :
    ProjectionForest.Represents color ⟨source.focus.setRoot fresh,source.ancestors⟩
      (Function.update forest q (some
        ⟨physical.focus.setRoot (updateEntries identifier (identifier source.focus.rootRecord) fresh physical.focus.rootRecord),
          physical.ancestors⟩)) := by
  have owner := represented_record_color identifier color source forest represented unique q physical present member
  have selected := represented q
  rw [present] at selected
  have selectedOwner : ColoredStorage.Represents color (source.focus.rootOwner color) source physical := owner ▸ selected
  have written := write_record_exact identifier color source fresh unique selectedOwner
  have support : source.tree.support color = (Cursor.tree ⟨source.focus.setRoot fresh,source.ancestors⟩).support color := by
    rw [Source.support_leaves,Source.support_leaves,(SourcePointer.Step.write source.focus fresh source.ancestors).leaves]
  intro other
  by_cases equal : other = q
  · subst other
    simp only [Function.update_self,ProjectionForest.RepresentsAt]
    exact owner ▸ written
  · rw [Function.update_of_ne equal]
    have previous := represented other
    cases location : forest other with
    | none =>
      rw [location] at previous
      simpa only [ProjectionForest.RepresentsAt,← support] using previous
    | some cursor =>
      rw [location] at previous
      exact write_other color other source fresh (owner ▸ equal) previous

theorem scan [DecidableEq α] [Fintype C] (identifier : ρ → ι) (color : α → C)
    (source : Cursor α ρ) (fresh : ρ) (forest : ProjectionForest.State C α ρ)
    (represented : ProjectionForest.Represents color source forest) (unique : (source.tree.inventory identifier).Nodup)
    (colors : List C) (owner : source.focus.rootOwner color ∈ colors) :
    ∃ target reads cost,
      Run (program identifier (identifier source.focus.rootRecord) fresh) (.scan colors) forest .done target reads cost ∧
      ProjectionForest.Represents color ⟨source.focus.setRoot fresh,source.ancestors⟩ target ∧ cost ≤ colors.length+1 := by
  have distinguishes : Distinguishes identifier source.tree := Multiset.inj_on_of_nodup_map unique
  induction colors with
  | nil => simp only [List.not_mem_nil] at owner
  | cons q rest ih =>
    let code := program (C := C) identifier (identifier source.focus.rootRecord) fresh
    have member : source.focus.rootOwner color ∈ source.tree.support color :=
      ProjectionForest.support_focus color source.focus source.ancestors (Source.rootOwner_mem color source.focus)
    have atRep := represented q
    cases location : forest q with
    | none =>
      rw [location] at atRep
      have different : source.focus.rootOwner color ≠ q := fun equal => atRep (equal ▸ member)
      obtain ⟨target,reads,cost,tail,targetRep,bounded⟩ := ih ((List.mem_cons.mp owner).resolve_left different)
      have first : Step code (.scan (q::rest)) forest (.scan rest) forest none :=
        .readNone (next := observe identifier (identifier source.focus.rootRecord) fresh q rest) rfl location
      exact ⟨target,reads,cost+1,Run.next first tail,targetRep,by simp only [List.length_cons]; omega⟩
    | some physical =>
      rw [location] at atRep
      have first := Step.readSome (program := code) (state := .scan (q::rest))
        (next := observe identifier (identifier source.focus.rootRecord) fresh q rest) rfl location
      cases decoded : decodeRecord identifier (identifier source.focus.rootRecord) physical.focus.rootRecord with
      | none =>
        have different : source.focus.rootOwner color ≠ q := by
          intro equal
          have atOwner : ColoredStorage.Represents color (source.focus.rootOwner color) source physical := equal ▸ atRep
          have found := (read_decodes identifier color source distinguishes atOwner).2.1
          rw [decoded] at found
          cases found
        obtain ⟨target,reads,cost,tail,targetRep,bounded⟩ := ih ((List.mem_cons.mp owner).resolve_left different)
        have read : Step code (.scan (q::rest)) forest (.scan rest) forest (some (q,physical.focus.rootRecord)) := by
          simpa only [observe,decoded] using first
        exact ⟨target,(q,physical.focus.rootRecord)::reads,cost+1,Run.next read tail,targetRep,
          by simp only [List.length_cons]; omega⟩
      | some record =>
        have exactRecord := PackedReadController.decode_sound identifier color q source physical atRep distinguishes record decoded
        subst record
        let records := updateEntries identifier (identifier source.focus.rootRecord) fresh physical.focus.rootRecord
        have read : Step code (.scan (q::rest)) forest (.writing q records) forest (some (q,physical.focus.rootRecord)) := by
          simpa only [observe,decoded] using first
        have write : Step code (.writing q records) forest .done
            (Function.update forest q (some ⟨physical.focus.setRoot records,physical.ancestors⟩)) none := .write rfl location
        have targetRep := write_forest identifier color source fresh forest represented unique q physical location
          (List.mem_of_find?_eq_some decoded)
        exact ⟨_,[(q,physical.focus.rootRecord)],2,Run.next read (Run.next write (.halt rfl)),targetRep,
          by simp only [List.length_cons]; omega⟩

theorem write [DecidableEq α] [Fintype C] (identifier : ρ → ι) (color : α → C)
    (source : Cursor α ρ) (fresh : ρ) (forest : ProjectionForest.State C α ρ)
    (represented : ProjectionForest.Represents color source forest) (unique : (source.tree.inventory identifier).Nodup) :
    ∃ target reads cost,
      Run (program identifier (identifier source.focus.rootRecord) fresh) (.scan (Finset.univ.sort (· ≤ ·)))
        forest .done target reads cost ∧
      ProjectionForest.Represents color ⟨source.focus.setRoot fresh,source.ancestors⟩ target ∧ cost ≤ Fintype.card C+1 := by
  simpa only [Finset.length_sort,Finset.card_univ] using
    scan identifier color source fresh forest represented unique (Finset.univ.sort (· ≤ ·)) (by simp)

end TangoSquared.Paper20261030.PackedWriteController
