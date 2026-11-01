import Greedy.TicketPreparation

/-! Administrative annotation witnesses compose with the literal plain journal. -/

namespace Greedy.TicketJournal

open Splay.Rank GreedyMerge.ActualLinks
open WinnerCredit

def Realizes {n : ℕ} (before after : States n) (actions : List (EntryJournal.Action (External n))) : Prop :=
  ∀ state : State n, MembershipPointer.Synced state.ticket before →
    ∃ annotated : List (Action n), erase annotated = actions ∧ Administrative annotated ∧
      MembershipPointer.Synced (WinnerCredit.run state annotated).ticket after

theorem Realizes.nil {n : ℕ} (states : States n) : Realizes states states [] := by
  intro state synced
  exact ⟨[], rfl, by simp [Administrative], synced⟩

theorem Realizes.append {n : ℕ} {before middle after : States n}
    {first second : List (EntryJournal.Action (External n))}
    (left : Realizes before middle first) (right : Realizes middle after second) :
    Realizes before after (first ++ second) := by
  intro state synced
  obtain ⟨head, headErase, headAdmin, headSync⟩ := left state synced
  obtain ⟨tail, tailErase, tailAdmin, tailSync⟩ := right (WinnerCredit.run state head) headSync
  refine ⟨head ++ tail, ?_, (administrative_append ..).mpr ⟨headAdmin, tailAdmin⟩, ?_⟩
  · rw [erase_append, headErase, tailErase]
  · rw [run_append]; exact tailSync

end Greedy.TicketJournal
