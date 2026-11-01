import Greedy.TicketAccess
import Greedy.TicketRealizes

/-! Annotation certificates preserve one exact chronological journal. -/

namespace Greedy.TicketJournal

open Splay.Rank GreedyMerge.ActualLinks
open WinnerCredit

def Certifies {n : ℕ} (state : WeightedMemory.State (External n))
    (pointer : External n → Ticket) (after : States n)
    (actions : List (EntryJournal.Action (External n))) (wins : Ticket → ℕ) : Prop :=
  ∃ annotated : List (Action n), erase annotated = actions ∧
    Legal ⟨state, pointer⟩ annotated ∧ Paired annotated ∧
    MembershipPointer.Synced (WinnerCredit.run ⟨state, pointer⟩ annotated).ticket after ∧
    ∀ ticket, remaining annotated ticket = wins ticket

theorem state_after {n : ℕ} (state : WeightedMemory.State (External n))
    (pointer : External n → Ticket) (annotated : List (Action n))
    (actions : List (EntryJournal.Action (External n))) (erases : erase annotated = actions) :
    WinnerCredit.run ⟨state, pointer⟩ annotated =
      ⟨EntryJournal.run state actions, (WinnerCredit.run ⟨state, pointer⟩ annotated).ticket⟩ := by
  rw [← erases, ← run_account (⟨state, pointer⟩ : State n)]

theorem certifies_append {n : ℕ} (state : WeightedMemory.State (External n))
    (pointer : External n → Ticket) (after : States n)
    (first second : List (EntryJournal.Action (External n))) (firstWins secondWins : Ticket → ℕ)
    (annotated : List (Action n)) (erases : erase annotated = first)
    (legal : Legal ⟨state, pointer⟩ annotated) (paired : Paired annotated)
    (counts : ∀ ticket, remaining annotated ticket = firstWins ticket)
    (tail : Certifies (EntryJournal.run state first) (WinnerCredit.run ⟨state, pointer⟩ annotated).ticket
      after second secondWins) :
    Certifies state pointer after (first ++ second) (fun ticket => firstWins ticket + secondWins ticket) := by
  obtain ⟨rest, restErase, restLegal, restPaired, restSync, restCounts⟩ := tail
  have middle := state_after state pointer annotated first erases
  refine ⟨annotated ++ rest, ?_, ?_, paired.append restPaired, ?_, ?_⟩
  · rw [erase_append, erases, restErase]
  · rw [legal_append, middle]; exact ⟨legal, restLegal⟩
  · rw [run_append, middle]; exact restSync
  · intro ticket; rw [remaining_append, counts, restCounts]

theorem certifies_nil {n : ℕ} (state : WeightedMemory.State (External n))
    (pointer : External n → Ticket) (blocks : States n) (synced : MembershipPointer.Synced pointer blocks) :
    Certifies state pointer blocks [] (fun _ => 0) :=
  ⟨[], rfl, trivial, .nil, synced, fun _ => rfl⟩

end Greedy.TicketJournal
