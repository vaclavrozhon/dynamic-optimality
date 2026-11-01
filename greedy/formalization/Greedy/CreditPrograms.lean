import Greedy.CreditCensus

/-! Composition and projection of explicit membership observation programs. -/

namespace Greedy.WinnerCredit

open EntryJournal

variable {Record Ticket : Type*} [Fintype Record] [DecidableEq Record] [DecidableEq Ticket]

def run (state : State Record Ticket) : List (Action Record Ticket) → State Record Ticket
  | [] => state
  | action :: rest => run (step state action) rest

theorem run_append (state : State Record Ticket) (first second : List (Action Record Ticket)) :
    run state (first ++ second) = run (run state first) second := by
  induction first generalizing state with
  | nil => rfl
  | cons action rest ih => exact ih (step state action)

theorem erase_append (first second : List (Action Record Ticket)) : erase (first ++ second) = erase first ++ erase second :=
  List.flatMap_append

theorem run_account (state : State Record Ticket) (actions : List (Action Record Ticket)) :
    (run state actions).account = EntryJournal.run state.account (erase actions) := by
  induction actions generalizing state with
  | nil => rfl
  | cons action rest ih =>
      rw [run, ih]
      cases action <;> simp only [erase, List.flatMap_cons, eraseOne, List.singleton_append, List.nil_append, EntryJournal.run, step]

theorem legal_append (state : State Record Ticket) (first second : List (Action Record Ticket)) :
    Legal state (first ++ second) ↔ Legal state first ∧ Legal (run state first) second := by
  induction first generalizing state with
  | nil => simp [Legal, run]
  | cons action rest ih => simp only [List.cons_append, Legal, run, ih, and_assoc]

theorem Paired.append {first second : List (Action Record Ticket)} (left : Paired first) (right : Paired second) :
    Paired (first ++ second) := by
  induction left with
  | nil => exact right
  | change record label _ ih => exact .change record label ih
  | ordinary record creator ticket _ ih => exact .ordinary record creator ticket ih
  | boundary record creator ticket _ ih => exact .boundary record creator ticket ih
  | internal record creator oldTicket newTicket _ ih => exact .internal record creator oldTicket newTicket ih

theorem remaining_append (first second : List (Action Record Ticket)) (ticket : Ticket) :
    remaining (first ++ second) ticket = remaining first ticket + remaining second ticket := by
  induction first with
  | nil => simp [remaining]
  | cons action rest ih => cases action <;> simp [remaining, ih, Nat.add_assoc]

end Greedy.WinnerCredit
