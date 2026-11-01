import Greedy.TicketRestoration
import Greedy.AccessMemoryRun

/-! Every physical link has a paired membership observation and arrival. -/

namespace Greedy.TicketJournal

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical Splay.Analysis
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.ActualLinks
open WinnerCredit

abbrev Ticket := MembershipPointer.Ticket

def pair {n : ℕ} (rank : ℕ → ℕ) (kind : EntryJournal.Kind)
    (oldTicket newTicket : Ticket) (event : External n × External n) : List (Action n) :=
  (if kind = .internal then [.win event.1 oldTicket] else []) ++
    [.entry event.2 event.1 kind newTicket,
      .change event.2 (contractedGap (rank event.2.val - rank event.1.val))]

theorem pair_erases {n : ℕ} (rank : ℕ → ℕ) (kind : EntryJournal.Kind)
    (oldTicket newTicket : Ticket) (event : External n × External n) :
    erase (pair rank kind oldTicket newTicket event) =
      [.entry event.2 event.1 kind, .change event.2 (contractedGap (rank event.2.val - rank event.1.val))] := by
  cases kind <;> rfl

theorem pair_paired {n : ℕ} (rank : ℕ → ℕ) (kind : EntryJournal.Kind)
    (oldTicket newTicket : Ticket) (event : External n × External n) :
    Paired (pair rank kind oldTicket newTicket event) := by
  cases kind with
  | ordinary => exact .ordinary _ _ _ (.change _ _ .nil)
  | boundary => exact .boundary _ _ _ (.change _ _ .nil)
  | internal => exact .internal _ _ _ _ (.change _ _ .nil)

theorem pair_legal {n : ℕ} (rank : ℕ → ℕ) (kind : EntryJournal.Kind)
    (oldTicket newTicket : Ticket) (event : External n × External n) (state : State n)
    (matching : state.ticket event.1 = oldTicket) :
    Legal state (pair rank kind oldTicket newTicket event) := by
  cases kind <;> simp [pair, Legal, matching]

theorem pair_ticket {n : ℕ} (rank : ℕ → ℕ) (kind : EntryJournal.Kind)
    (oldTicket newTicket : Ticket) (event : External n × External n) (state : State n) :
    (WinnerCredit.run state (pair rank kind oldTicket newTicket event)).ticket =
      Function.update state.ticket event.2 newTicket := by
  cases kind <;> rfl

theorem pair_account {n : ℕ} (rank : ℕ → ℕ) (kind : External n × External n → EntryJournal.Kind)
    (oldTicket newTicket : Ticket) (event : External n × External n) (state : State n) :
    (WinnerCredit.run state (pair rank (kind event) oldTicket newTicket event)).account =
      AccessJournal.advance rank kind state.account event := by
  rw [run_account, pair_erases]; rfl

theorem pair_remaining {n : ℕ} (rank : ℕ → ℕ) (kind : EntryJournal.Kind)
    (oldTicket newTicket ticket : Ticket) (event : External n × External n) :
    remaining (pair rank kind oldTicket newTicket event) ticket =
      if kind = .internal ∧ oldTicket = ticket then 1 else 0 := by
  cases kind <;> simp [pair, remaining, eq_comm]

def receivingTicket {n : ℕ} (states : States n) (event : External n × External n) (time : ℕ) : Ticket :=
  ((states event.1 (targetSide event)).grower.map Grower.family |>.getD 0, time)

noncomputable def links {n : ℕ} (rank : ℕ → ℕ) (K : ℤ)
    (source : External n) (sourceSide : External n × External n → Bool)
    (kind : External n × External n → EntryJournal.Kind) (oldTicket : External n → Ticket) :
    ℕ → States n → List (External n × External n) → List (Action n)
  | _, _, [] => []
  | time, states, event :: rest =>
      pair rank (kind event) (oldTicket event.1) (receivingTicket states event time) event ++
        links rank K source sourceSide kind oldTicket (time+1)
          (linkState states source event.1 event.2 (sourceSide event) (targetSide event)
            (arrivalEntry (GreedyMerge.StateLabels.label rank K states) event.1 event.2 time)) rest

theorem links_erases {n : ℕ} (rank : ℕ → ℕ) (K : ℤ)
    (source : External n) (sourceSide : External n × External n → Bool)
    (kind : External n × External n → EntryJournal.Kind) (oldTicket : External n → Ticket)
    (time : ℕ) (states : States n) (events : List (External n × External n)) :
    erase (links rank K source sourceSide kind oldTicket time states events) = AccessJournal.program rank kind events := by
  induction events generalizing time states with
  | nil => rfl
  | cons event rest ih => rw [links, erase_append, pair_erases, ih]; rfl

theorem links_paired {n : ℕ} (rank : ℕ → ℕ) (K : ℤ)
    (source : External n) (sourceSide : External n × External n → Bool)
    (kind : External n × External n → EntryJournal.Kind) (oldTicket : External n → Ticket)
    (time : ℕ) (states : States n) (events : List (External n × External n)) :
    Paired (links rank K source sourceSide kind oldTicket time states events) := by
  induction events generalizing time states with
  | nil => exact .nil
  | cons event rest ih => exact (pair_paired ..).append (ih (time+1) _)

theorem links_remaining {n : ℕ} (rank : ℕ → ℕ) (K : ℤ)
    (source : External n) (sourceSide : External n × External n → Bool)
    (kind : External n × External n → EntryJournal.Kind) (oldTicket : External n → Ticket)
    (time : ℕ) (states : States n) (events : List (External n × External n)) (ticket : Ticket) :
    remaining (links rank K source sourceSide kind oldTicket time states events) ticket =
      (events.map (fun event => if kind event = .internal ∧ oldTicket event.1 = ticket then 1 else 0)).sum := by
  induction events generalizing time states with
  | nil => rfl
  | cons event rest ih => rw [links, remaining_append, pair_remaining, ih]; rfl

end Greedy.TicketJournal
