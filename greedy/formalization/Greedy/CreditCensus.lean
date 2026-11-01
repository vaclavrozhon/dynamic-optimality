import Greedy.WinnerCredit
import Greedy.JournalKinds

/-! A paired win/entry journal counts internal links using current deficits. -/

namespace Greedy.EntryJournal

def creatorShift {Record : Type*} (state : WeightedMemory.State Record) : Action Record → ℤ
  | .entry record creator .internal => state.memory record - state.memory creator
  | _ => 0

end Greedy.EntryJournal

namespace Greedy.WinnerCredit

open EntryJournal
open scoped BigOperators

variable {Record Ticket : Type*} [Fintype Record] [DecidableEq Record] [DecidableEq Ticket]

/-- Every internal entry is immediately preceded by its actual winning
record observation. External entries and changes have no observation. -/
inductive Paired : List (Action Record Ticket) → Prop
  | nil : Paired []
  | change (record : Record) (label : ℤ) {rest} (tail : Paired rest) :
      Paired (.change record label :: rest)
  | ordinary (record creator : Record) (ticket : Ticket) {rest} (tail : Paired rest) :
      Paired (.entry record creator .ordinary ticket :: rest)
  | boundary (record creator : Record) (ticket : Ticket) {rest} (tail : Paired rest) :
      Paired (.entry record creator .boundary ticket :: rest)
  | internal (record creator : Record) (oldTicket newTicket : Ticket) {rest} (tail : Paired rest) :
      Paired (.win creator oldTicket :: .entry record creator .internal newTicket :: rest)

theorem census_bound (state : State Record Ticket) (actions : List (Action Record Ticket))
    (paired : Paired actions) :
    EntryJournal.total internal state.account (erase actions) ≤ observed state actions +
      EntryJournal.total shift state.account (erase actions) +
      EntryJournal.total creatorShift state.account (erase actions) := by
  induction paired generalizing state with
  | nil => simp [erase, EntryJournal.total, observed]
  | change record label _ ih =>
      have tail := ih (step state (.change record label))
      simpa only [erase, List.flatMap_cons, eraseOne, List.singleton_append, EntryJournal.total,
        internal, shift, EntryJournal.encode, WeightedMemory.shift, creatorShift, observed, step, zero_add] using tail
  | ordinary record creator ticket _ ih =>
      have tail := ih (step state (.entry record creator .ordinary ticket))
      simpa only [erase, List.flatMap_cons, eraseOne, List.singleton_append, EntryJournal.total,
        internal, shift, EntryJournal.encode, WeightedMemory.shift, creatorShift, observed, step,
        zero_add, beq_iff_eq, reduceCtorEq, if_false] using tail
  | boundary record creator ticket _ ih =>
      have tail := ih (step state (.entry record creator .boundary ticket))
      simpa only [erase, List.flatMap_cons, eraseOne, List.singleton_append, EntryJournal.total,
        internal, shift, EntryJournal.encode, WeightedMemory.shift, creatorShift, observed, step,
        zero_add, beq_iff_eq, reduceCtorEq, if_false] using tail
  | internal record creator oldTicket newTicket _ ih =>
      have tail := ih (step state (.entry record creator .internal newTicket))
      have deficit := GreedyForest.entryRank_add_deficit (state.account.label creator) (state.account.memory creator)
      unfold erase at tail
      simp only [erase, List.flatMap_cons, eraseOne, List.singleton_append, List.nil_append, EntryJournal.total,
        internal, shift, EntryJournal.encode, WeightedMemory.shift, creatorShift, observed, step,
        zero_add, beq_self_eq_true, if_true]
      dsimp only [step] at tail
      linarith

theorem potential_initial (credit : Ticket → ℕ) (capacity : ∀ ticket, credit ticket ≤ 4)
    (label : Record → ℤ) (ticket : Record → Ticket) :
    potential credit (⟨⟨label, label⟩, ticket⟩ : State Record Ticket) ≤ 4 * Fintype.card Record := by
  unfold potential cell
  simp only [GreedyForest.entryDeficit, sub_self, sub_zero, max_eq_right (by omega : (0 : ℤ) ≤ 1), mul_one]
  calc
    (∑ record, (credit (ticket record) : ℤ)) ≤ ∑ _record : Record, (4 : ℤ) := by
      apply Finset.sum_le_sum
      intro record _
      exact_mod_cast capacity (ticket record)
    _ = 4 * Fintype.card Record := by simp [mul_comm]

theorem internal_bound (label : Record → ℤ) (ticket : Record → Ticket)
    (actions : List (Action Record Ticket))
    (legal : Legal ⟨⟨label, label⟩, ticket⟩ actions)
    (paired : Paired actions) (capacity : ∀ name, remaining actions name ≤ 4) :
    let state : WeightedMemory.State Record := ⟨label, label⟩
    EntryJournal.total internal state (erase actions) ≤
      4*EntryJournal.total deficit state (erase actions) +
      4*EntryJournal.total negativeChange state (erase actions) +
      EntryJournal.total shift state (erase actions) +
      EntryJournal.total creatorShift state (erase actions) + 4*Fintype.card Record := by
  have counted := census_bound ⟨⟨label, label⟩, ticket⟩ actions paired
  have weighted := observed_bound ⟨⟨label, label⟩, ticket⟩ actions legal capacity
  have initial := potential_initial (remaining actions) capacity label ticket
  dsimp only at counted weighted ⊢
  linarith

end Greedy.WinnerCredit
