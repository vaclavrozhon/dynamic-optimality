import Greedy.JournalVariation

/-!
Remaining internal wins provide a direct potential for weighted winner charges.
A membership ticket is the pair consisting of its family and original join time.
The generic theorem below uses an explicit observation journal; the geometric
run must still supply that journal and its already proved four-win capacity.
-/

namespace Greedy.WinnerCredit

open scoped BigOperators
open EntryJournal

variable {Record Ticket : Type*} [Fintype Record] [DecidableEq Record] [DecidableEq Ticket]

structure State (Record Ticket : Type*) where
  account : WeightedMemory.State Record
  ticket : Record → Ticket

inductive Action (Record Ticket : Type*) where
  | change (record : Record) (label : ℤ)
  | entry (record creator : Record) (kind : Kind) (ticket : Ticket)
  | win (record : Record) (ticket : Ticket)

def eraseOne : Action Record Ticket → List (EntryJournal.Action Record)
  | .change record label => [.change record label]
  | .entry record creator kind _ => [.entry record creator kind]
  | .win _ _ => []

def erase (actions : List (Action Record Ticket)) : List (EntryJournal.Action Record) := actions.flatMap eraseOne

def step (state : State Record Ticket) : Action Record Ticket → State Record Ticket
  | .change record label => ⟨EntryJournal.step state.account (.change record label), state.ticket⟩
  | .entry record creator kind ticket =>
      ⟨EntryJournal.step state.account (.entry record creator kind), Function.update state.ticket record ticket⟩
  | .win _ _ => state

def remaining : List (Action Record Ticket) → Ticket → ℕ
  | [] => fun _ => 0
  | .win _ ticket :: rest => fun query => (if query = ticket then 1 else 0) + remaining rest query
  | _ :: rest => remaining rest

def Legal (state : State Record Ticket) : List (Action Record Ticket) → Prop
  | [] => True
  | action :: rest =>
      (match action with
       | .win record ticket => state.ticket record = ticket
       | _ => True) ∧ Legal (step state action) rest

def observed (state : State Record Ticket) : List (Action Record Ticket) → ℤ
  | [] => 0
  | action :: rest =>
      (match action with
       | .win record _ => GreedyForest.entryDeficit (state.account.label record) (state.account.memory record)
       | _ => 0) + observed (step state action) rest

def cell (credit : Ticket → ℕ) (state : State Record Ticket) (record : Record) : ℤ :=
  (credit (state.ticket record) : ℤ) * GreedyForest.entryDeficit (state.account.label record) (state.account.memory record)

def potential (credit : Ticket → ℕ) (state : State Record Ticket) : ℤ := ∑ record, cell credit state record

theorem cell_nonneg (credit : Ticket → ℕ) (state : State Record Ticket) (record : Record) :
    0 ≤ cell credit state record := mul_nonneg (by positivity) (GreedyForest.entryDeficit_nonneg _ _)

theorem potential_nonneg (credit : Ticket → ℕ) (state : State Record Ticket) :
    0 ≤ potential credit state := Finset.sum_nonneg (fun record _ => cell_nonneg credit state record)

theorem change_one (credit : Ticket → ℕ) (before after : State Record Ticket) (record : Record)
    (outside : ∀ other, other ≠ record → cell credit after other = cell credit before other) :
    potential credit after = potential credit before - cell credit before record + cell credit after record := by
  have first := Finset.sum_erase_add Finset.univ (cell credit before) (Finset.mem_univ record)
  have last := Finset.sum_erase_add Finset.univ (cell credit after) (Finset.mem_univ record)
  have equal : ∑ other ∈ Finset.univ.erase record, cell credit after other =
      ∑ other ∈ Finset.univ.erase record, cell credit before other := by
    apply Finset.sum_congr rfl
    intro other member
    exact outside other (Finset.mem_erase.mp member).1
  unfold potential
  rw [← first, ← last, equal]
  ring

theorem entry_bound (credit : Ticket → ℕ) (bounded : ∀ ticket, credit ticket ≤ 4)
    (state : State Record Ticket) (record creator : Record) (kind : Kind) (ticket : Ticket) :
    potential credit (step state (.entry record creator kind ticket)) ≤ potential credit state +
      4*GreedyForest.entryDeficit (state.account.label record) (state.account.label creator) := by
  have equality := change_one credit state (step state (.entry record creator kind ticket)) record (by
    intro other different
    simp [cell, step, EntryJournal.step, encode, WeightedMemory.step, Function.update_of_ne different])
  have newCell : cell credit (step state (.entry record creator kind ticket)) record =
      (credit ticket : ℤ) * GreedyForest.entryDeficit (state.account.label record) (state.account.label creator) := by
    simp [cell, step, EntryJournal.step, encode, WeightedMemory.step]
  have bound : (credit ticket : ℤ) ≤ 4 := by exact_mod_cast bounded ticket
  rw [equality, newCell]
  nlinarith [cell_nonneg credit state record, GreedyForest.entryDeficit_nonneg (state.account.label record) (state.account.label creator)]

theorem change_bound (credit : Ticket → ℕ) (bounded : ∀ ticket, credit ticket ≤ 4)
    (state : State Record Ticket) (record : Record) (label : ℤ) :
    potential credit (step state (.change record label)) ≤ potential credit state +
      4*max 0 (state.account.label record - label) := by
  have equality := change_one credit state (step state (.change record label)) record (by
    intro other different
    simp [cell, step, EntryJournal.step, encode, WeightedMemory.step, Function.update_of_ne different])
  have newCell : cell credit (step state (.change record label)) record =
      (credit (state.ticket record) : ℤ) * GreedyForest.entryDeficit label (state.account.memory record) := by
    simp [cell, step, EntryJournal.step, encode, WeightedMemory.step]
  have bound : (credit (state.ticket record) : ℤ) ≤ 4 := by exact_mod_cast bounded (state.ticket record)
  have nonnegative : 0 ≤ (credit (state.ticket record) : ℤ) := by positivity
  have deficit : GreedyForest.entryDeficit label (state.account.memory record) ≤
      GreedyForest.entryDeficit (state.account.label record) (state.account.memory record) + max 0 (state.account.label record - label) := by
    unfold GreedyForest.entryDeficit
    omega
  rw [equality, newCell]
  unfold cell
  nlinarith [le_max_left 0 (state.account.label record - label)]

theorem win_bound (rest : List (Action Record Ticket)) (state : State Record Ticket)
    (record : Record) (ticket : Ticket) (matching : state.ticket record = ticket) :
    GreedyForest.entryDeficit (state.account.label record) (state.account.memory record) + potential (remaining rest) state ≤
      potential (remaining (.win record ticket :: rest)) state := by
  have pointwise (other : Record) : cell (remaining (.win record ticket :: rest)) state other =
      cell (remaining rest) state other +
      if state.ticket other = ticket then GreedyForest.entryDeficit (state.account.label other) (state.account.memory other) else 0 := by
    by_cases same : state.ticket other = ticket <;> simp [cell, remaining, same, add_mul, add_comm]
  unfold potential
  simp_rw [pointwise]
  rw [Finset.sum_add_distrib]
  have charge : GreedyForest.entryDeficit (state.account.label record) (state.account.memory record) ≤
      ∑ other, if state.ticket other = ticket then GreedyForest.entryDeficit (state.account.label other) (state.account.memory other) else 0 := by
    have result := Finset.single_le_sum
      (f := fun other => if state.ticket other = ticket then GreedyForest.entryDeficit (state.account.label other) (state.account.memory other) else 0)
      (s := (Finset.univ : Finset Record)) (by intro other _; split_ifs <;> simp [GreedyForest.entryDeficit_nonneg])
      (Finset.mem_univ record)
    simpa only [matching, if_true] using result
  linarith

theorem remaining_tail (action : Action Record Ticket) (rest : List (Action Record Ticket)) (ticket : Ticket) :
    remaining rest ticket ≤ remaining (action :: rest) ticket := by
  cases action <;> simp [remaining]

theorem observed_bound (state : State Record Ticket) (actions : List (Action Record Ticket))
    (legal : Legal state actions) (capacity : ∀ ticket, remaining actions ticket ≤ 4) :
    observed state actions ≤ 4*EntryJournal.total deficit state.account (erase actions) +
      4*EntryJournal.total negativeChange state.account (erase actions) + potential (remaining actions) state := by
  induction actions generalizing state with
  | nil => simp [observed, erase, remaining, potential, cell, EntryJournal.total]
  | cons action rest ih =>
      have tailCapacity : ∀ ticket, remaining rest ticket ≤ 4 :=
        fun ticket => (remaining_tail action rest ticket).trans (capacity ticket)
      have tail := ih (step state action) legal.2 tailCapacity
      unfold erase at tail
      cases action with
      | change record label =>
          have localBound := change_bound (remaining rest) tailCapacity state record label
          simp only [observed, erase, List.flatMap_cons, eraseOne, List.singleton_append,
            EntryJournal.total, deficit, negativeChange, remaining, zero_add, mul_zero] at ⊢
          change observed (step state (.change record label)) rest ≤ _
          change observed (step state (.change record label)) rest ≤ _ at tail
          dsimp only [step] at tail localBound ⊢
          linarith
      | entry record creator kind ticket =>
          have localBound := entry_bound (remaining rest) tailCapacity state record creator kind ticket
          simp only [observed, erase, List.flatMap_cons, eraseOne, List.singleton_append,
            EntryJournal.total, deficit, negativeChange, remaining, zero_add, mul_zero] at ⊢
          dsimp only [step] at tail localBound ⊢
          linarith
      | win record ticket =>
          have localBound := win_bound rest state record ticket legal.1
          simp only [observed, erase, List.flatMap_cons, eraseOne, List.nil_append, step] at tail ⊢
          linarith

end Greedy.WinnerCredit
