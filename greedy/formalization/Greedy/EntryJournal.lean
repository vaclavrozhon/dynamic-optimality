import Greedy.WeightedMemory
import ForestLedger

/-!
# Entry deficits and loser shifts in one chronological journal

An entry reads both endpoint labels from its current state and stores
the creator's current label. Internal entries require only weak label
order, so good equal-label links are included. Ordinary entries include
initialization and administrative reparenting; boundary entries are
access links between distinct source instances.

The two conclusions below derive the deficit and loser-shift rows of the
linear ledger from local journal actions. They do not assume either
aggregate inequality.
-/

namespace Greedy.EntryJournal

open GreedyForest
open Greedy.WeightedMemory (State potential)

inductive Kind where
  | ordinary | internal | boundary
  deriving DecidableEq

inductive Action (Record : Type*) where
  | change (record : Record) (label : ℤ)
  | entry (record creator : Record) (kind : Kind)

variable {Record : Type*} [Fintype Record] [DecidableEq Record]

def encode (state : State Record) : Action Record → WeightedMemory.Event Record
  | .change record label => .change record label
  | .entry record creator kind => .entry record (state.label creator) (kind == .internal)

def step (state : State Record) (action : Action Record) : State Record :=
  WeightedMemory.step state (encode state action)

def Bounded (K : ℤ) (state : State Record) : Prop :=
  ∀ record, 1 ≤ state.label record ∧ state.label record ≤ K

def legal (K : ℤ) (state : State Record) : Action Record → Prop
  | .change _ label => 1 ≤ label ∧ label ≤ K
  | .entry record creator kind => kind = .internal → state.label creator ≤ state.label record

def Valid (K : ℤ) (state : State Record) : List (Action Record) → Prop
  | [] => True
  | action :: rest => legal K state action ∧ Valid K (step state action) rest

def total (weight : State Record → Action Record → ℤ) (state : State Record) : List (Action Record) → ℤ
  | [] => 0
  | action :: rest => weight state action + total weight (step state action) rest

def run (state : State Record) : List (Action Record) → State Record
  | [] => state
  | action :: rest => run (step state action) rest

def ordinary (_state : State Record) : Action Record → ℤ
  | .entry _ _ .ordinary => 1
  | _ => 0

def boundary (_state : State Record) : Action Record → ℤ
  | .entry _ _ .boundary => 1
  | _ => 0

def good (state : State Record) : Action Record → ℤ
  | .entry record creator .internal => if state.label record = state.label creator then 1 else 0
  | _ => 0

def deficit (state : State Record) : Action Record → ℤ
  | .entry record creator _ => entryDeficit (state.label record) (state.label creator)
  | _ => 0

def negativeEntry (state : State Record) : Action Record → ℤ
  | .entry record creator .boundary => max 0 (state.label creator - state.label record)
  | _ => 0

def positiveEntry (state : State Record) : Action Record → ℤ
  | .entry record creator .boundary => max 0 (state.label record - state.label creator)
  | _ => 0

def shift (state : State Record) (action : Action Record) : ℤ :=
  WeightedMemory.shift state (encode state action)

def positiveChange (state : State Record) (action : Action Record) : ℤ :=
  WeightedMemory.positiveChange state (encode state action)

theorem step_bounded (K : ℤ) (state : State Record) (action : Action Record)
    (bounded : Bounded K state) (valid : legal K state action) : Bounded K (step state action) := by
  cases action with
  | change record label =>
      intro key
      by_cases same : key = record
      · subst key; simpa [step, encode, WeightedMemory.step, legal] using valid
      · simpa [step, encode, WeightedMemory.step, same] using bounded key
  | entry record creator kind => exact bounded

omit [Fintype Record] [DecidableEq Record] in
theorem deficit_step (K : ℤ) (hK : 1 ≤ K) (state : State Record) (action : Action Record)
    (bounded : Bounded K state) (valid : legal K state action) :
    deficit state action ≤ K * ordinary state action + good state action +
      boundary state action + negativeEntry state action := by
  cases action with
  | change record label => simp [deficit, ordinary, good, boundary, negativeEntry]
  | entry record creator kind =>
      have rb := bounded record
      have cb := bounded creator
      cases kind with
      | ordinary =>
          simpa [deficit, ordinary, good, boundary, negativeEntry] using
            entryDeficit_le_bound K _ _ hK rb.1 cb.2
      | internal =>
          have order : state.label creator ≤ state.label record := valid rfl
          simp only [deficit, ordinary, good, boundary, negativeEntry, mul_zero, zero_add,
            add_zero, entryDeficit]
          split_ifs <;> omega
      | boundary =>
          simp only [deficit, ordinary, good, boundary, negativeEntry, mul_zero, zero_add, entryDeficit]
          omega

theorem memory_step (K : ℤ) (state : State Record) (action : Action Record)
    (bounded : Bounded K state) (valid : legal K state action) :
    shift state action + potential (step state action) ≤
      potential state + positiveChange state action +
        (K - 1) * ordinary state action + positiveEntry state action := by
  have memoryValid : WeightedMemory.valid state (encode state action) := by
    cases action with
    | change => trivial
    | entry record creator kind => simpa only [encode, WeightedMemory.valid, beq_iff_eq, legal] using valid
  have result := WeightedMemory.step_bound state (encode state action) memoryValid
  have chargeBound : WeightedMemory.entryCharge state (encode state action) ≤
      (K - 1) * ordinary state action + positiveEntry state action := by
    cases action with
    | change => simp [encode, WeightedMemory.entryCharge, ordinary, positiveEntry]
    | entry record creator kind =>
        have rb := bounded record
        have cb := bounded creator
        cases kind <;> simp [encode, WeightedMemory.entryCharge, ordinary, positiveEntry] <;> omega
  change shift state action + potential (step state action) ≤
    potential state + positiveChange state action + _ at result
  linarith

theorem deficits_bound (K : ℤ) (hK : 1 ≤ K) (state : State Record) (actions : List (Action Record))
    (bounded : Bounded K state) (valid : Valid K state actions) :
    total deficit state actions ≤ K * total ordinary state actions + total good state actions +
      total boundary state actions + total negativeEntry state actions := by
  induction actions generalizing state with
  | nil => simp [total]
  | cons action rest ih =>
      have head := deficit_step K hK state action bounded valid.1
      have tail := ih _ (step_bounded K state action bounded valid.1) valid.2
      simp only [total]
      linarith

theorem memory_bound (K : ℤ) (state : State Record) (actions : List (Action Record))
    (bounded : Bounded K state) (valid : Valid K state actions) :
    total shift state actions + potential (run state actions) ≤
      potential state + total positiveChange state actions +
        (K - 1) * total ordinary state actions + total positiveEntry state actions := by
  induction actions generalizing state with
  | nil => simp [total, run]
  | cons action rest ih =>
      have head := memory_step K state action bounded valid.1
      have tail := ih _ (step_bounded K state action bounded valid.1) valid.2
      simp only [total, run]
      linarith

theorem loser_bound (K : ℤ) (label : Record → ℤ) (actions : List (Action Record))
    (bounded : ∀ record, 1 ≤ label record ∧ label record ≤ K)
    (valid : Valid K ⟨label, label⟩ actions) :
    total shift ⟨label, label⟩ actions ≤ total positiveChange ⟨label, label⟩ actions +
      (K - 1) * total ordinary ⟨label, label⟩ actions + total positiveEntry ⟨label, label⟩ actions := by
  have bound := memory_bound K ⟨label, label⟩ actions bounded valid
  have initial : potential (⟨label, label⟩ : State Record) = 0 := by simp [potential]
  have nonneg := WeightedMemory.potential_nonneg (run ⟨label, label⟩ actions)
  rw [initial] at bound
  linarith

end Greedy.EntryJournal
