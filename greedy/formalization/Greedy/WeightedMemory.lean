import Mathlib

/-!
# Weighted creator-memory accounting

`label v` is the current label of record `v`; `memory v` is the creator's
label saved at its most recent entry. The potential is the sum of positive
differences `label v - memory v`. Internal entries can pay their signed
memory change by releasing this potential. Other entries inject precisely
their positive entry difference; label changes inject at most their positive
variation. Events may interleave different records arbitrarily.
-/

namespace Greedy.WeightedMemory

open scoped BigOperators

variable {Record : Type*} [Fintype Record] [DecidableEq Record]

structure State (Record : Type*) where
  label : Record → ℤ
  memory : Record → ℤ

inductive Event (Record : Type*) where
  | change (record : Record) (label : ℤ)
  | entry (record : Record) (creator : ℤ) (internal : Bool)

def potential (state : State Record) : ℤ :=
  ∑ v, max 0 (state.label v - state.memory v)

def step (state : State Record) : Event Record → State Record
  | .change v label => { state with label := Function.update state.label v label }
  | .entry v creator _ => { state with memory := Function.update state.memory v creator }

def valid (state : State Record) : Event Record → Prop
  | .change _ _ => True
  | .entry v creator internal => internal = true → creator ≤ state.label v

def shift (state : State Record) : Event Record → ℤ
  | .change _ _ => 0
  | .entry v creator internal => if internal then creator - state.memory v else 0

def positiveChange (state : State Record) : Event Record → ℤ
  | .change v label => max 0 (label - state.label v)
  | .entry _ _ _ => 0

def entryCharge (state : State Record) : Event Record → ℤ
  | .change _ _ => 0
  | .entry v creator internal => if internal then 0 else max 0 (state.label v - creator)

omit [DecidableEq Record] in
theorem potential_nonneg (state : State Record) : 0 ≤ potential state :=
  Finset.sum_nonneg fun _ _ => le_max_left _ _

theorem potential_change (state : State Record) (v : Record) (label : ℤ) :
    potential (step state (.change v label)) = potential state -
      max 0 (state.label v - state.memory v) + max 0 (label - state.memory v) := by
  have pointwise : ∀ w,
      max 0 (Function.update state.label v label w - state.memory w) =
        max 0 (state.label w - state.memory w) +
          if w = v then max 0 (label - state.memory v) -
            max 0 (state.label v - state.memory v) else 0 := by
    intro w
    by_cases same : w = v
    · subst w; simp
    · simp [same]
  unfold potential step
  simp_rw [pointwise]
  rw [Finset.sum_add_distrib]
  simp
  ring

theorem potential_entry (state : State Record) (v : Record) (creator : ℤ) (internal : Bool) :
    potential (step state (.entry v creator internal)) = potential state -
      max 0 (state.label v - state.memory v) + max 0 (state.label v - creator) := by
  have pointwise : ∀ w,
      max 0 (state.label w - Function.update state.memory v creator w) =
        max 0 (state.label w - state.memory w) +
          if w = v then max 0 (state.label v - creator) -
            max 0 (state.label v - state.memory v) else 0 := by
    intro w
    by_cases same : w = v
    · subst w; simp
    · simp [same]
  unfold potential step
  simp_rw [pointwise]
  rw [Finset.sum_add_distrib]
  simp
  ring

theorem step_bound (state : State Record) (event : Event Record) (legal : valid state event) :
    shift state event + potential (step state event) ≤
      potential state + positiveChange state event + entryCharge state event := by
  cases event with
  | change v label =>
      rw [potential_change]
      simp only [shift, positiveChange, entryCharge]
      omega
  | entry v creator internal =>
      rw [potential_entry]
      cases internal <;> simp_all only [valid, shift, positiveChange, entryCharge,
        Bool.false_eq_true, ↓reduceIte, forall_const] <;> omega

def run (state : State Record) : List (Event Record) → State Record
  | [] => state
  | event :: rest => run (step state event) rest

def Valid (state : State Record) : List (Event Record) → Prop
  | [] => True
  | event :: rest => valid state event ∧ Valid (step state event) rest

def total (weight : State Record → Event Record → ℤ) (state : State Record) :
    List (Event Record) → ℤ
  | [] => 0
  | event :: rest => weight state event + total weight (step state event) rest

theorem run_bound (state : State Record) (events : List (Event Record)) (legal : Valid state events) :
    total shift state events + potential (run state events) ≤
      potential state + total positiveChange state events + total entryCharge state events := by
  induction events generalizing state with
  | nil => simp [total, run]
  | cons event rest ih =>
      have headBound := step_bound state event legal.1
      have tailBound := ih (step state event) legal.2
      simp only [total, run]
      linarith

/-- Initial memory equals the initial record label, so no uncharged
initial reserve appears in the bound. Actual initial memberships are
ordinary entries and pay their positive entry differences. -/
theorem weighted_loser_bound (label : Record → ℤ) (events : List (Event Record))
    (legal : Valid ⟨label, label⟩ events) :
    total shift ⟨label, label⟩ events ≤
      total positiveChange ⟨label, label⟩ events + total entryCharge ⟨label, label⟩ events := by
  have bound := run_bound ⟨label, label⟩ events legal
  have nonneg := potential_nonneg (run ⟨label, label⟩ events)
  have initial : potential (⟨label, label⟩ : State Record) = 0 := by simp [potential]
  rw [initial] at bound
  linarith

end Greedy.WeightedMemory
