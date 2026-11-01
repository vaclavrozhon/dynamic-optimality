import Greedy.JournalBatches

/-! Exact signed variation and its initial reserve in the entry journal. -/

namespace Greedy.EntryJournal

open scoped BigOperators
open WeightedMemory (State)

variable {Record : Type*} [Fintype Record] [DecidableEq Record]

def negativeChange (state : State Record) : Action Record → ℤ
  | .change record value => max 0 (state.label record - value)
  | .entry _ _ _ => 0

def labelMass (state : State Record) : ℤ := ∑ record, state.label record

theorem variation_step (state : State Record) (action : Action Record) :
    labelMass (step state action) = labelMass state + positiveChange state action - negativeChange state action := by
  cases action with
  | entry record creator kind => simp [labelMass, step, encode, WeightedMemory.step, positiveChange, WeightedMemory.positiveChange, negativeChange]
  | change record value =>
      have pointwise : ∀ key, Function.update state.label record value key =
          state.label key + if key = record then value - state.label record else 0 := by
        intro key
        by_cases same : key = record <;> simp [same]
      simp only [labelMass, step, encode, WeightedMemory.step]
      simp_rw [pointwise]
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, positiveChange, encode,
        WeightedMemory.positiveChange, negativeChange]
      omega

theorem variation_balance (state : State Record) (actions : List (Action Record)) :
    labelMass (run state actions) = labelMass state +
      total positiveChange state actions - total negativeChange state actions := by
  induction actions generalizing state with
  | nil => simp [run, total]
  | cons action rest ih =>
      simp only [run, total, ih, variation_step]
      ring

theorem run_bounded (K : ℤ) (state : State Record) (actions : List (Action Record))
    (bounded : Bounded K state) (valid : Valid K state actions) : Bounded K (run state actions) := by
  induction actions generalizing state with
  | nil => exact bounded
  | cons action rest ih => exact ih _ (step_bounded K state action bounded valid.1) valid.2

theorem labelMass_bounds (K : ℤ) (state : State Record) (bounded : Bounded K state) :
    Fintype.card Record ≤ labelMass state ∧ labelMass state ≤ K * Fintype.card Record := by
  have lower := Finset.sum_le_sum (s := (Finset.univ : Finset Record)) (fun record _ => (bounded record).1)
  have upper := Finset.sum_le_sum (s := (Finset.univ : Finset Record)) (fun record _ => (bounded record).2)
  exact ⟨by simpa [labelMass] using lower, by simpa [labelMass, mul_comm] using upper⟩

/-- All downward variation is paid by upward variation and the finite
initial label reserve. Entries preserve labels and need no extra reserve. -/
theorem negative_bound (K : ℤ) (state : State Record) (actions : List (Action Record))
    (bounded : Bounded K state) (valid : Valid K state actions) :
    total negativeChange state actions ≤ (K - 1) * Fintype.card Record + total positiveChange state actions := by
  have identity := variation_balance state actions
  have before := labelMass_bounds K state bounded
  have after := labelMass_bounds K (run state actions) (run_bounded K state actions bounded valid)
  linarith

theorem total_nonneg (weight : State Record → Action Record → ℤ)
    (nonneg : ∀ state action, 0 ≤ weight state action) (state : State Record) (actions : List (Action Record)) :
    0 ≤ total weight state actions := by
  induction actions generalizing state with
  | nil => rfl
  | cons action rest ih => exact add_nonneg (nonneg state action) (ih _)

end Greedy.EntryJournal
