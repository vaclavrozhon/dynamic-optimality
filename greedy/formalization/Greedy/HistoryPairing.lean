import Greedy.SparseCreatorSum

/-! Linear pairing of signed creator coefficients with actual label changes. -/

namespace Greedy.LabelHistory

open scoped BigOperators

variable {Record : Type*} [Fintype Record]

def pairing (history : History Record) (coefficient : Record → ℕ → ℤ) : ℤ :=
  (history.changes.map (fun change => ∑ record, coefficient record change.time * change.delta record)).sum

theorem pairing_zero (history : History Record) : pairing history (fun _ _ => 0) = 0 := by
  simp [pairing]

theorem pairing_add (history : History Record) (first second : Record → ℕ → ℤ) :
    pairing history (fun record time => first record time + second record time) =
      pairing history first + pairing history second := by
  simp only [pairing, add_mul, Finset.sum_add_distrib]
  induction history.changes with
  | nil => simp
  | cons change rest ih => simp only [List.map_cons, List.sum_cons]; omega

theorem pairing_sum {Index : Type*} (history : History Record) (indices : Finset Index)
    (coefficient : Index → Record → ℕ → ℤ) :
    pairing history (fun record time => ∑ index ∈ indices, coefficient index record time) =
      ∑ index ∈ indices, pairing history (coefficient index) := by
  classical
  induction indices using Finset.induction_on with
  | empty => simp [pairing_zero]
  | @insert index indices absent ih =>
      simp only [Finset.sum_insert absent, pairing_add, ih]

theorem pairing_bound (history : History Record) (coefficient : Record → ℕ → ℤ) (capacity : ℤ)
    (bound : ∀ record time, |coefficient record time| ≤ capacity) : pairing history coefficient ≤ capacity * variation history := by
  have one (change : Change Record) :
      (∑ record, coefficient record change.time * change.delta record) ≤ capacity * ∑ record, |change.delta record| := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro record _
    calc
      _ ≤ |coefficient record change.time * change.delta record| := le_abs_self _
      _ = |coefficient record change.time| * |change.delta record| := abs_mul _ _
      _ ≤ capacity * |change.delta record| := mul_le_mul_of_nonneg_right (bound record change.time) (abs_nonneg _)
  unfold pairing variation
  induction history.changes with
  | nil => simp
  | cons change rest ih =>
      simp only [List.map_cons, List.sum_cons, mul_add]
      exact add_le_add (one change) ih

end Greedy.LabelHistory
