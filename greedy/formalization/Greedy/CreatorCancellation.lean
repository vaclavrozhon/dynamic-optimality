import ForestLedger
import Greedy.SignedCuts

/-!
# From signed family cuts to creator variation

Each edge has two historical join times in the same block family.
The coefficient of a label change at time `t` is the difference of the
indicators that these joins occur after `t`. A family's signed coefficient
vanishes outside its growth window. Combining the per-family cancellation
bound with the number of simultaneous growth windows bounds the creator
shift by total variation, with no factor depending on the label range.
-/

namespace Greedy.CreatorCancellation

open GreedyForest
open scoped BigOperators

theorem multiplicity {Family Edge : Type*} [Fintype Family] [Fintype Edge]
    [DecidableEq Family] (family : Edge → Family) (start finish : Family → ℕ)
    (winnerJoin loserJoin : Edge → ℕ) (time : ℕ) (overlap capacity : ℤ)
    (capacityNonneg : 0 ≤ capacity)
    (joins : ∀ e,
      (start (family e) ≤ winnerJoin e ∧ winnerJoin e ≤ finish (family e)) ∧
      (start (family e) ≤ loserJoin e ∧ loserJoin e ≤ finish (family e)))
    (localBound : ∀ b, |∑ e, if family e = b then
      joinCoefficient (winnerJoin e) (loserJoin e) time else 0| ≤ capacity)
    (growthBound : ∑ b, (if start b ≤ time ∧ time < finish b then (1 : ℤ) else 0) ≤ overlap) :
    |∑ e, joinCoefficient (winnerJoin e) (loserJoin e) time| ≤ overlap * capacity := by
  classical
  let mass : Family → ℤ := fun b => ∑ e, if family e = b then
    joinCoefficient (winnerJoin e) (loserJoin e) time else 0
  have partition : ∑ b, mass b = ∑ e, joinCoefficient (winnerJoin e) (loserJoin e) time := by
    dsimp [mass]
    rw [Finset.sum_comm]
    simp
  have bound : ∀ b, |mass b| ≤
      (if start b ≤ time ∧ time < finish b then (1 : ℤ) else 0) * capacity := by
    intro b
    by_cases growing : start b ≤ time ∧ time < finish b
    · simpa only [if_pos growing, one_mul] using localBound b
    · have zero : mass b = 0 := by
        apply Finset.sum_eq_zero
        intro e _
        by_cases same : family e = b
        · have coefficientZero := joinCoefficient_zero_outside_growth
            (start b) (finish b) (winnerJoin e) (loserJoin e) time
            (by simpa [same] using (joins e).1) (by simpa [same] using (joins e).2) growing
          simp [same, coefficientZero]
        · simp [same]
      simp [growing, zero]
  rw [← partition]
  calc
    |∑ b, mass b| ≤ ∑ b, |mass b| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ b, (if start b ≤ time ∧ time < finish b then (1 : ℤ) else 0) * capacity :=
      Finset.sum_le_sum fun b _ => bound b
    _ = (∑ b, if start b ≤ time ∧ time < finish b then (1 : ℤ) else 0) * capacity := by
      rw [Finset.sum_mul]
    _ ≤ overlap * capacity := mul_le_mul_of_nonneg_right growthBound capacityNonneg

theorem shift_bound {Family Edge : Type*} [Fintype Family] [Fintype Edge]
    [DecidableEq Family] (family : Edge → Family) (start finish : Family → ℕ)
    (winnerJoin loserJoin : Edge → ℕ) (label : ℕ → ℤ) (time : ℕ) (overlap capacity : ℤ)
    (capacityNonneg : 0 ≤ capacity) (finishBound : ∀ b, finish b ≤ time)
    (joins : ∀ e,
      (start (family e) ≤ winnerJoin e ∧ winnerJoin e ≤ finish (family e)) ∧
      (start (family e) ≤ loserJoin e ∧ loserJoin e ≤ finish (family e)))
    (localBound : ∀ b t, |∑ e, if family e = b then
      joinCoefficient (winnerJoin e) (loserJoin e) t else 0| ≤ capacity)
    (growthBound : ∀ t, ∑ b,
      (if start b ≤ t ∧ t < finish b then (1 : ℤ) else 0) ≤ overlap) :
    ∑ e, (label (loserJoin e) - label (winnerJoin e)) ≤
      overlap * capacity * ∑ t ∈ Finset.range time, |label (t+1) - label t| := by
  classical
  have expand : (∑ e, (label (loserJoin e) - label (winnerJoin e))) =
      ∑ e, ∑ t ∈ Finset.range time,
        joinCoefficient (winnerJoin e) (loserJoin e) t * (label (t+1) - label t) := by
    apply Finset.sum_congr rfl
    intro e _
    exact (joinCoefficient_telescope label time (winnerJoin e) (loserJoin e)
      ((joins e).1.2.trans (finishBound _)) ((joins e).2.2.trans (finishBound _))).symm
  rw [expand, Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro t _
  have coefficientBound := multiplicity family start finish winnerJoin loserJoin t overlap capacity
    capacityNonneg joins (fun b => localBound b t) (growthBound t)
  rw [← Finset.sum_mul]
  calc
    _ ≤ |(∑ e, joinCoefficient (winnerJoin e) (loserJoin e) t) * (label (t+1) - label t)| :=
      le_abs_self _
    _ = |∑ e, joinCoefficient (winnerJoin e) (loserJoin e) t| * |label (t+1) - label t| := abs_mul _ _
    _ ≤ (overlap * capacity) * |label (t+1) - label t| :=
      mul_le_mul_of_nonneg_right coefficientBound (abs_nonneg _)

end Greedy.CreatorCancellation
