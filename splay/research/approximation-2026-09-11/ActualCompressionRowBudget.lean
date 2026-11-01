import ActualRelabelRows
import HistoricalRankCompression

/-! The logarithmic scalar estimates are instantiated on the actual timed
historical rows. Clamping only makes the label function globally bounded for
the numerical compiler; all ranks on the original history lie below the clamp. -/

namespace Splay.Research.ActualCompressionRowBudget

open Splay.Interface ActualRelabelRows
open scoped BigOperators

noncomputable section

def label (G rank : ℕ) : ℕ := HistoricalRankCompression.natLabel (min rank G)

def cap (G : ℕ) : ℕ := HistoricalRankCompression.natLabel G

theorem label_positive (G rank : ℕ) : 1 ≤ label G rank :=
  HistoricalRankCompression.natLabel_positive _

theorem label_bounded (G rank : ℕ) : label G rank ≤ cap G :=
  HistoricalRankCompression.natLabel_monotone (Nat.min_le_right _ _)

theorem label_cast_of_le {G rank : ℕ} (bounded : rank ≤ G) :
    (label G rank : ℝ) = HistoricalRankCompression.label (rank : ℝ) := by
  unfold label
  rw [Nat.min_eq_left bounded]
  exact HistoricalRankCompression.natLabel_real_cast rank

def charge {n : ℕ} (timed : TimedAnnotatedPairShiftSnapshot n) : ℕ :=
  (ActualTimedErrorBudget.error timed).toNat

def earlyError {n : ℕ} (cutoff : ℕ)
    (snapshots : List (TimedAnnotatedPairShiftSnapshot n)) : ℕ :=
  ((significantTimedSnapshots cutoff snapshots).map charge).sum

def lateCount {n : ℕ} (cutoff : ℕ)
    (snapshots : List (TimedAnnotatedPairShiftSnapshot n)) : ℕ :=
  (snapshots.filter fun timed => decide (cutoff ≤ timed.annotated.sourcePassCount)).length

private theorem nat_sub_cast (a b : ℕ) :
    ((a-b : ℕ) : ℝ) = max 0 ((a : ℝ) - b) := by
  by_cases order : b ≤ a
  · rw [Nat.cast_sub order, max_eq_right]
    exact sub_nonneg.mpr (by exact_mod_cast order)
  · have reversed : a ≤ b := by omega
    rw [Nat.sub_eq_zero_of_le reversed, Nat.cast_zero, max_eq_left]
    exact sub_nonpos.mpr (by exact_mod_cast reversed)

/-- The early scalar inequalities have no free per-row rounding charge. -/
theorem row_bounds {n : ℕ} {params : Parameters}
    {timed : TimedAnnotatedPairShiftSnapshot n} (valid : RowValid params timed) :
    rowPositive (label params.valueBound) timed ≤ 17 * charge timed ∧
    rowPreparation (label params.valueBound) timed ≤
      18 * rowNegative (label params.valueBound) timed + 20 * charge timed := by
  obtain ⟨winnerPositive, winnerBound, oldPositive, oldBound,
    newPositive, newBound, identity⟩ := valid
  have realIdentity : (newRank timed : ℝ) = (oldRank timed : ℝ) -
      (winnerRank timed : ℝ) + (ActualTimedErrorBudget.error timed : ℝ) := by
    exact_mod_cast identity
  have chargedInt : ActualTimedErrorBudget.error timed ≤ (charge timed : ℤ) := by
    unfold charge
    omega
  have charged : (ActualTimedErrorBudget.error timed : ℝ) ≤ (charge timed : ℝ) := by
    exact_mod_cast chargedInt
  have rises := HistoricalRankCompression.positive_relabel_bound
    (by exact_mod_cast winnerPositive : (1 : ℝ) ≤ winnerRank timed)
    (Nat.cast_nonneg (oldRank timed)) (Nat.cast_nonneg (newRank timed))
    realIdentity (Nat.cast_nonneg (charge timed)) charged
  have prepares := HistoricalRankCompression.preparation_bound
    (by exact_mod_cast winnerPositive : (1 : ℝ) ≤ winnerRank timed)
    (Nat.cast_nonneg (oldRank timed)) (Nat.cast_nonneg (newRank timed))
    realIdentity (Nat.cast_nonneg (charge timed)) charged
  have positiveCast : (rowPositive (label params.valueBound) timed : ℝ) =
      HistoricalRankCompression.rise (oldRank timed) (newRank timed) := by
    unfold rowPositive HistoricalRankCompression.rise
    rw [nat_sub_cast, label_cast_of_le newBound, label_cast_of_le oldBound]
  have negativeCast : (rowNegative (label params.valueBound) timed : ℝ) =
      HistoricalRankCompression.fall (oldRank timed) (newRank timed) := by
    unfold rowNegative HistoricalRankCompression.fall HistoricalRankCompression.rise
    rw [nat_sub_cast, label_cast_of_le oldBound, label_cast_of_le newBound]
  have preparationCast : (rowPreparation (label params.valueBound) timed : ℝ) =
      HistoricalRankCompression.preparation (winnerRank timed) (oldRank timed) := by
    unfold rowPreparation HistoricalRankCompression.preparation
    rw [nat_sub_cast, Nat.cast_add, Nat.cast_one,
      label_cast_of_le winnerBound, label_cast_of_le oldBound]
  rw [← positiveCast] at rises
  rw [← preparationCast, ← negativeCast] at prepares
  exact ⟨by exact_mod_cast rises, by exact_mod_cast prepares⟩

theorem late_row_bounds {n : ℕ} (G : ℕ)
    (timed : TimedAnnotatedPairShiftSnapshot n) :
    rowPositive (label G) timed ≤ cap G ∧
    rowPreparation (label G) timed ≤ cap G + 1 := by
  have newBound := label_bounded G (newRank timed)
  have winnerBound := label_bounded G (winnerRank timed)
  unfold rowPositive rowPreparation
  omega

theorem rows_bounds {n : ℕ} {params : Parameters}
    (cutoff : ℕ) (snapshots : List (TimedAnnotatedPairShiftSnapshot n))
    (valid : ∀ timed ∈ snapshots, RowValid params timed) :
    (snapshots.map (rowPositive (label params.valueBound))).sum ≤
      17 * earlyError cutoff snapshots + cap params.valueBound * lateCount cutoff snapshots ∧
    (snapshots.map (rowPreparation (label params.valueBound))).sum ≤
      18 * (snapshots.map (rowNegative (label params.valueBound))).sum +
        20 * earlyError cutoff snapshots + (cap params.valueBound + 1) * lateCount cutoff snapshots := by
  induction snapshots with
  | nil => simp [earlyError, lateCount, significantTimedSnapshots]
  | cons timed snapshots ih =>
      have head := row_bounds (valid timed (by simp))
      have lateHead := late_row_bounds params.valueBound timed
      have tail := ih (by intro later member; exact valid later (by simp [member]))
      by_cases early : timed.annotated.sourcePassCount < cutoff
      · have notLate : ¬ cutoff ≤ timed.annotated.sourcePassCount := by omega
        simp [earlyError, significantTimedSnapshots,
          AnnotatedPairShiftSnapshot.significantDecision, early,
          lateCount, notLate, Nat.mul_add] at tail ⊢
        constructor <;> omega
      · have late : cutoff ≤ timed.annotated.sourcePassCount := by omega
        simp [earlyError, significantTimedSnapshots,
          AnnotatedPairShiftSnapshot.significantDecision, early,
          lateCount, late, Nat.mul_add] at tail ⊢
        constructor <;> omega

theorem earlyError_le {n : ℕ} {params : Parameters}
    {initial final : State n} {finalLabels : RootLabels}
    {finalLedger : EpisodeLedger n} {finalClock : EpisodeClock n}
    {finalEvents : List (ValueChangeEvent n)} {operations : List (Operation n)}
    {snapshots : List (TimedAnnotatedPairShiftSnapshot n)}
    (history : LifetimeHistory.TimedPairShiftHistory params initial []
      (EpisodeLedger.empty : EpisodeLedger n) (fun _ => 0) []
      operations snapshots final finalLabels finalLedger finalClock finalEvents)
    (initialState : initial.Initial params) (cutoff : ℕ) :
    earlyError cutoff snapshots ≤
      ((1 + params.growingLimit) * cutoff + 1) * totalValueChanges operations := by
  have bound := ActualTimedErrorBudget.early_error_le history initialState cutoff
  have castSum : ∀ rows : List (TimedAnnotatedPairShiftSnapshot n),
      ((rows.map charge).sum : ℤ) = (rows.map fun timed =>
        max (ActualTimedErrorBudget.error timed) 0).sum := by
    intro rows
    induction rows with
    | nil => simp
    | cons timed rows ih =>
        simp only [List.map_cons, List.sum_cons, Nat.cast_add, ih]
        have head : (charge timed : ℤ) = max (ActualTimedErrorBudget.error timed) 0 := by
          unfold charge
          omega
        rw [head]
  rw [← castSum] at bound
  exact_mod_cast bound

/-- All three budgets are obtained from the literal original history. -/
theorem history_bounds {n : ℕ} {params : Parameters}
    {initial final : State n} {finalLabels : RootLabels}
    {finalLedger : EpisodeLedger n} {finalClock : EpisodeClock n}
    {finalEvents : List (ValueChangeEvent n)} {operations : List (Operation n)}
    {snapshots : List (TimedAnnotatedPairShiftSnapshot n)}
    (history : LifetimeHistory.TimedPairShiftHistory params initial []
      (EpisodeLedger.empty : EpisodeLedger n) (fun _ => 0) []
      operations snapshots final finalLabels finalLedger finalClock finalEvents)
    (initialState : initial.Initial params) (cutoff : ℕ) :
    let P := (snapshots.map (rowPositive (label params.valueBound))).sum
    let N := (snapshots.map (rowNegative (label params.valueBound))).sum
    let J := (snapshots.map (rowPreparation (label params.valueBound))).sum
    let W := ((1 + params.growingLimit) * cutoff + 1) * totalValueChanges operations
    let R := cap params.valueBound
    let T := lateCount cutoff snapshots
    P ≤ 17 * W + R * T ∧ N ≤ R * totalInserts operations + P ∧
      J ≤ 18 * N + 20 * W + (R + 1) * T := by
  have valid := history_valid history (EpisodeLedger.frozenValuesBound_empty params)
  have rows := rows_bounds cutoff snapshots valid
  have errors := earlyError_le history initialState cutoff
  have negatives := (history_rows (label params.valueBound) history).negative_le_insert_add_positive
    (label_positive params.valueBound) (label_bounded params.valueBound)
  dsimp
  constructor
  · omega
  constructor
  · exact negatives
  · omega

/-- Closed numerical budget ready for the actual trace compiler's
`Vnew ≤ 2 (RI + P + J)` endpoint. -/
theorem compiler_charge_bound {n : ℕ} {params : Parameters}
    {initial final : State n} {finalLabels : RootLabels}
    {finalLedger : EpisodeLedger n} {finalClock : EpisodeClock n}
    {finalEvents : List (ValueChangeEvent n)} {operations : List (Operation n)}
    {snapshots : List (TimedAnnotatedPairShiftSnapshot n)}
    (history : LifetimeHistory.TimedPairShiftHistory params initial []
      (EpisodeLedger.empty : EpisodeLedger n) (fun _ => 0) []
      operations snapshots final finalLabels finalLedger finalClock finalEvents)
    (initialState : initial.Initial params) (cutoff : ℕ) :
    2 * (cap params.valueBound * totalInserts operations +
      (snapshots.map (rowPositive (label params.valueBound))).sum +
      (snapshots.map (rowPreparation (label params.valueBound))).sum) ≤
    38 * cap params.valueBound * totalInserts operations +
      686 * (((1 + params.growingLimit) * cutoff + 1) * totalValueChanges operations) +
      (40 * cap params.valueBound + 2) * lateCount cutoff snapshots := by
  have bounds := history_bounds history initialState cutoff
  dsimp at bounds
  nlinarith

#print axioms row_bounds
#print axioms compiler_charge_bound

end
end Splay.Research.ActualCompressionRowBudget
