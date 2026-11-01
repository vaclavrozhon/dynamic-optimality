import TightDyadicCompressionInventory
import TightDyadicCompressionRanks
import DyadicCompressionRowBudget

namespace Splay.Research.SharperDyadicCompressionRowBudget
open Splay.Interface ActualRelabelRows

def label (G rank : ℕ) : ℕ := DyadicRankCompression.label (min rank (G-1))
def cap (G : ℕ) : ℕ := max 2 (DyadicRankCompression.label (G-1))

theorem cap_ge_two (G : ℕ) : 2 ≤ cap G := le_max_left _ _
theorem cap_positive (G : ℕ) : 1 ≤ cap G := (by omega : 1 ≤ 2).trans (cap_ge_two G)
theorem label_positive (G rank : ℕ) : 1 ≤ label G rank := DyadicRankCompression.label_positive _
theorem label_bounded (G rank : ℕ) : label G rank ≤ cap G :=
  (DyadicRankCompression.label_monotone (Nat.min_le_right _ _)).trans (le_max_right _ _)
theorem label_of_le {G rank : ℕ} (bounded : rank ≤ G-1) :
    label G rank = DyadicRankCompression.label rank := by
  simp [label, Nat.min_eq_left bounded]
theorem cap_lt_of_two_lt {G : ℕ} (large : 2 < G) : cap G < G := by
  have old := DyadicCompressionRowBudget.cap_lt_of_two_lt large
  have smaller := DyadicRankCompression.label_monotone (Nat.sub_le G 1)
  exact max_lt large (smaller.trans_lt old)

/-- Optimality inside the monotone zero-error-drop charging template,
using the actual historical alphabet 1,...,G-1. This is not a trace lower bound. -/
theorem optimal_actual_cap (L : ℕ → ℕ) (G R multiplier : ℕ)
    (large : 2 ≤ G) (two : 2 ≤ R) (positive : 1 ≤ L 1) (monotone : Monotone L)
    (bounded : L (G-1) ≤ R)
    (repair : ∀ rank, 1 ≤ rank → 2 * rank ≤ G-1 →
      L rank + 1 - L (2 * rank) ≤ multiplier * (L (2 * rank) - L rank)) :
    cap G ≤ R := by
  have lower := DyadicRankCompression.optimal_label_range L (G-1) multiplier
    (by omega) positive monotone repair
  exact max_le two (lower.trans bounded)

def ValidRow {n : ℕ} (params : Parameters) (timed : TimedAnnotatedPairShiftSnapshot n) : Prop :=
  RowValid params timed ∧ winnerRank timed ≤ params.valueBound - 1 ∧
    oldRank timed ≤ params.valueBound - 1 ∧ newRank timed ≤ params.valueBound - 1

abbrev charge := @ActualCompressionRowBudget.charge
abbrev earlyError := @ActualCompressionRowBudget.earlyError
abbrev lateCount := @ActualCompressionRowBudget.lateCount

theorem row_bounds {n : ℕ} {params : Parameters}
    {timed : TimedAnnotatedPairShiftSnapshot n} (valid : ValidRow params timed) :
    rowPositive (label params.valueBound) timed ≤ charge timed ∧
    rowPreparation (label params.valueBound) timed ≤
      rowNegative (label params.valueBound) timed + charge timed := by
  obtain ⟨winnerPositive, winnerBound, oldPositive, oldBound,
    newPositive, newBound, identity⟩ := valid.1
  have charged : ActualTimedErrorBudget.error timed ≤ (charge timed : ℤ) := by
    unfold charge ActualCompressionRowBudget.charge
    omega
  have integerBound : (newRank timed : ℤ) + winnerRank timed ≤
      oldRank timed + charge timed := by omega
  have bound : newRank timed + winnerRank timed ≤ oldRank timed + charge timed := by
    exact_mod_cast integerBound
  have rise := DyadicRankCompression.positive_relabel_bound bound
  have preparation := DyadicRankCompression.preparation_bound winnerPositive newPositive bound
  unfold rowPositive rowPreparation rowNegative
  rw [label_of_le valid.2.2.2, label_of_le valid.2.2.1, label_of_le valid.2.1]
  exact ⟨rise, preparation⟩

theorem row_combined_bound {n : ℕ} {params : Parameters}
    {timed : TimedAnnotatedPairShiftSnapshot n} (valid : ValidRow params timed) :
    rowPositive (label params.valueBound) timed +
      rowPreparation (label params.valueBound) timed ≤
        rowNegative (label params.valueBound) timed + charge timed := by
  obtain ⟨winnerPositive, winnerBound, oldPositive, oldBound,
    newPositive, newBound, identity⟩ := valid.1
  have charged : ActualTimedErrorBudget.error timed ≤ (charge timed : ℤ) := by
    unfold charge ActualCompressionRowBudget.charge
    omega
  have integerBound : (newRank timed : ℤ) + winnerRank timed ≤
      oldRank timed + charge timed := by omega
  have bound : newRank timed + winnerRank timed ≤ oldRank timed + charge timed := by
    exact_mod_cast integerBound
  have combined := DyadicRankCompression.combined_relabel_bound winnerPositive newPositive bound
  unfold rowPositive rowPreparation rowNegative
  rw [label_of_le valid.2.2.2, label_of_le valid.2.2.1, label_of_le valid.2.1]
  exact combined

theorem late_row_bounds {n : ℕ} (G : ℕ)
    (timed : TimedAnnotatedPairShiftSnapshot n) :
    rowPositive (label G) timed ≤ cap G - 1 ∧
    rowPreparation (label G) timed ≤ cap G := by
  have newBound := label_bounded G (newRank timed)
  have winnerBound := label_bounded G (winnerRank timed)
  have oldPositive := label_positive G (oldRank timed)
  unfold rowPositive rowPreparation
  omega

theorem rows_bounds {n : ℕ} {params : Parameters}
    (cutoff : ℕ) (snapshots : List (TimedAnnotatedPairShiftSnapshot n))
    (valid : ∀ timed ∈ snapshots, ValidRow params timed) :
    (snapshots.map (rowPositive (label params.valueBound))).sum ≤
      earlyError cutoff snapshots + (cap params.valueBound - 1) * lateCount cutoff snapshots ∧
    (snapshots.map (rowPositive (label params.valueBound))).sum +
      (snapshots.map (rowPreparation (label params.valueBound))).sum ≤
        (snapshots.map (rowNegative (label params.valueBound))).sum +
          earlyError cutoff snapshots + (2 * cap params.valueBound - 1) * lateCount cutoff snapshots := by
  induction snapshots with
  | nil => simp [earlyError, lateCount, ActualCompressionRowBudget.earlyError,
      ActualCompressionRowBudget.lateCount, significantTimedSnapshots]
  | cons timed snapshots ih =>
      have head := row_bounds (valid timed (by simp))
      have combined := row_combined_bound (valid timed (by simp))
      simp only [charge] at head combined
      have lateHead := late_row_bounds params.valueBound timed
      have capPositive := cap_positive params.valueBound
      have lateCombined : rowPositive (label params.valueBound) timed +
          rowPreparation (label params.valueBound) timed ≤ 2 * cap params.valueBound - 1 := by omega
      have tail := ih (by intro later member; exact valid later (by simp [member]))
      by_cases early : timed.annotated.sourcePassCount < cutoff
      · have notLate : ¬ cutoff ≤ timed.annotated.sourcePassCount := by omega
        simp [earlyError, ActualCompressionRowBudget.earlyError, significantTimedSnapshots,
          AnnotatedPairShiftSnapshot.significantDecision, early,
          lateCount, ActualCompressionRowBudget.lateCount, notLate, Nat.mul_add] at tail ⊢
        constructor <;> omega
      · have late : cutoff ≤ timed.annotated.sourcePassCount := by omega
        simp [earlyError, ActualCompressionRowBudget.earlyError, significantTimedSnapshots,
          AnnotatedPairShiftSnapshot.significantDecision, early,
          lateCount, ActualCompressionRowBudget.lateCount, late, Nat.mul_add] at tail ⊢
        constructor <;> omega

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
    (4 * cap params.valueBound - 2) * totalInserts operations +
      4 * (((1 + params.growingLimit) * cutoff + 1) * totalValueChanges operations) +
      (6 * cap params.valueBound - 4) * lateCount cutoff snapshots := by
  have ordinaryValid := ActualRelabelRows.history_valid history (EpisodeLedger.frozenValuesBound_empty params)
  have rankBounds := TightDyadicCompressionRanks.history_ranks history (TightDyadicCompressionRanks.empty params)
  have valid : ∀ timed ∈ snapshots, ValidRow params timed := by
    intro timed member
    exact ⟨ordinaryValid timed member, rankBounds timed member⟩
  have rows := rows_bounds cutoff snapshots valid
  have errors := ActualCompressionRowBudget.earlyError_le history initialState cutoff
  change earlyError cutoff snapshots ≤
    ((1 + params.growingLimit) * cutoff + 1) * totalValueChanges operations at errors
  have negatives := TightDyadicCompressionInventory.negative_le_insert_add_positive_tight
    (label_positive params.valueBound) (label_bounded params.valueBound)
    (history_rows (label params.valueBound) history)
  have positive := cap_positive params.valueBound
  have insertCoefficient : 4 * cap params.valueBound - 2 =
      2 * (cap params.valueBound + (cap params.valueBound - 1)) := by omega
  have tailCoefficient : 6 * cap params.valueBound - 4 =
      2 * ((cap params.valueBound - 1) + (2 * cap params.valueBound - 1)) := by omega
  rw [insertCoefficient, tailCoefficient]
  nlinarith

end Splay.Research.SharperDyadicCompressionRowBudget

#print axioms Splay.Research.SharperDyadicCompressionRowBudget.compiler_charge_bound
#print axioms Splay.Research.SharperDyadicCompressionRowBudget.cap_lt_of_two_lt
#print axioms Splay.Research.SharperDyadicCompressionRowBudget.optimal_actual_cap
