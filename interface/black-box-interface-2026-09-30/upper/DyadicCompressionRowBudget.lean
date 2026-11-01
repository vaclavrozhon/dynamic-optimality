import ActualCompressionRowBudget
import DyadicRankCompression

/-! Dyadic local bounds on the original timed historical rows. The common
temporal incidence and source-tail objects are reused without modification. -/

namespace Splay.Research.DyadicCompressionRowBudget

open Splay.Interface ActualRelabelRows

def label (G rank : ℕ) : ℕ := DyadicRankCompression.label (min rank G)

def cap (G : ℕ) : ℕ := DyadicRankCompression.label G

theorem label_positive (G rank : ℕ) : 1 ≤ label G rank :=
  DyadicRankCompression.label_positive _

theorem cap_positive (G : ℕ) : 1 ≤ cap G :=
  DyadicRankCompression.label_positive _

theorem cap_ge_two {G : ℕ} (two : 2 ≤ G) : 2 ≤ cap G := by
  have h := DyadicRankCompression.label_monotone two
  have base : DyadicRankCompression.label 2 = 2 := by decide
  change 2 ≤ DyadicRankCompression.label G
  omega

theorem cap_lt_of_two_lt {G : ℕ} (large : 2 < G) : cap G < G := by
  have h := DyadicRankCompression.label_add_le 3 (G - 3)
  have equal : 3 + (G - 3) = G := by omega
  rw [equal] at h
  have base : DyadicRankCompression.label 3 = 2 := by decide
  change DyadicRankCompression.label G < G
  omega

theorem label_bounded (G rank : ℕ) : label G rank ≤ cap G :=
  DyadicRankCompression.label_monotone (Nat.min_le_right _ _)

theorem label_of_le {G rank : ℕ} (bounded : rank ≤ G) :
    label G rank = DyadicRankCompression.label rank := by
  simp [label, Nat.min_eq_left bounded]

abbrev charge := @ActualCompressionRowBudget.charge
abbrev earlyError := @ActualCompressionRowBudget.earlyError
abbrev lateCount := @ActualCompressionRowBudget.lateCount

theorem row_bounds {n : ℕ} {params : Parameters}
    {timed : TimedAnnotatedPairShiftSnapshot n} (valid : RowValid params timed) :
    rowPositive (label params.valueBound) timed ≤ charge timed ∧
    rowPreparation (label params.valueBound) timed ≤
      rowNegative (label params.valueBound) timed + charge timed := by
  obtain ⟨winnerPositive, winnerBound, oldPositive, oldBound,
    newPositive, newBound, identity⟩ := valid
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
  rw [label_of_le newBound, label_of_le oldBound, label_of_le winnerBound]
  exact ⟨rise, preparation⟩

theorem row_combined_bound {n : ℕ} {params : Parameters}
    {timed : TimedAnnotatedPairShiftSnapshot n} (valid : RowValid params timed) :
    rowPositive (label params.valueBound) timed +
      rowPreparation (label params.valueBound) timed ≤
        rowNegative (label params.valueBound) timed + charge timed := by
  obtain ⟨winnerPositive, winnerBound, oldPositive, oldBound,
    newPositive, newBound, identity⟩ := valid
  have charged : ActualTimedErrorBudget.error timed ≤ (charge timed : ℤ) := by
    unfold charge ActualCompressionRowBudget.charge
    omega
  have integerBound : (newRank timed : ℤ) + winnerRank timed ≤
      oldRank timed + charge timed := by omega
  have bound : newRank timed + winnerRank timed ≤ oldRank timed + charge timed := by
    exact_mod_cast integerBound
  have combined := DyadicRankCompression.combined_relabel_bound winnerPositive newPositive bound
  unfold rowPositive rowPreparation rowNegative
  rw [label_of_le newBound, label_of_le oldBound, label_of_le winnerBound]
  exact combined

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
      earlyError cutoff snapshots + cap params.valueBound * lateCount cutoff snapshots ∧
    (snapshots.map (rowPreparation (label params.valueBound))).sum ≤
      (snapshots.map (rowNegative (label params.valueBound))).sum +
        earlyError cutoff snapshots + (cap params.valueBound + 1) * lateCount cutoff snapshots := by
  induction snapshots with
  | nil => simp [earlyError, lateCount, ActualCompressionRowBudget.earlyError,
      ActualCompressionRowBudget.lateCount, significantTimedSnapshots]
  | cons timed snapshots ih =>
      have head := row_bounds (valid timed (by simp))
      simp only [charge] at head
      have lateHead := late_row_bounds params.valueBound timed
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
    P ≤ W + R * T ∧ N ≤ R * totalInserts operations + P ∧
      J ≤ N + W + (R + 1) * T := by
  have valid := history_valid history (EpisodeLedger.frozenValuesBound_empty params)
  have rows := rows_bounds cutoff snapshots valid
  have errors := ActualCompressionRowBudget.earlyError_le history initialState cutoff
  change earlyError cutoff snapshots ≤
    ((1 + params.growingLimit) * cutoff + 1) * totalValueChanges operations at errors
  have negatives := (history_rows (label params.valueBound) history).negative_le_insert_add_positive
    (label_positive params.valueBound) (label_bounded params.valueBound)
  dsimp
  constructor
  · omega
  constructor
  · exact negatives
  · omega

theorem rows_combined_bound {n : ℕ} {params : Parameters}
    (cutoff : ℕ) (snapshots : List (TimedAnnotatedPairShiftSnapshot n))
    (valid : ∀ timed ∈ snapshots, RowValid params timed) :
    (snapshots.map (rowPositive (label params.valueBound))).sum +
      (snapshots.map (rowPreparation (label params.valueBound))).sum ≤
        (snapshots.map (rowNegative (label params.valueBound))).sum +
          earlyError cutoff snapshots +
            (2 * cap params.valueBound + 1) * lateCount cutoff snapshots := by
  induction snapshots with
  | nil => simp [earlyError, lateCount, ActualCompressionRowBudget.earlyError,
      ActualCompressionRowBudget.lateCount, significantTimedSnapshots]
  | cons timed snapshots ih =>
      have head := row_combined_bound (valid timed (by simp))
      simp only [charge] at head
      have lateHead := late_row_bounds params.valueBound timed
      have tail := ih (by intro later member; exact valid later (by simp [member]))
      by_cases early : timed.annotated.sourcePassCount < cutoff
      · have notLate : ¬ cutoff ≤ timed.annotated.sourcePassCount := by omega
        simp [earlyError, ActualCompressionRowBudget.earlyError, significantTimedSnapshots,
          AnnotatedPairShiftSnapshot.significantDecision, early,
          lateCount, ActualCompressionRowBudget.lateCount, notLate] at tail ⊢
        omega
      · have late : cutoff ≤ timed.annotated.sourcePassCount := by omega
        simp [earlyError, ActualCompressionRowBudget.earlyError, significantTimedSnapshots,
          AnnotatedPairShiftSnapshot.significantDecision, early,
          lateCount, ActualCompressionRowBudget.lateCount, late, Nat.mul_add] at tail ⊢
        omega

theorem history_preparation_bound {n : ℕ} {params : Parameters}
    {initial final : State n} {finalLabels : RootLabels}
    {finalLedger : EpisodeLedger n} {finalClock : EpisodeClock n}
    {finalEvents : List (ValueChangeEvent n)} {operations : List (Operation n)}
    {snapshots : List (TimedAnnotatedPairShiftSnapshot n)}
    (history : LifetimeHistory.TimedPairShiftHistory params initial []
      (EpisodeLedger.empty : EpisodeLedger n) (fun _ => 0) []
      operations snapshots final finalLabels finalLedger finalClock finalEvents)
    (initialState : initial.Initial params) (cutoff : ℕ) :
    (snapshots.map (rowPreparation (label params.valueBound))).sum ≤
      cap params.valueBound * totalInserts operations +
        ((1 + params.growingLimit) * cutoff + 1) * totalValueChanges operations +
          (2 * cap params.valueBound + 1) * lateCount cutoff snapshots := by
  have valid := history_valid history (EpisodeLedger.frozenValuesBound_empty params)
  have combined := rows_combined_bound cutoff snapshots valid
  have errors := ActualCompressionRowBudget.earlyError_le history initialState cutoff
  change earlyError cutoff snapshots ≤
    ((1 + params.growingLimit) * cutoff + 1) * totalValueChanges operations at errors
  have negatives := (history_rows (label params.valueBound) history).negative_le_insert_add_positive
    (label_positive params.valueBound) (label_bounded params.valueBound)
  omega

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
    4 * cap params.valueBound * totalInserts operations +
      4 * (((1 + params.growingLimit) * cutoff + 1) * totalValueChanges operations) +
      (6 * cap params.valueBound + 2) * lateCount cutoff snapshots := by
  have bounds := history_bounds history initialState cutoff
  have preparation := history_preparation_bound history initialState cutoff
  dsimp at bounds
  nlinarith

#print axioms row_bounds
#print axioms compiler_charge_bound

end Splay.Research.DyadicCompressionRowBudget
