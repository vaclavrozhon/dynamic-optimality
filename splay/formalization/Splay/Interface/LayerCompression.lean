import Splay.Interface.BinaryLayerSum
import SharperDyadicCompressionRealization
import HistoricalCompressionTail

namespace Splay.Interface.LayerCompression

open Splay.Research ActualRelabelRows

abbrev label := SharperDyadicCompressionRowBudget.label
abbrev cap := SharperDyadicCompressionRowBudget.cap

/-- Logarithmic charge of one actual historical pairing row. -/
def rowCharge {n : ℕ} (row : TimedAnnotatedPairShiftSnapshot n) : ℕ :=
  LogarithmicRowCharge.charge (ActualCompressionRowBudget.charge row)

def totalCharge {n : ℕ} (rows : List (TimedAnnotatedPairShiftSnapshot n)) : ℕ :=
  (rows.map rowCharge).sum

/-- A shape constant for the early-error budget at any halving cutoff. -/
def shapeConstant (shape : Shape) : ℕ :=
  (1 + shape.growingLimit) * (shape.exemptPasses + shape.matchingDenominator) + 1

theorem row_bounds {n : ℕ} {params : Parameters}
    {row : TimedAnnotatedPairShiftSnapshot n}
    (valid : SharperDyadicCompressionRowBudget.ValidRow params row) :
    rowPositive (label params.valueBound) row ≤ rowCharge row ∧
    rowPositive (label params.valueBound) row + rowPreparation (label params.valueBound) row ≤
      rowNegative (label params.valueBound) row + 2 * rowCharge row := by
  obtain ⟨winnerPositive, winnerBound, oldPositive, oldBound,
    newPositive, newBound, identity⟩ := valid.1
  have charged : ActualTimedErrorBudget.error row ≤ (ActualCompressionRowBudget.charge row : ℤ) := by
    unfold ActualCompressionRowBudget.charge
    omega
  have integerBound : (newRank row : ℤ) + winnerRank row ≤
      oldRank row + ActualCompressionRowBudget.charge row := by omega
  have bound : newRank row + winnerRank row ≤ oldRank row + ActualCompressionRowBudget.charge row := by
    exact_mod_cast integerBound
  have rise := LogarithmicRowCharge.positive_bound oldPositive bound
  have combined := LogarithmicRowCharge.combined_bound winnerPositive oldPositive newPositive bound
  unfold rowPositive rowPreparation rowNegative label
  rw [SharperDyadicCompressionRowBudget.label_of_le valid.2.2.2,
    SharperDyadicCompressionRowBudget.label_of_le valid.2.2.1,
    SharperDyadicCompressionRowBudget.label_of_le valid.2.1]
  exact ⟨rise, combined⟩

theorem rows_bounds {n : ℕ} {params : Parameters}
    (rows : List (TimedAnnotatedPairShiftSnapshot n))
    (valid : ∀ row ∈ rows, SharperDyadicCompressionRowBudget.ValidRow params row) :
    (rows.map (rowPositive (label params.valueBound))).sum ≤ totalCharge rows ∧
    (rows.map (rowPositive (label params.valueBound))).sum +
      (rows.map (rowPreparation (label params.valueBound))).sum ≤
        (rows.map (rowNegative (label params.valueBound))).sum + 2 * totalCharge rows := by
  induction rows with
  | nil => simp [totalCharge]
  | cons row rows ih =>
    have head := row_bounds (valid row (by simp))
    have tail := ih (fun later member => valid later (by simp [member]))
    simp only [totalCharge, List.map_cons, List.sum_cons] at tail ⊢
    constructor <;> omega

/-- The existing numerical compiler, now paid by logarithmic errors.
Neither the variation charge nor the later cutoff contains the outer cap. -/
theorem compiler_charge_bound {n : ℕ} {params : Parameters}
    {initial final : State n} {finalLabels : RootLabels}
    {finalLedger : EpisodeLedger n} {finalClock : EpisodeClock n}
    {finalEvents : List (ValueChangeEvent n)} {operations : List (Operation n)}
    {rows : List (TimedAnnotatedPairShiftSnapshot n)}
    (history : LifetimeHistory.TimedPairShiftHistory params initial []
      (EpisodeLedger.empty : EpisodeLedger n) (fun _ => 0) []
      operations rows final finalLabels finalLedger finalClock finalEvents) :
    2 * (cap params.valueBound * totalInserts operations +
      (rows.map (rowPositive (label params.valueBound))).sum +
      (rows.map (rowPreparation (label params.valueBound))).sum) ≤
      (4 * cap params.valueBound - 2) * totalInserts operations + 6 * totalCharge rows := by
  have ordinary := history_valid history (EpisodeLedger.frozenValuesBound_empty params)
  have ranks := TightDyadicCompressionRanks.history_ranks history (TightDyadicCompressionRanks.empty params)
  have bounds := rows_bounds rows (fun row member => ⟨ordinary row member, ranks row member⟩)
  have negatives := TightDyadicCompressionInventory.negative_le_insert_add_positive_tight
    (SharperDyadicCompressionRowBudget.label_positive params.valueBound)
    (SharperDyadicCompressionRowBudget.label_bounded params.valueBound)
    (history_rows (label params.valueBound) history)
  have positive := SharperDyadicCompressionRowBudget.cap_positive params.valueBound
  have coefficient : 4 * cap params.valueBound - 2 =
      2 * (cap params.valueBound + (cap params.valueBound - 1)) := by omega
  rw [coefficient]
  nlinarith only [bounds.1, bounds.2, negatives]

/-- Binary error layers combine the already verified early-error account
and late-source decay on the same literal history. -/
theorem totalCharge_bound {n : ℕ} {params : Parameters}
    {initial final : State n} {finalLabels : RootLabels}
    {finalLedger : EpisodeLedger n} {finalClock : EpisodeClock n}
    {finalEvents : List (ValueChangeEvent n)} {operations : List (Operation n)}
    {rows : List (TimedAnnotatedPairShiftSnapshot n)}
    (history : LifetimeHistory.TimedPairShiftHistory params initial []
      (EpisodeLedger.empty : EpisodeLedger n) (fun _ => 0) []
      operations rows final finalLabels finalLedger finalClock finalEvents)
    (initialized : initial.Initial params) (k : ℕ) :
    2 ^ k * totalCharge rows ≤
      2 ^ k * (2 * shapeConstant params.toShape * (k + 2) * totalValueChanges operations) +
        2 * (totalActivity operations + totalInserts operations) := by
  let early := fun j (row : TimedAnnotatedPairShiftSnapshot n) =>
    decide (row.annotated.sourcePassCount < ArbitrarySourceTail.threshold params j)
  apply BinaryLayerSum.logarithmic_charge_bound
    ActualCompressionRowBudget.charge rows early (shapeConstant params.toShape)
    (totalValueChanges operations) (totalActivity operations + totalInserts operations) ?_ ?_ k
  · intro j
    have budget := ActualCompressionRowBudget.earlyError_le history initialized
      (ArbitrarySourceTail.threshold params j)
    change ((rows.filter (early j)).map ActualCompressionRowBudget.charge).sum ≤
      ((1 + params.growingLimit) * (params.exemptPasses + params.matchingDenominator * j) + 1) *
        totalValueChanges operations at budget
    apply budget.trans
    apply Nat.mul_le_mul_right
    dsimp [shapeConstant]
    ring_nf
    omega
  · intro j
    have budget := HistoricalCompressionTail.timed_tail_bound initialized history j
    have filters : (rows.filter fun row => !(early j row)) =
        rows.filter fun row => decide (ArbitrarySourceTail.threshold params j ≤ row.annotated.sourcePassCount) := by
      apply List.filter_congr
      intro row _
      by_cases low : row.annotated.sourcePassCount < ArbitrarySourceTail.threshold params j
      · simp [early, low, show ¬ArbitrarySourceTail.threshold params j ≤ row.annotated.sourcePassCount by omega]
      · simp [early, low, show ArbitrarySourceTail.threshold params j ≤ row.annotated.sourcePassCount by omega]
    rw [filters]
    exact budget

end Splay.Interface.LayerCompression
