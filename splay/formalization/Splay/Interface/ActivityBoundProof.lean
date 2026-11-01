import Splay.Interface.GlobalDecay
import Splay.Interface.ShiftAccounting

namespace Splay.Interface

/--
Concrete semantic endpoint still required from the lifetime history.

There is exactly one `PairShiftSnapshot` per unit of activity.  The global
decay history chooses the insignificant suffix activity.  The three remaining
fields are precisely the significant/insignificant v- and u-incidence bounds
and the episode-chain w-telescoping bound; all subsequent arithmetic is
already verified below.
-/
def PairShiftHistoryHypothesis (shape : Shape) : Prop :=
  ∀ (params : Parameters), params.toShape = shape →
    ∀ {n : ℕ} {initial final : State n}
      {operations : List (Operation n)},
      initial.Initial params →
      Trace params initial operations final →
      ∃ (insignificantActivity : ℕ)
          (snapshots : List PairShiftSnapshot),
        snapshots.length = totalActivity operations ∧
          4 * params.valueBound * insignificantActivity ≤
            totalActivity operations + totalInserts operations ∧
          totalVShift snapshots ≤
            ((params.valueBound * insignificantActivity +
              FiberProfile.insignificantThreshold params *
                totalValueChanges operations : ℕ) : ℤ) ∧
          totalUShift snapshots ≤
            ((params.valueBound * insignificantActivity +
              params.growingLimit *
                FiberProfile.insignificantThreshold params *
                totalValueChanges operations : ℕ) : ℤ) ∧
          totalWShift snapshots ≤
            ((params.valueBound * totalInserts operations : ℕ) : ℤ)

/--
The exact per-pair snapshot obligations imply the manuscript's abstract
`ShiftChargingHypothesis`, with constants depending only on `Shape`.
-/
theorem shiftCharging_of_pairShiftHistory
    (shape : Shape)
    (historyCharging : PairShiftHistoryHypothesis shape) :
    ShiftChargingHypothesis shape 1
      ((shape.growingLimit + 1) *
        (shape.exemptPasses +
          3 * shape.matchingDenominator)) := by
  intro params params_shape n initial final operations initialState trace
  obtain
    ⟨insignificantActivity, snapshots, snapshot_count, decay_bound,
      v_bound, u_bound, w_bound⟩ :=
    historyCharging params params_shape initialState trace
  refine ⟨insignificantActivity, decay_bound, ?_⟩
  have activity_le_pairRank_nat :
      totalActivity operations ≤ totalPairRank snapshots := by
    rw [← snapshot_count]
    exact snapshots_length_le_totalPairRank snapshots
  have activity_le_pairRank :
      (totalActivity operations : ℤ) ≤
        (totalPairRank snapshots : ℤ) := by
    exact_mod_cast activity_le_pairRank_nat
  have explicitThresholdCharge :
      totalActivity operations ≤
        2 * params.valueBound * insignificantActivity +
          params.valueBound * totalInserts operations +
          (params.growingLimit + 1) *
            FiberProfile.insignificantThreshold params *
              totalValueChanges operations := by
    exact
      shiftCharge_of_aggregateBounds
        activity_le_pairRank
        (totalPairRank_eq_shifts snapshots)
        v_bound u_bound w_bound
  have logarithmicCharge :
      totalActivity operations ≤
        2 * params.valueBound * insignificantActivity +
          params.valueBound * totalInserts operations +
          ((params.growingLimit + 1) *
            (params.exemptPasses +
              3 * params.matchingDenominator)) *
            Nat.clog 2 params.valueBound *
              totalValueChanges operations := by
    exact
      shiftCharge_of_logarithmicThreshold explicitThresholdCharge
        (FiberProfile.insignificantThreshold_le_shape_mul_clog params)
  have growing_eq :
      params.growingLimit = shape.growingLimit :=
    congrArg Shape.growingLimit params_shape
  have exempt_eq :
      params.exemptPasses = shape.exemptPasses :=
    congrArg Shape.exemptPasses params_shape
  have denominator_eq :
      params.matchingDenominator = shape.matchingDenominator :=
    congrArg Shape.matchingDenominator params_shape
  simpa [growing_eq, exempt_eq, denominator_eq,
    Nat.one_mul] using logarithmicCharge

/--
Final reduction: constructing the checked pair-shift history is sufficient
for the unconditional interface theorem.  No asymptotic or continuity claim
remains hidden in this arithmetic step.
-/
theorem activityBound_of_pairShiftHistory
    (shape : Shape)
    (historyCharging : PairShiftHistoryHypothesis shape) :
    ActivityBound shape :=
  activityBound_of_shiftCharging shape 1
    ((shape.growingLimit + 1) *
      (shape.exemptPasses +
        3 * shape.matchingDenominator))
    (shiftCharging_of_pairShiftHistory shape historyCharging)

end Splay.Interface
