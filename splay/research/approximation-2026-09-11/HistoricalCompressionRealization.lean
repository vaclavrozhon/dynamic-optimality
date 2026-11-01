import HistoricalNumericTimedLift
import ActualCompressionRowBudget

/-! Literal historical-rank compression of every initialized strict
interface trace. The conclusion includes the actual new legal trace and
its variation budget on the original timed rows. -/

namespace Splay.Research.HistoricalCompressionRealization

open Splay.Interface
open Splay.Research.ActualCompressionRowBudget

noncomputable section

/-- Only the numeric cap changes. Every structural parameter is retained. -/
def parameters (original : Parameters) : Parameters :=
  { toShape := original.toShape
    valueBound := cap original.valueBound + 1
    valueBound_ge_two := by
      have positive := HistoricalRankCompression.natLabel_positive original.valueBound
      change 2 ≤ HistoricalRankCompression.natLabel original.valueBound + 1
      omega }

/-- This endpoint assumes only the original initialized legal trace. It
constructs the original timed history and the compressed trace together;
the activity, insert count, and block-growth count are exactly preserved. -/
theorem from_initial_trace {n : ℕ} {params : Parameters}
    {initial final : State n} {operations : List (Operation n)}
    (initialState : initial.Initial params) (original : Trace params initial operations final)
    (cutoff : ℕ) :
    ∃ finalLabels finalLedger finalClock finalEvents snapshots liftedOperations,
      LifetimeHistory.TimedPairShiftHistory params initial []
        (EpisodeLedger.empty : EpisodeLedger n) (fun _ => 0) []
        operations snapshots final finalLabels finalLedger finalClock finalEvents ∧
      (HistoricalNumericStepLift.state (label params.valueBound) initial EpisodeLedger.empty).Initial
        (parameters params) ∧
      Trace (parameters params)
        (HistoricalNumericStepLift.state (label params.valueBound) initial EpisodeLedger.empty)
        liftedOperations (HistoricalNumericStepLift.state (label params.valueBound) final finalLedger) ∧
      totalActivity liftedOperations = totalActivity operations ∧
      totalBlockGrowth liftedOperations = totalBlockGrowth operations ∧
      totalInserts liftedOperations = totalInserts operations ∧
      totalValueChanges liftedOperations ≤
        38 * cap params.valueBound * totalInserts operations +
          686 * (((1 + params.growingLimit) * cutoff + 1) * totalValueChanges operations) +
          (40 * cap params.valueBound + 2) * lateCount cutoff snapshots := by
  obtain ⟨finalLabels,finalLedger,finalClock,finalEvents,snapshots,liftedOperations,
      timed,newInitial,trace,activity,growth,inserts,changes⟩ :=
    HistoricalNumericTimedLift.from_initial_trace (label params.valueBound)
      initialState original (params := parameters params) rfl
      (label_positive params.valueBound) (label_bounded params.valueBound) (le_refl _)
  have budget := compiler_charge_bound timed initialState cutoff
  refine ⟨finalLabels,finalLedger,finalClock,finalEvents,snapshots,liftedOperations,
    timed,newInitial,trace,activity,growth,inserts,?_⟩
  omega

end
end Splay.Research.HistoricalCompressionRealization

#print axioms Splay.Research.HistoricalCompressionRealization.from_initial_trace
