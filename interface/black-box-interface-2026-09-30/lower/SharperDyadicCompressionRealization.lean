import CappedHistoricalNumericTimedLift
import SharperDyadicCompressionRowBudget

/-! Dyadic historical compression all the way to its exact label cap.
The bounded preparation compiler needs no reserved extra cap unit. -/

namespace Splay.Research.SharperDyadicCompressionRealization

open Splay.Interface SharperDyadicCompressionRowBudget

def parameters (original : Parameters) : Parameters :=
  { toShape := original.toShape
    valueBound := cap original.valueBound
    valueBound_ge_two := cap_ge_two original.valueBound }

theorem cap_decreases {original : Parameters} (large : 2 < original.valueBound) :
    (parameters original).valueBound < original.valueBound :=
  cap_lt_of_two_lt large

theorem from_initial_trace {n : ℕ} {params : Parameters}
    {initial final : State n} {operations : List (Operation n)}
    (initialState : initial.Initial params) (original : Trace params initial operations final)
    (cutoff : ℕ) :
    ∃ finalLabels finalLedger finalClock finalEvents snapshots liftedOperations,
      LifetimeHistory.TimedPairShiftHistory params initial []
        (EpisodeLedger.empty : EpisodeLedger n) (fun _ => 0) []
        operations snapshots final finalLabels finalLedger finalClock finalEvents ∧
      (CappedHistoricalNumericStepLift.state (label params.valueBound) initial EpisodeLedger.empty).Initial
        (parameters params) ∧
      Trace (parameters params)
        (CappedHistoricalNumericStepLift.state (label params.valueBound) initial EpisodeLedger.empty)
        liftedOperations (CappedHistoricalNumericStepLift.state (label params.valueBound) final finalLedger) ∧
      totalActivity liftedOperations = totalActivity operations ∧
      totalBlockGrowth liftedOperations = totalBlockGrowth operations ∧
      totalInserts liftedOperations = totalInserts operations ∧
      totalValueChanges liftedOperations ≤
        (4 * cap params.valueBound - 2) * totalInserts operations +
          4 * (((1 + params.growingLimit) * cutoff + 1) * totalValueChanges operations) +
          (6 * cap params.valueBound - 4) * lateCount cutoff snapshots := by
  obtain ⟨finalLabels,finalLedger,finalClock,finalEvents,snapshots,liftedOperations,
      timed,newInitial,trace,activity,growth,inserts,changes⟩ :=
    CappedHistoricalNumericTimedLift.from_initial_trace (label params.valueBound)
      initialState original (params := parameters params) rfl
      (label_positive params.valueBound) (label_bounded params.valueBound)
      (cap_ge_two params.valueBound) (le_refl _)
  have budget := SharperDyadicCompressionRowBudget.compiler_charge_bound timed initialState cutoff
  refine ⟨finalLabels,finalLedger,finalClock,finalEvents,snapshots,liftedOperations,
    timed,newInitial,trace,activity,growth,inserts,?_⟩
  omega

end Splay.Research.SharperDyadicCompressionRealization

#print axioms Splay.Research.SharperDyadicCompressionRealization.from_initial_trace
#print axioms Splay.Research.SharperDyadicCompressionRealization.cap_decreases
