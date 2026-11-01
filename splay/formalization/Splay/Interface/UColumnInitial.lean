import Splay.Interface.UAdjacentCutHistory
import Splay.Interface.UEventGrowingHistory

namespace Splay.Interface

namespace LifetimeHistory

/--
For the concrete timed history constructed by the activity proof, the
root/pass-floor step invariant closes the full significant `u` column.
-/
theorem TimedPairShiftHistory.significant_uColumn_le_of_initial
    (rootStep : ClockCutRootStepHypothesis)
    {n : ℕ} {params : Parameters}
    {initial final : State n} {finalLabels : RootLabels}
    {finalLedger : EpisodeLedger n} {finalClock : EpisodeClock n}
    {finalEvents : List (ValueChangeEvent n)}
    {operations : List (Operation n)}
    {snapshots : List (TimedAnnotatedPairShiftSnapshot n)}
    (history :
      TimedPairShiftHistory params initial []
        (EpisodeLedger.empty : EpisodeLedger n)
        (fun _ => 0) [] operations snapshots
        final finalLabels finalLedger finalClock finalEvents)
    (initialState : initial.Initial params)
    (threshold : ℕ) (event : Fin finalEvents.length) :
    ((significantTimedSnapshots threshold snapshots).map fun timed =>
        |timed.uTemporalCharge finalEvents event|).sum ≤
      ((params.growingLimit * threshold : ℕ) : ℤ) := by
  have cut :
      UAdjacentCutInvariant finalEvents threshold snapshots :=
    history.uAdjacentCutInvariant_of_initial
      (clockCutStateStepHypothesis_of_root rootStep)
      initialState threshold
  have eventRoots :
      UEventGrowingRoots params finalEvents threshold snapshots :=
    history.uEventGrowingRoots_of_initial initialState threshold
  exact
    significant_uColumn_le finalEvents threshold snapshots
      cut eventRoots event

end LifetimeHistory

/--
Exact concrete-start `u`-column API consumed by the final assembly.
-/
def InitialSignificantUColumnIncidenceHypothesis : Prop :=
  ∀ {n : ℕ} {params : Parameters}
    {initial final : State n} {finalLabels : RootLabels}
    {finalLedger : EpisodeLedger n} {finalClock : EpisodeClock n}
    {finalEvents : List (ValueChangeEvent n)}
    {operations : List (Operation n)}
    {snapshots : List (TimedAnnotatedPairShiftSnapshot n)},
    initial.Initial params →
      LifetimeHistory.TimedPairShiftHistory params initial []
        (EpisodeLedger.empty : EpisodeLedger n)
        (fun _ => 0) [] operations snapshots
        final finalLabels finalLedger finalClock finalEvents →
      ∀ event : Fin finalEvents.length,
        ((significantTimedSnapshots
            (FiberProfile.insignificantThreshold params)
            snapshots).map fun timed =>
          |timed.uTemporalCharge finalEvents event|).sum ≤
            ((params.growingLimit *
              FiberProfile.insignificantThreshold params : ℕ) : ℤ)

/-- The remaining root/pass-floor step invariant implies the concrete API. -/
theorem initialSignificantUColumnIncidence_of_rootStep
    (rootStep : ClockCutRootStepHypothesis) :
    InitialSignificantUColumnIncidenceHypothesis := by
  intro n params initial final finalLabels finalLedger finalClock
    finalEvents operations snapshots initialState history event
  exact
    history.significant_uColumn_le_of_initial rootStep initialState
      (FiberProfile.insignificantThreshold params) event

end Splay.Interface
