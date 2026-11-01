import Splay.Interface.ActivityBoundProof
import Splay.Interface.RootDecayBridge
import Splay.Interface.WShiftTrace
import Splay.Interface.ShiftIncidence

namespace Splay.Interface

open scoped BigOperators

/--
The one remaining model-specific lemma needed by the final assembly.

For every timed chronological snapshot history, a value-change event belongs
to at most `threshold` significant `v` intervals and to at most
`growingLimit * threshold` significant `u` intervals.  All other ingredients
of `PairShiftHistoryHypothesis` are constructed below from an ordinary trace.
-/
def SignificantColumnIncidenceHypothesis : Prop :=
  ∀ {n : ℕ} {params : Parameters}
    {initial final : State n}
    {initialLabels finalLabels : RootLabels}
    {initialLedger finalLedger : EpisodeLedger n}
    {initialClock finalClock : EpisodeClock n}
    {finalEvents : List (ValueChangeEvent n)}
    {operations : List (Operation n)}
    {timedSnapshots : List (TimedAnnotatedPairShiftSnapshot n)},
    LifetimeHistory.TimedPairShiftHistory params
        initial initialLabels initialLedger initialClock []
        operations timedSnapshots
        final finalLabels finalLedger finalClock finalEvents →
      (∀ event : Fin finalEvents.length,
          ((significantTimedSnapshots
              (FiberProfile.insignificantThreshold params)
              timedSnapshots).map fun timed =>
            |timed.vTemporalCharge finalEvents event|).sum ≤
              (FiberProfile.insignificantThreshold params : ℤ)) ∧
        (∀ event : Fin finalEvents.length,
          ((significantTimedSnapshots
              (FiberProfile.insignificantThreshold params)
              timedSnapshots).map fun timed =>
            |timed.uTemporalCharge finalEvents event|).sum ≤
              ((params.growingLimit *
                FiberProfile.insignificantThreshold params : ℕ) : ℤ))

/--
The exact incidence API needed by the activity proof.  Unlike the more
general compatibility API above, it only quantifies over the concrete timed
history lifted from an interface trace: empty labels, ledger, clock, and
event list at the initial state.
-/
def InitialSignificantColumnIncidenceHypothesis : Prop :=
  ∀ {n : ℕ} {params : Parameters}
    {initial final : State n}
    {finalLabels : RootLabels}
    {finalLedger : EpisodeLedger n}
    {finalClock : EpisodeClock n}
    {finalEvents : List (ValueChangeEvent n)}
    {operations : List (Operation n)}
    {timedSnapshots : List (TimedAnnotatedPairShiftSnapshot n)},
    initial.Initial params →
      LifetimeHistory.TimedPairShiftHistory params
          initial [] (EpisodeLedger.empty : EpisodeLedger n)
          (fun _ => 0) [] operations timedSnapshots
          final finalLabels finalLedger finalClock finalEvents →
        (∀ event : Fin finalEvents.length,
            ((significantTimedSnapshots
                (FiberProfile.insignificantThreshold params)
                timedSnapshots).map fun timed =>
              |timed.vTemporalCharge finalEvents event|).sum ≤
                (FiberProfile.insignificantThreshold params : ℤ)) ∧
          (∀ event : Fin finalEvents.length,
            ((significantTimedSnapshots
                (FiberProfile.insignificantThreshold params)
                timedSnapshots).map fun timed =>
              |timed.uTemporalCharge finalEvents event|).sum ≤
                ((params.growingLimit *
                  FiberProfile.insignificantThreshold params : ℕ) : ℤ))

/--
The column-incidence lemma assembles with exact lifetime histories, global
root decay, frozen-value bounds, and insert-rooted `w` telescoping to produce
the complete pair-shift hypothesis.
-/
theorem pairShiftHistoryHypothesis_of_initialSignificantColumnIncidence
    (shape : Shape)
    (columnIncidence : InitialSignificantColumnIncidenceHypothesis) :
    PairShiftHistoryHypothesis shape := by
  intro params _paramsShape n initial final operations initialState trace
  obtain ⟨finalLabels, lineageHistory, _finalAligned⟩ :=
    HistoryTrace.lift_initial initialState trace
  obtain ⟨joins, joinHistory⟩ :=
    JoinHistory.lift lineageHistory
  obtain ⟨finalLedger, leaves, closed, lifetimeHistory⟩ :=
    LifetimeHistory.lift joinHistory
      (EpisodeLedger.empty : EpisodeLedger n)
  have initialAligned :
      ([] : RootLabels).length = initial.blocks.length := by
    simp [initialState.2]
  have initialExact :
      EpisodeLedger.ExactAt initial []
        (EpisodeLedger.empty : EpisodeLedger n) :=
    EpisodeLedger.ExactAt.initial initialState
  let initialClock : EpisodeClock n := fun _ => 0
  have initialClockSound :
      EpisodeClock.SoundAt initial
        (EpisodeLedger.empty : EpisodeLedger n)
        initialClock [] :=
    EpisodeClock.soundAt_empty initial initialClock []
  obtain
      ⟨finalClock, finalEvents, timedSnapshots, timedHistory⟩ :=
    lifetimeHistory.lift_timedPairShiftSnapshots
      initialClock [] initialAligned initialExact initialClockSound
  let threshold := FiberProfile.insignificantThreshold params
  let annotatedSnapshots :=
    timedSnapshots.map TimedAnnotatedPairShiftSnapshot.annotated
  let snapshots :=
    annotatedSnapshots.map AnnotatedPairShiftSnapshot.snapshot
  have annotatedHistory :
      LifetimeHistory.AnnotatedPairShiftHistory params initial []
        (EpisodeLedger.empty : EpisodeLedger n)
        operations annotatedSnapshots final finalLabels finalLedger := by
    simpa [annotatedSnapshots] using timedHistory.erase
  have snapshotHistory :
      LifetimeHistory.PairShiftSnapshotHistory params initial []
        (EpisodeLedger.empty : EpisodeLedger n)
        operations snapshots final finalLabels finalLedger := by
    simpa [snapshots] using annotatedHistory.erase
  let insignificantActivity :=
    (insignificantAnnotatedSnapshots threshold annotatedSnapshots).length
  have frozen :
      EpisodeLedger.FrozenValuesBound params
        (EpisodeLedger.empty : EpisodeLedger n) :=
    EpisodeLedger.frozenValuesBound_empty params
  let significancePartition :=
    annotatedHistory.significancePartition frozen threshold

  have concreteIncidence := columnIncidence initialState timedHistory
  have vIncidence :
      ∀ event : Fin finalEvents.length,
        ((significantTimedSnapshots threshold timedSnapshots).map fun timed =>
          |timed.vTemporalCharge finalEvents event|).sum ≤
            (threshold : ℤ) := by
    simpa [threshold] using concreteIncidence.1
  have uIncidence :
      ∀ event : Fin finalEvents.length,
        ((significantTimedSnapshots threshold timedSnapshots).map fun timed =>
          |timed.uTemporalCharge finalEvents event|).sum ≤
            ((params.growingLimit * threshold : ℕ) : ℤ) := by
    simpa [threshold] using concreteIncidence.2
  have significantBounds :=
    timedHistory.significant_shift_bounds threshold vIncidence uIncidence
  have significantVBound :
      totalVShift significancePartition.significant ≤
        ((threshold * totalValueChanges operations : ℕ) : ℤ) := by
    change
      totalVShift
          (significantPairShiftSnapshots threshold annotatedSnapshots) ≤
        ((threshold * totalValueChanges operations : ℕ) : ℤ)
    simpa [annotatedSnapshots] using significantBounds.1
  have significantUBound :
      totalUShift significancePartition.significant ≤
        ((params.growingLimit * threshold *
          totalValueChanges operations : ℕ) : ℤ) := by
    change
      totalUShift
          (significantPairShiftSnapshots threshold annotatedSnapshots) ≤
        ((params.growingLimit * threshold *
          totalValueChanges operations : ℕ) : ℤ)
    simpa [annotatedSnapshots] using significantBounds.2
  have vBound :
      totalVShift snapshots ≤
        ((params.valueBound * insignificantActivity +
          threshold * totalValueChanges operations : ℕ) : ℤ) := by
    have combined :=
      significancePartition.totalVShift_le_of_significant significantVBound
    simpa only [Nat.cast_add] using combined
  have uBound :
      totalUShift snapshots ≤
        ((params.valueBound * insignificantActivity +
          params.growingLimit * threshold *
            totalValueChanges operations : ℕ) : ℤ) := by
    have combined :=
      significancePartition.totalUShift_le_of_significant significantUBound
    simpa only [Nat.cast_add] using combined

  obtain ⟨activityOccurrences, activityHistory, tailCount⟩ :=
    LifetimeHistory.AnnotatedPairShiftHistory.lift_activityHistory_with_tail
      threshold annotatedHistory
  obtain ⟨conversionOccurrences, conversionHistory⟩ :=
    RootConversionHistory.lift lineageHistory
  have decayToConversion :=
    activityHistory.global_tailActivity_le_conversionMass_of_initial
      conversionHistory initialState
  have conversionBalance := conversionHistory.growingMass_balance
  have initialGrowingZero : initial.growingMass = 0 := by
    simp [State.growingMass, growingMassBlocks, initialState.2]
  rw [initialGrowingZero, zero_add] at conversionBalance
  have conversionBound :
      (conversionOccurrences.map
          ConversionOccurrence.convertedMass).sum ≤
        totalActivity operations + totalInserts operations := by
    omega
  have tailDecay :
      4 * params.valueBound *
          tailActivity activityOccurrences threshold ≤
        totalActivity operations + totalInserts operations :=
    decayToConversion.trans conversionBound
  have insignificantEqTail :
      insignificantActivity =
        tailActivity activityOccurrences threshold := by
    simpa [insignificantActivity] using tailCount
  have decayBound :
      4 * params.valueBound * insignificantActivity ≤
        totalActivity operations + totalInserts operations := by
    rw [insignificantEqTail]
    exact tailDecay

  have chainPartition :
      Nonempty
        (SnapshotChainPartition params operations snapshots) :=
    snapshotHistory.snapshotChainPartition_nonempty
  have wBound :
      totalWShift snapshots ≤
        ((params.valueBound * totalInserts operations : ℕ) : ℤ) :=
    SnapshotChainPartition.totalWShift_le_valueBound_mul_totalInserts
      (Classical.choice chainPartition)
  have snapshotCount :
      snapshots.length = totalActivity operations := by
    simpa [snapshots, annotatedSnapshots] using
      timedHistory.snapshots_length
  refine
    ⟨insignificantActivity, snapshots, snapshotCount, decayBound, ?_, ?_,
      wBound⟩
  · simpa [threshold] using vBound
  · simpa [threshold] using uBound

/--
The older general incidence API implies the concrete-start API consumed by
the assembly.
-/
theorem pairShiftHistoryHypothesis_of_significantColumnIncidence
    (shape : Shape)
    (columnIncidence : SignificantColumnIncidenceHypothesis) :
    PairShiftHistoryHypothesis shape :=
  pairShiftHistoryHypothesis_of_initialSignificantColumnIncidence shape <| by
    intro n params initial final finalLabels finalLedger finalClock
      finalEvents operations timedSnapshots _initialState history
    exact columnIncidence history

/--
The concrete chronological incidence theorem is sufficient for the
unconditional interface activity theorem.
-/
theorem activityBound_of_initialSignificantColumnIncidence
    (shape : Shape)
    (columnIncidence : InitialSignificantColumnIncidenceHypothesis) :
    ActivityBound shape :=
  activityBound_of_pairShiftHistory shape
    (pairShiftHistoryHypothesis_of_initialSignificantColumnIncidence
      shape columnIncidence)

/--
Final public reduction: proving the single chronological column-incidence
lemma is sufficient for the unconditional interface activity theorem.
-/
theorem activityBound_of_significantColumnIncidence
    (shape : Shape)
    (columnIncidence : SignificantColumnIncidenceHypothesis) :
    ActivityBound shape :=
  activityBound_of_pairShiftHistory shape
    (pairShiftHistoryHypothesis_of_significantColumnIncidence
      shape columnIncidence)

end Splay.Interface
