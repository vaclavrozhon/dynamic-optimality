import Splay.Interface.ShiftIncidence
import Splay.Interface.RootPhaseHistory
import Splay.Interface.GlobalDecay

namespace Splay.Interface

/-- The lineage/pass-counter column occupied by one timed pair snapshot. -/
def TimedAnnotatedPairShiftSnapshot.uRunKey {n : ℕ}
    (timed : TimedAnnotatedPairShiftSnapshot n) : LineageRunKey :=
  (timed.annotated.sourceRoot, timed.annotated.sourcePassCount)

/-- The fixed event lies strictly between the two episode-opening clocks. -/
def TimedAnnotatedPairShiftSnapshot.UClockStraddlesAt {n : ℕ}
    (timed : TimedAnnotatedPairShiftSnapshot n) (eventIndex : ℕ) : Prop :=
  (timed.winnerStartEvent ≤ eventIndex ∧
      eventIndex < timed.loserStartEvent) ∨
    (timed.loserStartEvent ≤ eventIndex ∧
      eventIndex < timed.winnerStartEvent)

instance TimedAnnotatedPairShiftSnapshot.instDecidableUClockStraddlesAt
    {n : ℕ} (timed : TimedAnnotatedPairShiftSnapshot n)
    (eventIndex : ℕ) :
    Decidable (timed.UClockStraddlesAt eventIndex) := by
  unfold TimedAnnotatedPairShiftSnapshot.UClockStraddlesAt
  infer_instance

/--
Nonzero `u` incidence has the exact geometric meaning needed by the adjacent
cut proof: the event changes the source creator, occurs before the pass, and
strictly separates the two endpoint clocks.
-/
theorem TimedAnnotatedPairShiftSnapshot.uTemporalCharge_ne_zero_facts
    {n : ℕ} (finalEvents : List (ValueChangeEvent n))
    (timed : TimedAnnotatedPairShiftSnapshot n)
    (event : Fin finalEvents.length)
    (nonzero : timed.uTemporalCharge finalEvents event ≠ 0) :
    event.val < timed.eventsBefore.length ∧
      ValueChangeEvent.isFor timed.annotated.sourceCreator
        (finalEvents.get event) ∧
      timed.UClockStraddlesAt event.val := by
  let winnerActive : Prop :=
    timed.winnerStartEvent ≤ event.val ∧
      event.val < timed.eventsBefore.length ∧
      ValueChangeEvent.isFor timed.annotated.sourceCreator
        (finalEvents.get event)
  let loserActive : Prop :=
    timed.loserStartEvent ≤ event.val ∧
      event.val < timed.eventsBefore.length ∧
      ValueChangeEvent.isFor timed.annotated.sourceCreator
        (finalEvents.get event)
  by_cases winner : winnerActive
  · by_cases loser : loserActive
    · change
        timed.winnerStartEvent ≤ event.val ∧
          event.val < timed.eventsBefore.length ∧
          ValueChangeEvent.isFor timed.annotated.sourceCreator
            (finalEvents.get event) at winner
      change
        timed.loserStartEvent ≤ event.val ∧
          event.val < timed.eventsBefore.length ∧
          ValueChangeEvent.isFor timed.annotated.sourceCreator
            (finalEvents.get event) at loser
      simp [uTemporalCharge, eventIntervalCharge, winner, loser] at nonzero
    · have loser_start_gt :
          event.val < timed.loserStartEvent := by
        apply Nat.lt_of_not_ge
        intro loser_start
        apply loser
        exact ⟨loser_start, winner.2⟩
      exact
        ⟨winner.2.1, winner.2.2,
          Or.inl ⟨winner.1, loser_start_gt⟩⟩
  · by_cases loser : loserActive
    · have winner_start_gt :
          event.val < timed.winnerStartEvent := by
        apply Nat.lt_of_not_ge
        intro winner_start
        apply winner
        exact ⟨winner_start, loser.2⟩
      exact
        ⟨loser.2.1, loser.2.2,
          Or.inr ⟨loser.1, winner_start_gt⟩⟩
    · change
        ¬((if winnerActive then (1 : ℤ) else 0) -
            (if loserActive then 1 else 0) = 0) at nonzero
      simp [winner, loser] at nonzero

/-- Every member of the concrete incident list supplies the straddling cut. -/
theorem mem_uIncidentTimedSnapshots_clockStraddles
    {n : ℕ} (finalEvents : List (ValueChangeEvent n))
    (event : Fin finalEvents.length)
    (snapshots : List (TimedAnnotatedPairShiftSnapshot n))
    {timed : TimedAnnotatedPairShiftSnapshot n}
    (member :
      timed ∈ uIncidentTimedSnapshots finalEvents event snapshots) :
    event.val < timed.eventsBefore.length ∧
      ValueChangeEvent.isFor timed.annotated.sourceCreator
        (finalEvents.get event) ∧
      timed.UClockStraddlesAt event.val := by
  have nonzero :
      timed.uTemporalCharge finalEvents event ≠ 0 := by
    simpa using (List.mem_filter.mp member).2
  exact
    timed.uTemporalCharge_ne_zero_facts finalEvents event nonzero

/-- An incident creator column is necessarily for the event's changed element. -/
theorem eventElement_eq_sourceCreator_of_mem_uIncident
    {n : ℕ} (finalEvents : List (ValueChangeEvent n))
    (event : Fin finalEvents.length)
    (snapshots : List (TimedAnnotatedPairShiftSnapshot n))
    {timed : TimedAnnotatedPairShiftSnapshot n}
    (member :
      timed ∈ uIncidentTimedSnapshots finalEvents event snapshots) :
    (finalEvents.get event).element =
      timed.annotated.sourceCreator := by
  have selected :=
    (mem_uIncidentTimedSnapshots_clockStraddles
      finalEvents event snapshots member).2.1
  simpa [ValueChangeEvent.isFor] using selected

/--
The purely structural super-column selected by one chronological clock cut.
Unlike `uIncidentTimedSnapshots`, this forgets both the changed creator and
the significance threshold; every concrete `u` column is a sublist of it.
-/
def clockCrossingTimedSnapshots {n : ℕ} (eventIndex : ℕ)
    (snapshots : List (TimedAnnotatedPairShiftSnapshot n)) :
    List (TimedAnnotatedPairShiftSnapshot n) :=
  snapshots.filter fun timed =>
    decide (timed.UClockStraddlesAt eventIndex)

/--
Concrete `u` incidence, after the significance filter, preserves chronological
order inside the structural clock-crossing column.
-/
theorem uIncident_significant_sublist_clockCrossing
    {n : ℕ} (finalEvents : List (ValueChangeEvent n))
    (event : Fin finalEvents.length) (threshold : ℕ)
    (snapshots : List (TimedAnnotatedPairShiftSnapshot n)) :
    (uIncidentTimedSnapshots finalEvents event
        (significantTimedSnapshots threshold snapshots)).Sublist
      (clockCrossingTimedSnapshots event.val snapshots) := by
  induction snapshots with
  | nil =>
      exact .slnil
  | cons timed snapshots ih =>
      by_cases significant :
          timed.annotated.sourcePassCount < threshold
      · by_cases incident :
          timed.uTemporalCharge finalEvents event ≠ 0
        · have crossing : timed.UClockStraddlesAt event.val :=
            (timed.uTemporalCharge_ne_zero_facts
              finalEvents event incident).2.2
          have crossingDecision :
              decide (timed.UClockStraddlesAt event.val) = true := by
            simp [crossing]
          simpa [uIncidentTimedSnapshots, significantTimedSnapshots,
            AnnotatedPairShiftSnapshot.significantDecision,
            clockCrossingTimedSnapshots, significant, incident,
            crossingDecision]
            using ih.cons_cons timed
        · by_cases crossing : timed.UClockStraddlesAt event.val
          · have crossingDecision :
                decide (timed.UClockStraddlesAt event.val) = true := by
              simp [crossing]
            simpa [uIncidentTimedSnapshots, significantTimedSnapshots,
              AnnotatedPairShiftSnapshot.significantDecision,
              clockCrossingTimedSnapshots, significant, incident,
              crossingDecision]
              using ih.cons timed
          · have crossingDecision :
                decide (timed.UClockStraddlesAt event.val) = false := by
              simp [crossing]
            simpa [uIncidentTimedSnapshots, significantTimedSnapshots,
              AnnotatedPairShiftSnapshot.significantDecision,
              clockCrossingTimedSnapshots, significant, incident,
              crossingDecision]
              using ih
      · by_cases crossing : timed.UClockStraddlesAt event.val
        · have crossingDecision :
              decide (timed.UClockStraddlesAt event.val) = true := by
            simp [crossing]
          simpa [uIncidentTimedSnapshots, significantTimedSnapshots,
            AnnotatedPairShiftSnapshot.significantDecision,
            clockCrossingTimedSnapshots, significant, crossingDecision]
            using ih.cons timed
        · have crossingDecision :
              decide (timed.UClockStraddlesAt event.val) = false := by
            simp [crossing]
          simpa [uIncidentTimedSnapshots, significantTimedSnapshots,
            AnnotatedPairShiftSnapshot.significantDecision,
            clockCrossingTimedSnapshots, significant, crossingDecision]
            using ih

/--
The actual history invariant required from the clock-order induction: all
clock-crossing pair snapshots have distinct lineage/pass-counter keys.
-/
def ClockCrossingRunKeysNodup {n : ℕ}
    (snapshots : List (TimedAnnotatedPairShiftSnapshot n)) : Prop :=
  ∀ eventIndex : ℕ,
    ((clockCrossingTimedSnapshots eventIndex snapshots).map
      TimedAnnotatedPairShiftSnapshot.uRunKey).Nodup

/--
Exact clock-order cut invariant still needed from the ordered lineage
history: at one fixed event, two chronological incident pairs cannot occupy
the same `(root, passCount)` column.

This is deliberately stated as `Pairwise`, rather than already as `Nodup` of
the key map, so its intended proof can work directly with consecutive
matching edges and the unique cut in the ordered lineage payload.
-/
def UAdjacentCutInvariant {n : ℕ}
    (finalEvents : List (ValueChangeEvent n)) (threshold : ℕ)
    (snapshots : List (TimedAnnotatedPairShiftSnapshot n)) : Prop :=
  ∀ event : Fin finalEvents.length,
    (uIncidentTimedSnapshots finalEvents event
      (significantTimedSnapshots threshold snapshots)).Pairwise
        (fun first second => first.uRunKey ≠ second.uRunKey)

/--
The structural clock-order invariant implies the event-specific adjacent-cut
invariant consumed by the column count.
-/
theorem ClockCrossingRunKeysNodup.uAdjacentCutInvariant
    {n : ℕ} {finalEvents : List (ValueChangeEvent n)}
    {threshold : ℕ}
    {snapshots : List (TimedAnnotatedPairShiftSnapshot n)}
    (invariant : ClockCrossingRunKeysNodup snapshots) :
    UAdjacentCutInvariant finalEvents threshold snapshots := by
  intro event
  have sublist :=
    uIncident_significant_sublist_clockCrossing
      finalEvents event threshold snapshots
  have mapped :=
    sublist.map TimedAnnotatedPairShiftSnapshot.uRunKey
  simpa only [List.nodup_iff_pairwise_ne, List.pairwise_map] using
    mapped.nodup (invariant event.val)

/--
The adjacent-cut formulation is exactly strong enough to supply the key
`Nodup` premise of `uIncident_length_le_of_runKeys_nodup`.
-/
theorem UAdjacentCutInvariant.runKeys_nodup
    {n : ℕ} {finalEvents : List (ValueChangeEvent n)}
    {threshold : ℕ}
    {snapshots : List (TimedAnnotatedPairShiftSnapshot n)}
    (cut : UAdjacentCutInvariant finalEvents threshold snapshots)
    (event : Fin finalEvents.length) :
    ((uIncidentTimedSnapshots finalEvents event
        (significantTimedSnapshots threshold snapshots)).map fun timed =>
      (timed.annotated.sourceRoot,
        timed.annotated.sourcePassCount)).Nodup := by
  rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
  simpa only [TimedAnnotatedPairShiftSnapshot.uRunKey] using cut event

/--
Smallest event-state bridge needed for the `growingLimit` argument.

For a fixed value-change event, every root represented by an incident
creator interval must still be a growing root block at one common valid
state, and its creator must be the element changed by that event.  The
intended construction chooses the state immediately before the event:
`uTemporalCharge ≠ 0` places the event strictly between the two episode
starts, while the no-entry-after-convert phase invariant keeps the root
growing there.
-/
def UEventGrowingRoots {n : ℕ} (params : Parameters)
    (finalEvents : List (ValueChangeEvent n)) (threshold : ℕ)
    (snapshots : List (TimedAnnotatedPairShiftSnapshot n)) : Prop :=
  ∀ event : Fin finalEvents.length,
    ∃ state : State n,
      state.Valid params ∧
        ∀ timed ∈
            uIncidentTimedSnapshots finalEvents event
              (significantTimedSnapshots threshold snapshots),
          ∃ block,
            state.block? timed.annotated.sourceRoot = some block ∧
              block.mode = .growing ∧
              block.creator = (finalEvents.get event).element

/--
The common event-state witness and `GrowingIsLineageRoot` counting theorem
bound the number of represented roots by `growingLimit`.
-/
theorem UEventGrowingRoots.roots_card_le_growingLimit
    {n : ℕ} {params : Parameters}
    {finalEvents : List (ValueChangeEvent n)}
    {threshold : ℕ}
    {snapshots : List (TimedAnnotatedPairShiftSnapshot n)}
    (witness :
      UEventGrowingRoots params finalEvents threshold snapshots)
    (event : Fin finalEvents.length) :
    ((uIncidentTimedSnapshots finalEvents event
        (significantTimedSnapshots threshold snapshots)).map fun timed =>
      timed.annotated.sourceRoot).toFinset.card ≤
        params.growingLimit := by
  let incident :=
    uIncidentTimedSnapshots finalEvents event
      (significantTimedSnapshots threshold snapshots)
  let roots :=
    (incident.map fun timed =>
      timed.annotated.sourceRoot).toFinset
  obtain ⟨state, valid, root_spec⟩ := witness event
  have list_spec :
      ∀ root ∈ roots.toList,
        ∃ block,
          state.block? root = some block ∧
            block.mode = .growing ∧
            block.creator = (finalEvents.get event).element := by
    intro root root_mem
    have root_mem_finset : root ∈ roots := by
      simpa using root_mem
    have root_mem_list :
        root ∈
          incident.map fun timed =>
            timed.annotated.sourceRoot := by
      simpa [roots] using root_mem_finset
    obtain ⟨timed, timed_mem, root_eq⟩ :=
      List.mem_map.mp root_mem_list
    subst root
    exact root_spec timed timed_mem
  have bound :=
    state.roots_length_le_growingLimit valid
      (finalEvents.get event).element roots.toList
      roots.nodup_toList list_spec
  simpa [incident, roots] using bound

/--
The two isolated structural facts close the significant `u`-column count.
-/
theorem significant_uIncident_length_le
    {n : ℕ} {params : Parameters}
    (finalEvents : List (ValueChangeEvent n))
    (threshold : ℕ)
    (snapshots : List (TimedAnnotatedPairShiftSnapshot n))
    (cut : UAdjacentCutInvariant finalEvents threshold snapshots)
    (eventRoots :
      UEventGrowingRoots params finalEvents threshold snapshots)
    (event : Fin finalEvents.length) :
    (uIncidentTimedSnapshots finalEvents event
        (significantTimedSnapshots threshold snapshots)).length ≤
      params.growingLimit * threshold := by
  exact
    uIncident_length_le_of_runKeys_nodup
      finalEvents event snapshots
      (cut.runKeys_nodup event)
      (eventRoots.roots_card_le_growingLimit event)

/-- The corresponding signed column inequality used by temporal charging. -/
theorem significant_uColumn_le
    {n : ℕ} {params : Parameters}
    (finalEvents : List (ValueChangeEvent n))
    (threshold : ℕ)
    (snapshots : List (TimedAnnotatedPairShiftSnapshot n))
    (cut : UAdjacentCutInvariant finalEvents threshold snapshots)
    (eventRoots :
      UEventGrowingRoots params finalEvents threshold snapshots)
    (event : Fin finalEvents.length) :
    ((significantTimedSnapshots threshold snapshots).map fun timed =>
        |timed.uTemporalCharge finalEvents event|).sum ≤
      ((params.growingLimit * threshold : ℕ) : ℤ) := by
  rw [sum_abs_uTemporalCharge_eq_incident_length]
  exact_mod_cast
    significant_uIncident_length_le
      finalEvents threshold snapshots cut eventRoots event

/-- The exact `u` half of `SignificantColumnIncidenceHypothesis`. -/
def SignificantUColumnIncidenceHypothesis : Prop :=
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
      ∀ event : Fin finalEvents.length,
        ((significantTimedSnapshots
            (FiberProfile.insignificantThreshold params)
            timedSnapshots).map fun timed =>
          |timed.uTemporalCharge finalEvents event|).sum ≤
            ((params.growingLimit *
              FiberProfile.insignificantThreshold params : ℕ) : ℤ)

/--
History-uniform clock cuts plus the event-state growing-root bridge imply the
complete significant `u`-column hypothesis.
-/
theorem significantUColumnIncidence_of_structural
    (cuts :
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
          UAdjacentCutInvariant finalEvents
            (FiberProfile.insignificantThreshold params)
            timedSnapshots)
    (eventRoots :
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
          UEventGrowingRoots params finalEvents
            (FiberProfile.insignificantThreshold params)
            timedSnapshots) :
    SignificantUColumnIncidenceHypothesis := by
  intro n params initial final initialLabels finalLabels initialLedger
    finalLedger initialClock finalClock finalEvents operations
    timedSnapshots history event
  exact
    significant_uColumn_le finalEvents
      (FiberProfile.insignificantThreshold params)
      timedSnapshots (cuts history) (eventRoots history) event

end Splay.Interface
