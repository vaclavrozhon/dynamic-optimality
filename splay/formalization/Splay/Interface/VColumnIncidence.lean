import Splay.Interface.ShiftIncidence
import Splay.Interface.GlobalDecay
import Splay.Interface.GlobalDecay

namespace Splay.Interface

namespace LifetimeHistory

/--
For one fixed value-change event, chronological significant winner intervals
have pairwise distinct inherited source pass counters.

The key step is strictness across operation boundaries.  A selected head
snapshot increments the physical counter of its winner.  Its incident
interval puts the event cutoff after that winner's episode clock, so the
clocked pass-floor invariant forces every selected tail snapshot for the same
event to have a strictly larger counter.
-/
theorem TimedPairShiftHistory.vIncident_sourcePassCounts_nodup
    {n : ℕ} {params : Parameters}
    {initial final : State n}
    {initialLabels finalLabels : RootLabels}
    {initialLedger finalLedger : EpisodeLedger n}
    {initialClock finalClock : EpisodeClock n}
    {initialEvents finalEvents : List (ValueChangeEvent n)}
    {operations : List (Operation n)}
    {snapshots : List (TimedAnnotatedPairShiftSnapshot n)}
    (history :
      TimedPairShiftHistory params initial initialLabels initialLedger
        initialClock initialEvents operations snapshots
        final finalLabels finalLedger finalClock finalEvents)
    (threshold : ℕ) (event : Fin finalEvents.length) :
    ((vIncidentTimedSnapshots finalEvents event
        (significantTimedSnapshots threshold snapshots)).map fun timed =>
      timed.annotated.sourcePassCount).Nodup := by
  induction history with
  | nil valid clockSound =>
      simp [vIncidentTimedSnapshots, significantTimedSnapshots]
  | @cons before middle final beforeLabels finalLabels beforeLedger
      finalLedger beforeClock finalClock beforeEvents finalEvents
      operation operations tailSnapshots aligned exact clockSound head tail
      ih =>
      let headSnapshots :=
        operationTimedPairShiftSnapshots before middle beforeLabels
          beforeLedger beforeClock beforeEvents operation exact head aligned
      let headIncident :=
        vIncidentTimedSnapshots finalEvents event
          (significantTimedSnapshots threshold headSnapshots)
      let tailIncident :=
        vIncidentTimedSnapshots finalEvents event
          (significantTimedSnapshots threshold tailSnapshots)
      have headLength : headIncident.length ≤ 1 := by
        exact
          length_vIncident_significant_operationTimed_le_one
            threshold finalEvents event before middle beforeLabels
            beforeLedger beforeClock beforeEvents operation exact head aligned
      have headNodup :
          (headIncident.map fun timed =>
            timed.annotated.sourcePassCount).Nodup := by
        cases incidentEq : headIncident with
        | nil =>
            simp
        | cons first rest =>
            cases rest with
            | nil =>
                simp
            | cons second rest =>
                simp [incidentEq] at headLength
      have tailNodup :
          (tailIncident.map fun timed =>
            timed.annotated.sourcePassCount).Nodup := by
        simpa [tailIncident] using ih event
      have headTailDisjoint :
          List.Disjoint
            (headIncident.map fun timed =>
              timed.annotated.sourcePassCount)
            (tailIncident.map fun timed =>
              timed.annotated.sourcePassCount) := by
        rw [List.disjoint_left]
        intro count countHead countTail
        obtain ⟨headTimed, headMember, headCountEq⟩ :=
          List.mem_map.mp countHead
        obtain ⟨tailTimed, tailMember, tailCountEq⟩ :=
          List.mem_map.mp countTail
        have headRaw :
            headTimed ∈ headSnapshots := by
          exact
            (List.mem_filter.mp
              (List.mem_filter.mp headMember).1).1
        have tailRaw :
            tailTimed ∈ tailSnapshots := by
          exact
            (List.mem_filter.mp
              (List.mem_filter.mp tailMember).1).1
        have headWinner :=
          winner_eq_eventElement_of_mem_vIncidentTimedSnapshots headMember
        have tailWinner :=
          winner_eq_eventElement_of_mem_vIncidentTimedSnapshots tailMember
        have sameWinner :
            tailTimed.annotated.winner =
              headTimed.annotated.winner := by
          exact tailWinner.trans headWinner.symm
        have headInterval :=
          start_le_event_lt_end_of_mem_vIncidentTimedSnapshots headMember
        have tailInterval :=
          start_le_event_lt_end_of_mem_vIncidentTimedSnapshots tailMember
        have headEvents :=
          eventsBefore_eq_of_mem_operationTimedPairShiftSnapshots
            before middle beforeLabels beforeLedger beforeClock beforeEvents
            operation exact head aligned headRaw
        have cutoffLeBefore :
            event.val + 1 ≤ beforeEvents.length := by
          rw [headEvents] at headInterval
          omega
        have cutoffLeTail :
            event.val + 1 ≤
              (beforeEvents ++
                operationValueChangeEvents operation).length := by
          have beforeLeAppend :
              beforeEvents.length ≤
                (beforeEvents ++
                  operationValueChangeEvents operation).length := by
            simp
          exact cutoffLeBefore.trans beforeLeAppend
        have physicalFloor :
            PassFloorAt middle headTimed.annotated.winner
              (headTimed.annotated.sourcePassCount + 1) :=
          passFloorAt_winner_after_of_mem_operationTimedPairShiftSnapshots
            before middle beforeLabels beforeLedger beforeClock beforeEvents
            operation exact head aligned headRaw
        have clockedFloor :
            ClockedPassFloorAt middle
              (EpisodeClock.after beforeEvents.length beforeClock operation)
              (event.val + 1) headTimed.annotated.winner
              (headTimed.annotated.sourcePassCount + 1) := by
          intro _clockBeforeCutoff
          exact physicalFloor
        have tailStartsBefore :
            tailTimed.winnerStartEvent < event.val + 1 := by
          omega
        have strictFloor :
            headTimed.annotated.sourcePassCount + 1 ≤
              tailTimed.annotated.sourcePassCount :=
          tail.sourcePassCount_ge_of_clockedFloor
            cutoffLeTail clockedFloor tailTimed tailRaw sameWinner
            tailStartsBefore
        omega
      have selectedAppend :
          vIncidentTimedSnapshots finalEvents event
              (significantTimedSnapshots threshold
                (headSnapshots ++ tailSnapshots)) =
            headIncident ++ tailIncident := by
        simp [headIncident, tailIncident, vIncidentTimedSnapshots,
          significantTimedSnapshots]
      rw [selectedAppend, List.map_append]
      exact headNodup.append tailNodup headTailDisjoint

/-- Every significant winner column contains at most `threshold` snapshots. -/
theorem TimedPairShiftHistory.significant_vIncident_length_le
    {n : ℕ} {params : Parameters}
    {initial final : State n}
    {initialLabels finalLabels : RootLabels}
    {initialLedger finalLedger : EpisodeLedger n}
    {initialClock finalClock : EpisodeClock n}
    {initialEvents finalEvents : List (ValueChangeEvent n)}
    {operations : List (Operation n)}
    {snapshots : List (TimedAnnotatedPairShiftSnapshot n)}
    (history :
      TimedPairShiftHistory params initial initialLabels initialLedger
        initialClock initialEvents operations snapshots
        final finalLabels finalLedger finalClock finalEvents)
    (threshold : ℕ) (event : Fin finalEvents.length) :
    (vIncidentTimedSnapshots finalEvents event
        (significantTimedSnapshots threshold snapshots)).length ≤
      threshold := by
  exact
    vIncident_length_le_of_passCounts_nodup finalEvents event snapshots
      (history.vIncident_sourcePassCounts_nodup threshold event)

/-- The unconditional signed winner-column inequality for temporal charging. -/
theorem TimedPairShiftHistory.significant_vColumn_le
    {n : ℕ} {params : Parameters}
    {initial final : State n}
    {initialLabels finalLabels : RootLabels}
    {initialLedger finalLedger : EpisodeLedger n}
    {initialClock finalClock : EpisodeClock n}
    {initialEvents finalEvents : List (ValueChangeEvent n)}
    {operations : List (Operation n)}
    {snapshots : List (TimedAnnotatedPairShiftSnapshot n)}
    (history :
      TimedPairShiftHistory params initial initialLabels initialLedger
        initialClock initialEvents operations snapshots
        final finalLabels finalLedger finalClock finalEvents)
    (threshold : ℕ) (event : Fin finalEvents.length) :
    ((significantTimedSnapshots threshold snapshots).map fun timed =>
        |timed.vTemporalCharge finalEvents event|).sum ≤
      (threshold : ℤ) := by
  rw [sum_abs_vTemporalCharge_eq_incident_length]
  exact_mod_cast history.significant_vIncident_length_le threshold event

end LifetimeHistory

/-- The winner half of significant column incidence, now proved unconditionally. -/
def SignificantVColumnIncidenceHypothesis : Prop :=
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
          |timed.vTemporalCharge finalEvents event|).sum ≤
            (FiberProfile.insignificantThreshold params : ℤ)

/-- Every timed lifetime history satisfies the significant winner-column bound. -/
theorem significantVColumnIncidence :
    SignificantVColumnIncidenceHypothesis := by
  intro n params initial final initialLabels finalLabels initialLedger
    finalLedger initialClock finalClock finalEvents operations
    timedSnapshots history event
  exact
    history.significant_vColumn_le
      (FiberProfile.insignificantThreshold params) event

end Splay.Interface
