import Splay.Interface.UClockCutStateHistory

namespace Splay.Interface

/--
For a positive cutoff, timed straddling at the preceding event index is the
same endpoint cut used by the state invariant.
-/
theorem uClockStraddles_iff_clockStraddlesAt_succ
    {n : ℕ} (timed : TimedAnnotatedPairShiftSnapshot n)
    (clock : EpisodeClock n) (eventIndex : ℕ)
    (winnerClock :
      timed.winnerStartEvent = clock timed.annotated.winner)
    (loserClock :
      timed.loserStartEvent = clock timed.annotated.loser) :
    timed.UClockStraddlesAt eventIndex ↔
      ClockStraddlesAt clock (eventIndex + 1) timed.annotated.winner
        timed.annotated.loser := by
  unfold TimedAnnotatedPairShiftSnapshot.UClockStraddlesAt
    ClockStraddlesAt
  rw [winnerClock, loserClock]
  omega

/--
A structural clock crossing emitted by one pass is an actual adjacent crossing
in the physical source block, with exactly the annotated root and pass count.
-/
theorem cut_spec_of_mem_timedLifetimePassSnapshots
    {n : ℕ} {params : Parameters}
    {before after : State n} {labels : RootLabels}
    {ledger : EpisodeLedger n} {source : BlockId}
    {matching : List (Pairing n)}
    (clock : EpisodeClock n) (events : List (ValueChangeEvent n))
    (exact : EpisodeLedger.ExactAt before labels ledger)
    (step : Step params before (.pass source matching) after)
    (aligned : labels.length = before.blocks.length)
    {timed : TimedAnnotatedPairShiftSnapshot n}
    (member :
      timed ∈
        timedLifetimePassSnapshots clock events exact step aligned)
    {eventIndex : ℕ}
    (crossing : timed.UClockStraddlesAt eventIndex) :
    ∃ sourceBlock,
      before.block? source = some sourceBlock ∧
        RootLabels.root? labels source =
          some timed.annotated.sourceRoot ∧
        sourceBlock.passCount =
          timed.annotated.sourcePassCount ∧
        BlockClockMixedAt clock (eventIndex + 1) sourceBlock := by
  obtain ⟨attached, attachedMem, timedEq⟩ :=
    List.mem_map.mp member
  subst timed
  obtain
      ⟨sourceBlock, sourceFound, rootFound, countEq, creatorEq,
        sourceEq, winnerEq, loserEq⟩ :=
    AnnotatedPairShiftSnapshot.source_lookup_ofLifetimePass
      exact step aligned attached.2
  have pairingValid :
      PairingValid before source sourceBlock attached.1 := by
    obtain ⟨actualSource, actualFound, validMatching⟩ :
        ∃ actualSource,
          before.block? source = some actualSource ∧
            MatchingValid params before source actualSource matching := by
      cases step.2.1 with
      | pass found valid blocksEq valuesEq =>
          exact ⟨_, found, valid⟩
    rw [sourceFound] at actualFound
    have sourceBlockEq : sourceBlock = actualSource :=
      Option.some.inj actualFound
    subst actualSource
    exact validMatching.2.2.2.1 attached.1 attached.2
  have timedCrossing :
      ClockStraddlesAt clock (eventIndex + 1)
        (TimedAnnotatedPairShiftSnapshot.ofLifetimePass
          clock events exact step aligned attached.2).annotated.winner
        (TimedAnnotatedPairShiftSnapshot.ofLifetimePass
          clock events exact step aligned attached.2).annotated.loser := by
    apply
      (uClockStraddles_iff_clockStraddlesAt_succ
        (TimedAnnotatedPairShiftSnapshot.ofLifetimePass
          clock events exact step aligned attached.2)
        clock eventIndex rfl rfl).mp
    exact crossing
  refine
    ⟨sourceBlock, sourceFound, rootFound, countEq,
      ?_⟩
  refine ⟨attached.1.winner, attached.1.loser, ?_, ?_⟩
  · simpa [winnerEq, loserEq] using pairingValid.1
  · simpa [TimedAnnotatedPairShiftSnapshot.ofLifetimePass,
      AnnotatedPairShiftSnapshot.ofLifetimePass] using timedCrossing

/--
One legal pass contributes at most one snapshot to a fixed structural clock
crossing column whenever its source block is cut-ordered.
-/
theorem length_clockCrossing_timedLifetimePassSnapshots_le_one
    {n : ℕ} {params : Parameters}
    {before after : State n} {labels : RootLabels}
    {ledger : EpisodeLedger n} {source : BlockId}
    {matching : List (Pairing n)} {sourceBlock : Block n}
    (clock : EpisodeClock n) (events : List (ValueChangeEvent n))
    (exact : EpisodeLedger.ExactAt before labels ledger)
    (step : Step params before (.pass source matching) after)
    (aligned : labels.length = before.blocks.length)
    (sourceFound : before.block? source = some sourceBlock)
    (eventIndex : ℕ)
    (ordered :
      ClockCutOrderedAt clock (eventIndex + 1) sourceBlock.elements)
    :
    (clockCrossingTimedSnapshots eventIndex
        (timedLifetimePassSnapshots clock events exact step aligned)).length ≤
      1 := by
  obtain ⟨actualSource, actualFound, validMatching⟩ :
      ∃ actualSource,
        before.block? source = some actualSource ∧
          MatchingValid params before source actualSource matching := by
    cases step.2.1 with
    | pass found valid blocksEq valuesEq =>
        exact ⟨_, found, valid⟩
  rw [sourceFound] at actualFound
  have sourceEq : sourceBlock = actualSource :=
    Option.some.inj actualFound
  subst actualSource
  have matchingBound :=
    validMatching.length_clockStraddlingPairings_le_one
      clock (eventIndex + 1) ordered
  unfold clockCrossingTimedSnapshots timedLifetimePassSnapshots
  rw [List.filter_map, List.length_map]
  have predicateEq :
      (fun attached : { pairing // pairing ∈ matching } =>
          decide
            ((TimedAnnotatedPairShiftSnapshot.ofLifetimePass
              clock events exact step aligned attached.2).UClockStraddlesAt
                eventIndex)) =
        (fun attached : { pairing // pairing ∈ matching } =>
          decide
            (ClockStraddlesAt clock (eventIndex + 1)
              attached.1.winner attached.1.loser)) := by
    funext attached
    simp [TimedAnnotatedPairShiftSnapshot.ofLifetimePass,
      AnnotatedPairShiftSnapshot.ofLifetimePass,
      TimedAnnotatedPairShiftSnapshot.UClockStraddlesAt,
      ClockStraddlesAt]
    ac_rfl
  rw [show
    (List.filter
      ((fun timed =>
        decide (timed.UClockStraddlesAt eventIndex)) ∘
          fun attached =>
            TimedAnnotatedPairShiftSnapshot.ofLifetimePass
              clock events exact step aligned attached.2)
        matching.attach) =
      List.filter
        (fun attached : { pairing // pairing ∈ matching } =>
          decide
            (ClockStraddlesAt clock (eventIndex + 1)
              attached.1.winner attached.1.loser))
        matching.attach by
      rw [show
        ((fun timed =>
          decide (timed.UClockStraddlesAt eventIndex)) ∘
            fun attached =>
              TimedAnnotatedPairShiftSnapshot.ofLifetimePass
                clock events exact step aligned attached.2) =
          (fun attached : { pairing // pairing ∈ matching } =>
            decide
              ((TimedAnnotatedPairShiftSnapshot.ofLifetimePass
                clock events exact step aligned attached.2).UClockStraddlesAt
                  eventIndex)) by rfl,
        predicateEq]]
  let selected : Pairing n → Bool := fun pairing =>
    decide
      (ClockStraddlesAt clock (eventIndex + 1)
        pairing.winner pairing.loser)
  change
    (List.filter (fun attached => selected attached.1)
      matching.attach).length ≤ 1
  have attachEq := List.filter_attach matching selected
  have lengthEq := congrArg List.length attachEq
  simp only [List.length_map, List.length_attach] at lengthEq
  rw [lengthEq]
  simpa [clockStraddlingPairings, selected] using matchingBound

/--
At one history step, structural crossing keys are internally unique and fresh
with respect to every key already stored in the fixed-cut accumulator.

This is the exact pass-floor use: a crossing snapshot identifies the current
mixed source block, while `pastBelow` puts every old key of that root strictly
below its physical pre-pass counter.
-/
theorem operation_clockCrossing_keys_fresh
    {n : ℕ} {params : Parameters}
    (before after : State n) (labels : RootLabels)
    (ledger : EpisodeLedger n) (clock : EpisodeClock n)
    (events : List (ValueChangeEvent n)) (operation : Operation n)
    (exact : EpisodeLedger.ExactAt before labels ledger)
    (step : Step params before operation after)
    (aligned : labels.length = before.blocks.length)
    (eventIndex : ℕ) (past : List LineageRunKey)
    (accumulator :
      ClockCrossingAccumulatorAt before labels clock
        (eventIndex + 1) past) :
    let selected :=
      clockCrossingTimedSnapshots eventIndex
        (operationTimedPairShiftSnapshots before after labels ledger clock
          events operation exact step aligned)
    let keys :=
      selected.map TimedAnnotatedPairShiftSnapshot.uRunKey
    keys.Nodup ∧ List.Disjoint past keys := by
  cases operation with
  | convert blockId =>
      simp [operationTimedPairShiftSnapshots,
        clockCrossingTimedSnapshots]
  | create creator =>
      simp [operationTimedPairShiftSnapshots,
        clockCrossingTimedSnapshots]
  | insert blockId element =>
      simp [operationTimedPairShiftSnapshots,
        clockCrossingTimedSnapshots]
  | delete blockId element =>
      simp [operationTimedPairShiftSnapshots,
        clockCrossingTimedSnapshots]
  | @pass source matching =>
      obtain ⟨sourceBlock, sourceFound, validMatching⟩ :
          ∃ sourceBlock,
            before.block? source = some sourceBlock ∧
              MatchingValid params before source sourceBlock matching := by
        cases step.2.1 with
        | pass found valid blocksEq valuesEq =>
            exact ⟨_, found, valid⟩
      let selected :=
        clockCrossingTimedSnapshots eventIndex
          (timedLifetimePassSnapshots clock events exact step aligned)
      let keys :=
        selected.map TimedAnnotatedPairShiftSnapshot.uRunKey
      have selectedLength : selected.length ≤ 1 := by
        apply
          length_clockCrossing_timedLifetimePassSnapshots_le_one
            clock events exact step aligned sourceFound eventIndex
        exact accumulator.ordered source sourceBlock sourceFound
      have keysLength : keys.length ≤ 1 := by
        simpa [keys] using selectedLength
      have keysNodup : keys.Nodup := by
        generalize keysEq : keys = actualKeys at keysLength ⊢
        cases actualKeys with
        | nil =>
            simp
        | cons first rest =>
            cases rest with
            | nil =>
                simp
            | cons second rest =>
                simp at keysLength
      have fresh : List.Disjoint past keys := by
        rw [List.disjoint_left]
        intro key keyPast keyCurrent
        have keyCurrent' : key ∈ keys := keyCurrent
        obtain ⟨timed, timedMem, keyEq⟩ :=
          List.mem_map.mp (by simpa [keys] using keyCurrent')
        change
          timed ∈
            clockCrossingTimedSnapshots eventIndex
              (timedLifetimePassSnapshots
                clock events exact step aligned) at timedMem
        have timedInfo := List.mem_filter.mp timedMem
        have rawMember :
            timed ∈
              timedLifetimePassSnapshots clock events exact step aligned :=
          timedInfo.1
        have crossing :
            timed.UClockStraddlesAt eventIndex := by
          simpa [clockCrossingTimedSnapshots] using timedInfo.2
        obtain
            ⟨actualSource, actualFound, rootFound, countEq, mixed⟩ :=
          cut_spec_of_mem_timedLifetimePassSnapshots
            clock events exact step aligned rawMember crossing
        have rootEq :
            timed.annotated.sourceRoot = key.1 := by
          simpa [TimedAnnotatedPairShiftSnapshot.uRunKey] using
            congrArg Prod.fst keyEq
        have passCountEq :
            timed.annotated.sourcePassCount = key.2 := by
          simpa [TimedAnnotatedPairShiftSnapshot.uRunKey] using
            congrArg Prod.snd keyEq
        have oldBelow :=
          accumulator.pastBelow key keyPast source actualSource
            actualFound
            (by
              rw [← rootEq]
              exact rootFound)
            mixed
        omega
      simpa [operationTimedPairShiftSnapshots, selected, keys] using
        And.intro keysNodup fresh
  | split blockId prefixLength =>
      simp [operationTimedPairShiftSnapshots,
        clockCrossingTimedSnapshots]
  | valueChange element delta =>
      cases delta <;>
        simp [operationTimedPairShiftSnapshots,
          clockCrossingTimedSnapshots]

/--
Every structural crossing key emitted by one operation has a realized root
block that is shrinking after that operation.
-/
theorem operation_clockCrossing_key_root_shrinking_after
    {n : ℕ} {params : Parameters}
    (before after : State n) (labels : RootLabels)
    (ledger : EpisodeLedger n) (clock : EpisodeClock n)
    (events : List (ValueChangeEvent n)) (operation : Operation n)
    (exact : EpisodeLedger.ExactAt before labels ledger)
    (step : Step params before operation after)
    (aligned : labels.length = before.blocks.length)
    (phase : RootLineagePhase before labels)
    (eventIndex : ℕ)
    {key : LineageRunKey}
    (keyMember :
      key ∈
        (clockCrossingTimedSnapshots eventIndex
          (operationTimedPairShiftSnapshots before after labels ledger clock
            events operation exact step aligned)).map
              TimedAnnotatedPairShiftSnapshot.uRunKey) :
    ∃ rootBlock,
      after.block? key.1 = some rootBlock ∧
        rootBlock.mode = .shrinking := by
  cases operation with
  | convert blockId =>
      simp [operationTimedPairShiftSnapshots,
        clockCrossingTimedSnapshots] at keyMember
  | create creator =>
      simp [operationTimedPairShiftSnapshots,
        clockCrossingTimedSnapshots] at keyMember
  | insert blockId element =>
      simp [operationTimedPairShiftSnapshots,
        clockCrossingTimedSnapshots] at keyMember
  | delete blockId element =>
      simp [operationTimedPairShiftSnapshots,
        clockCrossingTimedSnapshots] at keyMember
  | @pass source matching =>
      obtain ⟨sourceBlock, sourceFound, validMatching⟩ :
          ∃ sourceBlock,
            before.block? source = some sourceBlock ∧
              MatchingValid params before source sourceBlock matching := by
        cases step.2.1 with
        | pass found valid blocksEq valuesEq =>
            exact ⟨_, found, valid⟩
      obtain ⟨timed, timedMember, keyEq⟩ :=
        List.mem_map.mp keyMember
      have timedInfo := List.mem_filter.mp timedMember
      have rawMember :
          timed ∈
            timedLifetimePassSnapshots clock events exact step aligned :=
        timedInfo.1
      have crossing :
          timed.UClockStraddlesAt eventIndex := by
        simpa [clockCrossingTimedSnapshots] using timedInfo.2
      obtain
          ⟨actualSource, actualFound, rootFound, countEq, mixed⟩ :=
        cut_spec_of_mem_timedLifetimePassSnapshots
          clock events exact step aligned rawMember crossing
      rw [sourceFound] at actualFound
      have actualEq : actualSource = sourceBlock :=
        Option.some.inj actualFound.symm
      subst actualSource
      obtain ⟨rootBlock, rootBlockFound⟩ :=
        phase.rootsRealized source timed.annotated.sourceRoot rootFound
      have rootShrinking : rootBlock.mode = .shrinking := by
        cases modeEq : rootBlock.mode with
        | growing =>
            have sourceEq :
                source = timed.annotated.sourceRoot :=
              phase.mixed_block_eq_root_of_growing
                rootBlockFound modeEq sourceFound rootFound mixed
            rw [sourceEq, rootBlockFound] at sourceFound
            have blockEq : sourceBlock = rootBlock :=
              Option.some.inj sourceFound.symm
            subst sourceBlock
            rw [validMatching.1] at modeEq
            contradiction
        | shrinking =>
            rfl
      obtain ⟨afterRoot, afterRootFound, afterRootShrinking⟩ :=
        RootLineagePhase.shrinking_block_after_step
          step rootBlockFound rootShrinking
      have rootEq :
          timed.annotated.sourceRoot = key.1 := by
        simpa [TimedAnnotatedPairShiftSnapshot.uRunKey] using
          congrArg Prod.fst keyEq
      rw [rootEq] at afterRootFound
      exact ⟨afterRoot, afterRootFound, afterRootShrinking⟩
  | split blockId prefixLength =>
      simp [operationTimedPairShiftSnapshots,
        clockCrossingTimedSnapshots] at keyMember
  | valueChange element delta =>
      cases delta <;>
        simp [operationTimedPairShiftSnapshots,
          clockCrossingTimedSnapshots] at keyMember

/--
Shrinking-root evidence for the accumulated key list is preserved and extended
by one operation.
-/
theorem crossingKeyRootsShrinking_after_operation
    {n : ℕ} {params : Parameters}
    (before after : State n) (labels : RootLabels)
    (ledger : EpisodeLedger n) (clock : EpisodeClock n)
    (events : List (ValueChangeEvent n)) (operation : Operation n)
    (exact : EpisodeLedger.ExactAt before labels ledger)
    (step : Step params before operation after)
    (aligned : labels.length = before.blocks.length)
    (phase : RootLineagePhase before labels)
    (eventIndex : ℕ) (past : List LineageRunKey)
    (old : CrossingKeyRootsShrinkingAt before past) :
    let operationKeys :=
      (clockCrossingTimedSnapshots eventIndex
        (operationTimedPairShiftSnapshots before after labels ledger clock
          events operation exact step aligned)).map
            TimedAnnotatedPairShiftSnapshot.uRunKey
    CrossingKeyRootsShrinkingAt after (past ++ operationKeys) := by
  dsimp only
  unfold CrossingKeyRootsShrinkingAt
  intro key keyMember
  rcases List.mem_append.mp keyMember with oldMember | newMember
  · obtain ⟨rootBlock, rootFound, rootShrinking⟩ :=
      old key oldMember
    exact
      RootLineagePhase.shrinking_block_after_step
        step rootFound rootShrinking
  · exact
      operation_clockCrossing_key_root_shrinking_after
        before after labels ledger clock events operation exact step aligned
        phase eventIndex newMember

/--
The state-only part of one fixed-cut update.  The chronological key-list
bookkeeping is deliberately omitted: it is derived by
`operation_clockCrossing_keys_fresh`.
-/
structure ClockCutStateStepResult {n : ℕ}
    (state : State n) (labels : RootLabels) (clock : EpisodeClock n)
    (cutoff : ℕ) (past : List LineageRunKey) : Prop where
  ordered : StateClockCutOrderedAt state clock cutoff
  unique : RootClockCutUniqueAt state labels clock cutoff
  pastBelow : CrossingKeyBelowCutAt state labels clock cutoff past

/-- The still-local root/pass-floor part of a one-step cut update. -/
structure ClockCutRootStepResult {n : ℕ}
    (state : State n) (labels : RootLabels) (clock : EpisodeClock n)
    (cutoff : ℕ) (past : List LineageRunKey) : Prop where
  unique : RootClockCutUniqueAt state labels clock cutoff
  pastBelow : CrossingKeyBelowCutAt state labels clock cutoff past

/-- Minimal remaining one-step model hypothesis after clock-order preservation. -/
def ClockCutRootStepHypothesis : Prop :=
  ∀ {n : ℕ} {params : Parameters}
    {before after : State n} {labels : RootLabels}
    {ledger : EpisodeLedger n} {clock : EpisodeClock n}
    {events : List (ValueChangeEvent n)} {operation : Operation n}
    (exact : EpisodeLedger.ExactAt before labels ledger)
    (clockSound : EpisodeClock.SoundAt before ledger clock events)
    (aligned : labels.length = before.blocks.length)
    (phase : RootLineagePhase before labels)
    (step : Step params before operation after)
    (eventIndex : ℕ) (past : List LineageRunKey)
    (accumulator :
      ClockCrossingAccumulatorAt before labels clock
        (eventIndex + 1) past),
    let operationSnapshots :=
      operationTimedPairShiftSnapshots before after labels ledger clock
        events operation exact step aligned
    let newKeys :=
      (clockCrossingTimedSnapshots eventIndex operationSnapshots).map
        TimedAnnotatedPairShiftSnapshot.uRunKey
    ClockCutRootStepResult after
      (RootLabels.after labels operation)
      (EpisodeClock.after events.length clock operation)
      (eventIndex + 1) (past ++ newKeys)

/--
The remaining model-local one-step preservation theorem, isolated with its
minimal exact signature.
-/
def ClockCutStateStepHypothesis : Prop :=
  ∀ {n : ℕ} {params : Parameters}
    {before after : State n} {labels : RootLabels}
    {ledger : EpisodeLedger n} {clock : EpisodeClock n}
    {events : List (ValueChangeEvent n)} {operation : Operation n}
    (exact : EpisodeLedger.ExactAt before labels ledger)
    (clockSound : EpisodeClock.SoundAt before ledger clock events)
    (aligned : labels.length = before.blocks.length)
    (phase : RootLineagePhase before labels)
    (step : Step params before operation after)
    (eventIndex : ℕ) (past : List LineageRunKey)
    (accumulator :
      ClockCrossingAccumulatorAt before labels clock
        (eventIndex + 1) past),
    let operationSnapshots :=
      operationTimedPairShiftSnapshots before after labels ledger clock
        events operation exact step aligned
    let newKeys :=
      (clockCrossingTimedSnapshots eventIndex operationSnapshots).map
        TimedAnnotatedPairShiftSnapshot.uRunKey
    ClockCutStateStepResult after
      (RootLabels.after labels operation)
      (EpisodeClock.after events.length clock operation)
      (eventIndex + 1) (past ++ newKeys)

/-- The proved clock-order theorem upgrades the minimal root result. -/
theorem clockCutStateStepHypothesis_of_root
    (rootStep : ClockCutRootStepHypothesis) :
    ClockCutStateStepHypothesis := by
  intro n params before after labels ledger clock events operation
    exact clockSound aligned phase step eventIndex past accumulator
  have rootResult :=
    rootStep exact clockSound aligned phase step
      eventIndex past accumulator
  exact
    { ordered :=
        accumulator.ordered.after_step exact clockSound step
      unique := rootResult.unique
      pastBelow := rootResult.pastBelow }

namespace ClockCrossingAccumulatorAt

/--
The state preservation result plus the proved one-pass freshness lemma rebuild
the complete accumulator after one exact operation.
-/
theorem after_step_of_state_result
    {n : ℕ} {params : Parameters}
    {before after : State n} {labels : RootLabels}
    {ledger : EpisodeLedger n} {clock : EpisodeClock n}
    {events : List (ValueChangeEvent n)} {operation : Operation n}
    (exact : EpisodeLedger.ExactAt before labels ledger)
    (aligned : labels.length = before.blocks.length)
    (step : Step params before operation after)
    (phase : RootLineagePhase before labels)
    (eventIndex : ℕ) (past : List LineageRunKey)
    (accumulator :
      ClockCrossingAccumulatorAt before labels clock
        (eventIndex + 1) past)
    (stateResult :
      let operationSnapshots :=
        operationTimedPairShiftSnapshots before after labels ledger clock
          events operation exact step aligned
      let newKeys :=
        (clockCrossingTimedSnapshots eventIndex operationSnapshots).map
          TimedAnnotatedPairShiftSnapshot.uRunKey
      ClockCutStateStepResult after
        (RootLabels.after labels operation)
        (EpisodeClock.after events.length clock operation)
        (eventIndex + 1) (past ++ newKeys)) :
    let operationSnapshots :=
      operationTimedPairShiftSnapshots before after labels ledger clock
        events operation exact step aligned
    let newKeys :=
      (clockCrossingTimedSnapshots eventIndex operationSnapshots).map
        TimedAnnotatedPairShiftSnapshot.uRunKey
    ClockCrossingAccumulatorAt after
      (RootLabels.after labels operation)
      (EpisodeClock.after events.length clock operation)
      (eventIndex + 1) (past ++ newKeys) := by
  let operationSnapshots :=
    operationTimedPairShiftSnapshots before after labels ledger clock
      events operation exact step aligned
  let newKeys :=
    (clockCrossingTimedSnapshots eventIndex operationSnapshots).map
      TimedAnnotatedPairShiftSnapshot.uRunKey
  have fresh :=
    operation_clockCrossing_keys_fresh
      before after labels ledger clock events operation exact step aligned
      eventIndex past accumulator
  exact
    { ordered := stateResult.ordered
      unique := stateResult.unique
      keysNodup :=
        accumulator.keysNodup.append fresh.1 fresh.2
      pastBelow := stateResult.pastBelow
      pastRootsShrinking :=
        crossingKeyRootsShrinking_after_operation
          before after labels ledger clock events operation exact step aligned
          phase eventIndex past accumulator.pastRootsShrinking }

end ClockCrossingAccumulatorAt

namespace LifetimeHistory

/--
The isolated one-step state theorem telescopes to distinct structural crossing
keys over an entire timed history.
-/
theorem TimedPairShiftHistory.clockCrossingAccumulator
    (stepInvariant : ClockCutStateStepHypothesis)
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
    (eventIndex : ℕ) (past : List LineageRunKey)
    (phase : RootLineagePhase initial initialLabels)
    (accumulator :
      ClockCrossingAccumulatorAt initial initialLabels initialClock
        (eventIndex + 1) past) :
    ClockCrossingAccumulatorAt final finalLabels finalClock
      (eventIndex + 1)
      (past ++
        (clockCrossingTimedSnapshots eventIndex snapshots).map
          TimedAnnotatedPairShiftSnapshot.uRunKey) := by
  induction history generalizing past with
  | nil valid clockSound =>
      simpa [clockCrossingTimedSnapshots] using accumulator
  | @cons before middle final beforeLabels finalLabels beforeLedger
      finalLedger beforeClock finalClock beforeEvents finalEvents
      operation operations tailSnapshots aligned exact clockSound head tail
      ih =>
      let operationSnapshots :=
        operationTimedPairShiftSnapshots before middle beforeLabels
          beforeLedger beforeClock beforeEvents operation exact head aligned
      let headKeys :=
        (clockCrossingTimedSnapshots eventIndex operationSnapshots).map
          TimedAnnotatedPairShiftSnapshot.uRunKey
      have stateResult :=
        stepInvariant exact clockSound aligned phase head
          eventIndex past accumulator
      have nextAccumulator :
          ClockCrossingAccumulatorAt middle
            (RootLabels.after beforeLabels operation)
            (EpisodeClock.after beforeEvents.length beforeClock operation)
            (eventIndex + 1) (past ++ headKeys) := by
        exact
          accumulator.after_step_of_state_result
            exact aligned head phase eventIndex past stateResult
      have nextPhase :
          RootLineagePhase middle
            (RootLabels.after beforeLabels operation) :=
        phase.after_step aligned head
      have tailAccumulator :=
        ih (past ++ headKeys) nextPhase nextAccumulator
      simpa [operationSnapshots, headKeys,
        clockCrossingTimedSnapshots, List.filter_append,
        List.map_append, List.append_assoc] using tailAccumulator

/--
For the concrete empty-block start used by the activity theorem, the one-step
state invariant implies distinct structural crossing keys at every event cut.
-/
theorem TimedPairShiftHistory.clockCrossingRunKeysNodup_of_initial
    (stepInvariant : ClockCutStateStepHypothesis)
    {n : ℕ} {params : Parameters}
    {initial final : State n} {finalLabels : RootLabels}
    {finalLedger : EpisodeLedger n}
    {initialClock finalClock : EpisodeClock n}
    {initialEvents finalEvents : List (ValueChangeEvent n)}
    {operations : List (Operation n)}
    {snapshots : List (TimedAnnotatedPairShiftSnapshot n)}
    (initialState : initial.Initial params)
    (history :
      TimedPairShiftHistory params initial []
        (EpisodeLedger.empty : EpisodeLedger n)
        initialClock initialEvents operations snapshots
        final finalLabels finalLedger finalClock finalEvents) :
    ClockCrossingRunKeysNodup snapshots := by
  intro eventIndex
  have initialPhase : RootLineagePhase initial [] :=
    RootLineagePhase.initial initialState
  have initialAccumulator :
      ClockCrossingAccumulatorAt initial [] initialClock
        (eventIndex + 1) [] :=
    ClockCrossingAccumulatorAt.initial
      initial initialClock (eventIndex + 1) initialState.2
  have finalAccumulator :=
    history.clockCrossingAccumulator stepInvariant eventIndex []
      initialPhase initialAccumulator
  simpa using finalAccumulator.keysNodup

/-- The completed adjacent-cut consequence for concrete initial histories. -/
theorem TimedPairShiftHistory.uAdjacentCutInvariant_of_initial
    (stepInvariant : ClockCutStateStepHypothesis)
    {n : ℕ} {params : Parameters}
    {initial final : State n} {finalLabels : RootLabels}
    {finalLedger : EpisodeLedger n}
    {initialClock finalClock : EpisodeClock n}
    {initialEvents finalEvents : List (ValueChangeEvent n)}
    {operations : List (Operation n)}
    {snapshots : List (TimedAnnotatedPairShiftSnapshot n)}
    (initialState : initial.Initial params)
    (history :
      TimedPairShiftHistory params initial []
        (EpisodeLedger.empty : EpisodeLedger n)
        initialClock initialEvents operations snapshots
        final finalLabels finalLedger finalClock finalEvents)
    (threshold : ℕ) :
    UAdjacentCutInvariant finalEvents threshold snapshots :=
  (history.clockCrossingRunKeysNodup_of_initial
    stepInvariant initialState).uAdjacentCutInvariant

end LifetimeHistory

end Splay.Interface
