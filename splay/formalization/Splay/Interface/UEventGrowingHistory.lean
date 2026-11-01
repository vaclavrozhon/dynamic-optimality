import Splay.Interface.UColumnIncidence
import Splay.Interface.RootLineagePhase

namespace Splay.Interface

/--
Complete active-episode facts exposed by a timed snapshot of one operation.
-/
theorem episode_facts_of_mem_operationTimedPairShiftSnapshots
    {n : ℕ} {params : Parameters}
    (before after : State n) (labels : RootLabels)
    (ledger : EpisodeLedger n) (clock : EpisodeClock n)
    (events : List (ValueChangeEvent n)) (operation : Operation n)
    (exact : EpisodeLedger.ExactAt before labels ledger)
    (step : Step params before operation after)
    (aligned : labels.length = before.blocks.length)
    {timed : TimedAnnotatedPairShiftSnapshot n}
    (member :
      timed ∈
        operationTimedPairShiftSnapshots before after labels ledger clock
          events operation exact step aligned) :
    ledger timed.annotated.winner =
        some timed.annotated.winnerStart ∧
      ledger timed.annotated.loser =
        some timed.annotated.loserStart ∧
      clock timed.annotated.winner = timed.winnerStartEvent ∧
      clock timed.annotated.loser = timed.loserStartEvent ∧
      timed.annotated.winnerStart.join.destinationRoot =
        timed.annotated.sourceRoot ∧
      timed.annotated.loserStart.join.destinationRoot =
        timed.annotated.sourceRoot ∧
      timed.annotated.winnerStart.join.destinationCreator =
        timed.annotated.sourceCreator ∧
      timed.annotated.loserStart.join.destinationCreator =
        timed.annotated.sourceCreator := by
  cases operation with
  | convert blockId =>
      simp [operationTimedPairShiftSnapshots] at member
  | create creator =>
      simp [operationTimedPairShiftSnapshots] at member
  | insert blockId element =>
      simp [operationTimedPairShiftSnapshots] at member
  | delete blockId element =>
      simp [operationTimedPairShiftSnapshots] at member
  | @pass source matching =>
      obtain ⟨attached, _attachedMem, timedEq⟩ :=
        List.mem_map.mp member
      subst timed
      have facts :=
        AnnotatedPairShiftSnapshot.episode_facts_ofLifetimePass
          exact step aligned attached.2
      rcases facts with
        ⟨winnerActive, loserActive, winnerRoot, loserRoot,
          winnerCreator, loserCreator⟩
      let annotated :=
        AnnotatedPairShiftSnapshot.ofLifetimePass
          exact step aligned attached.2
      have combined :
          ledger attached.1.winner = some annotated.winnerStart ∧
            ledger attached.1.loser = some annotated.loserStart ∧
            clock attached.1.winner = clock attached.1.winner ∧
            clock attached.1.loser = clock attached.1.loser ∧
            annotated.winnerStart.join.destinationRoot =
              annotated.sourceRoot ∧
            annotated.loserStart.join.destinationRoot =
              annotated.sourceRoot ∧
            annotated.winnerStart.join.destinationCreator =
              annotated.sourceCreator ∧
            annotated.loserStart.join.destinationCreator =
              annotated.sourceCreator :=
        ⟨winnerActive, loserActive, rfl, rfl, winnerRoot, loserRoot,
          winnerCreator, loserCreator⟩
      simpa [annotated,
        TimedAnnotatedPairShiftSnapshot.ofLifetimePass,
        AnnotatedPairShiftSnapshot.ofLifetimePass] using combined
  | split blockId prefixLength =>
      simp [operationTimedPairShiftSnapshots] at member
  | valueChange element delta =>
      cases delta <;>
        simp [operationTimedPairShiftSnapshots] at member

/--
An active episode whose post-step clock is strictly older than the current
event prefix was not opened by that step.
-/
theorem old_episode_of_after_clock_lt
    {n : ℕ} {params : Parameters}
    {before after : State n} {labels : RootLabels}
    {ledger : EpisodeLedger n} {clock : EpisodeClock n}
    {events : List (ValueChangeEvent n)} {operation : Operation n}
    {element : Element n} {start : EpisodeStart n} {cutoff : ℕ}
    (cutoffLe : cutoff ≤ events.length)
    (step : Step params before operation after)
    (activeAfter :
      EpisodeLedger.after before labels ledger operation element =
        some start)
    (clockAfterLt :
      EpisodeClock.after events.length clock operation element < cutoff) :
    ledger element = some start ∧
      clock element =
        EpisodeClock.after events.length clock operation element := by
  cases operation with
  | convert blockId =>
      constructor
      · simpa using activeAfter
      · rfl
  | create creator =>
      constructor
      · simpa using activeAfter
      · rfl
  | insert destination inserted =>
      by_cases same : element = inserted
      · subst element
        simp [EpisodeClock.after] at clockAfterLt
        omega
      · constructor
        · simpa [EpisodeLedger.after, same] using activeAfter
        · simp [EpisodeClock.after, Function.update, same]
  | delete source deleted =>
      by_cases same : element = deleted
      · subst element
        simp [EpisodeLedger.after] at activeAfter
      · constructor
        · simpa [EpisodeLedger.after, same] using activeAfter
        · rfl
  | pass source matching =>
      obtain ⟨sourceBlock, sourceFound, validMatching⟩ :
          ∃ sourceBlock,
            before.block? source = some sourceBlock ∧
              MatchingValid params before source sourceBlock matching := by
        cases step.2.1 with
        | pass found validMatching blocksEq valuesEq =>
            exact ⟨_, found, validMatching⟩
      have losersNodup : (pairingLosers matching).Nodup :=
        pairingLosers_nodup validMatching.2.1
      by_cases loser : element ∈ pairingLosers matching
      · obtain ⟨pairing, pairingMem, loserEq⟩ :=
          List.mem_map.mp (by simpa [pairingLosers] using loser)
        have installed :=
          EpisodeClock.installPassStarts_apply_of_mem
            events.length clock losersNodup pairingMem
        rw [loserEq] at installed
        change
          EpisodeClock.installPassStarts events.length clock matching
              element <
            cutoff at clockAfterLt
        rw [installed] at clockAfterLt
        omega
      · constructor
        · change
            EpisodeLedger.installPassJoins before labels source ledger
                matching element =
              some start at activeAfter
          rw [EpisodeLedger.installPassJoins_apply_of_not_mem
            before labels source ledger matching element loser] at activeAfter
          exact activeAfter
        · change
            clock element =
              EpisodeClock.installPassStarts events.length clock matching
                element
          rw [EpisodeClock.installPassStarts_apply_of_not_mem
            events.length clock matching element loser]
  | split source prefixLength =>
      constructor
      · simpa using activeAfter
      · rfl
  | valueChange changed delta =>
      constructor
      · simpa using activeAfter
      · rfl

/-- A snapshot ending no later than the event cannot be incident to it. -/
theorem uIncident_operation_eq_nil_of_eventsBefore_le
    {n : ℕ} {params : Parameters}
    (finalEvents : List (ValueChangeEvent n))
    (event : Fin finalEvents.length)
    (before after : State n) (labels : RootLabels)
    (ledger : EpisodeLedger n) (clock : EpisodeClock n)
    (events : List (ValueChangeEvent n)) (operation : Operation n)
    (exact : EpisodeLedger.ExactAt before labels ledger)
    (step : Step params before operation after)
    (aligned : labels.length = before.blocks.length)
    (past : events.length ≤ event.val) :
    uIncidentTimedSnapshots finalEvents event
        (operationTimedPairShiftSnapshots before after labels ledger clock
          events operation exact step aligned) = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro timed member
  have eventsEq :=
    eventsBefore_eq_of_mem_operationTimedPairShiftSnapshots
      before after labels ledger clock events operation exact step aligned
        member
  have notBefore : ¬event.val < timed.eventsBefore.length := by
    rw [eventsEq]
    omega
  simp [uIncidentTimedSnapshots,
    TimedAnnotatedPairShiftSnapshot.uTemporalCharge,
    eventIntervalCharge, notBefore]

/-- All active episodes of one root were opened before a fixed event cut. -/
def RootActiveClocksBefore {n : ℕ}
    (ledger : EpisodeLedger n) (clock : EpisodeClock n)
    (root : RootId) (cutoff : ℕ) : Prop :=
  ∀ element start,
    ledger element = some start →
      start.join.destinationRoot = root →
        clock element < cutoff

/-- Every currently active episode predates the same cut. -/
def AllActiveClocksBefore {n : ℕ}
    (ledger : EpisodeLedger n) (clock : EpisodeClock n)
    (cutoff : ℕ) : Prop :=
  ∀ element start,
    ledger element = some start →
      clock element < cutoff

/--
If a lineage contains no growing block, no operation can open a new episode
in that lineage; hence its active clocks stay before the same cut.
-/
theorem RootActiveClocksBefore.after_step_of_noGrowing
    {n : ℕ} {params : Parameters}
    {before after : State n} {labels : RootLabels}
    {ledger : EpisodeLedger n} {clock : EpisodeClock n}
    {events : List (ValueChangeEvent n)} {operation : Operation n}
    {root : RootId} {cutoff : ℕ}
    (bounded : RootActiveClocksBefore ledger clock root cutoff)
    (growingIsRoot : GrowingIsLineageRoot before labels)
    (noGrowing : NoGrowingInLineage before labels root)
    (step : Step params before operation after) :
    RootActiveClocksBefore
      (EpisodeLedger.after before labels ledger operation)
      (EpisodeClock.after events.length clock operation)
      root cutoff := by
  intro element start activeAfter startRoot
  cases operation with
  | convert blockId =>
      exact bounded element start (by simpa using activeAfter) startRoot
  | create creator =>
      exact bounded element start (by simpa using activeAfter) startRoot
  | insert destination inserted =>
      by_cases same : element = inserted
      · subst element
        let joined :=
          makeJoinOccurrence before labels .insert inserted
            destination inserted
        have joinedMem :
            joined ∈
              operationJoinOccurrences before labels
                (.insert destination inserted) := by
          simp [joined]
        have installed :=
          EpisodeLedger.after_apply_eq_some_of_join
            step ledger joinedMem
        change
          EpisodeLedger.after before labels ledger
              (.insert destination inserted) inserted =
            some (EpisodeStart.ofJoin before joined) at installed
        rw [installed] at activeAfter
        have startEq :
            EpisodeStart.ofJoin before joined = start :=
          Option.some.inj activeAfter
        cases step.2.1 with
        | insert destinationFound destinationGrowing unassigned valueOrder
            blocksEq valuesEq =>
            rename_i destinationBlock
            have destinationSelf :=
              growingIsRoot destination destinationBlock
                destinationFound destinationGrowing
            have joinedRoot :
                (EpisodeStart.ofJoin before joined).join.destinationRoot =
                  destination := by
              simp [EpisodeStart.ofJoin, joined, makeJoinOccurrence,
                destinationFound, destinationSelf]
            have destinationEq : destination = root := by
              rw [startEq, startRoot] at joinedRoot
              exact joinedRoot.symm
            have destinationLabel :
                RootLabels.root? labels destination = some root := by
              simpa [destinationEq] using destinationSelf
            exact
              False.elim
                ((noGrowing destination destinationBlock destinationFound
                    destinationLabel) destinationGrowing)
      · have activeBefore : ledger element = some start := by
          simpa [EpisodeLedger.after, same] using activeAfter
        simpa [EpisodeClock.after, Function.update, same] using
          bounded element start activeBefore startRoot
  | delete source deleted =>
      by_cases same : element = deleted
      · subst element
        simp [EpisodeLedger.after] at activeAfter
      · have activeBefore : ledger element = some start := by
          simpa [EpisodeLedger.after, same] using activeAfter
        exact bounded element start activeBefore startRoot
  | pass source matching =>
      obtain ⟨sourceBlock, sourceFound, validMatching⟩ :
          ∃ sourceBlock,
            before.block? source = some sourceBlock ∧
              MatchingValid params before source sourceBlock matching := by
        cases step.2.1 with
        | pass found validMatching blocksEq valuesEq =>
            exact ⟨_, found, validMatching⟩
      by_cases loser : element ∈ pairingLosers matching
      · obtain ⟨pairing, pairingMem, loserEq⟩ :=
          List.mem_map.mp (by simpa [pairingLosers] using loser)
        let joined :=
          makeJoinOccurrence before labels
            (.pass source pairing.winner) pairing.loser
            pairing.destination pairing.winner
        have joinedMem :
            joined ∈
              operationJoinOccurrences before labels
                (.pass source matching) := by
          apply List.mem_map.mpr
          exact ⟨pairing, pairingMem, rfl⟩
        have installed :=
          EpisodeLedger.after_apply_eq_some_of_join
            step ledger joinedMem
        have installedAtElement :
            EpisodeLedger.after before labels ledger
                (.pass source matching) element =
              some (EpisodeStart.ofJoin before joined) := by
          simpa [joined, makeJoinOccurrence, loserEq] using installed
        rw [installedAtElement] at activeAfter
        have startEq :
            EpisodeStart.ofJoin before joined = start :=
          Option.some.inj activeAfter
        obtain ⟨destinationBlock, destinationFound,
            destinationGrowing, _creatorEq⟩ :=
          (validMatching.2.2.2.1 pairing pairingMem).2.2.2
        have destinationSelf :=
          growingIsRoot pairing.destination destinationBlock
            destinationFound destinationGrowing
        have joinedRoot :
            (EpisodeStart.ofJoin before joined).join.destinationRoot =
              pairing.destination := by
          simp [EpisodeStart.ofJoin, joined, makeJoinOccurrence,
            destinationFound, destinationSelf]
        have destinationEq : pairing.destination = root := by
          rw [startEq, startRoot] at joinedRoot
          exact joinedRoot.symm
        have destinationLabel :
            RootLabels.root? labels pairing.destination = some root := by
          simpa [destinationEq] using destinationSelf
        exact
          False.elim
            ((noGrowing pairing.destination destinationBlock
                destinationFound destinationLabel) destinationGrowing)
      · have activeBefore : ledger element = some start := by
          change
            EpisodeLedger.installPassJoins before labels source ledger
                matching element =
              some start at activeAfter
          rw [EpisodeLedger.installPassJoins_apply_of_not_mem
            before labels source ledger matching element loser] at activeAfter
          exact activeAfter
        have clockEq :
            EpisodeClock.installPassStarts events.length clock matching
                element =
              clock element :=
          EpisodeClock.installPassStarts_apply_of_not_mem
            events.length clock matching element loser
        change
          EpisodeClock.installPassStarts events.length clock matching
              element <
            cutoff
        rw [clockEq]
        exact bounded element start activeBefore startRoot
  | split source prefixLength =>
      exact bounded element start (by simpa using activeAfter) startRoot
  | valueChange changed delta =>
      exact bounded element start (by simpa using activeAfter) startRoot

namespace LifetimeHistory

/-- A timed history starts in a valid state. -/
theorem TimedPairShiftHistory.initialValid
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
        final finalLabels finalLedger finalClock finalEvents) :
    initial.Valid params := by
  cases history with
  | nil valid clockSound =>
      exact valid
  | cons aligned exact clockSound head tail =>
      exact head.1

/-- Every history snapshot retains the two common root/creator annotations. -/
theorem TimedPairShiftHistory.snapshot_episode_facts
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
        final finalLabels finalLedger finalClock finalEvents) :
    ∀ timed ∈ snapshots,
      timed.annotated.winnerStart.join.destinationRoot =
          timed.annotated.sourceRoot ∧
        timed.annotated.loserStart.join.destinationRoot =
          timed.annotated.sourceRoot ∧
        timed.annotated.winnerStart.join.destinationCreator =
          timed.annotated.sourceCreator ∧
        timed.annotated.loserStart.join.destinationCreator =
          timed.annotated.sourceCreator := by
  induction history with
  | nil valid clockSound =>
      simp
  | @cons before middle final beforeLabels finalLabels beforeLedger
      finalLedger beforeClock finalClock beforeEvents finalEvents
      operation operations tailSnapshots aligned exact clockSound head tail
      ih =>
      intro timed member
      rcases List.mem_append.mp member with headMember | tailMember
      · have facts :=
          episode_facts_of_mem_operationTimedPairShiftSnapshots
            before middle beforeLabels beforeLedger beforeClock beforeEvents
            operation exact head aligned headMember
        exact
          ⟨facts.2.2.2.2.1, facts.2.2.2.2.2.1,
            facts.2.2.2.2.2.2.1, facts.2.2.2.2.2.2.2⟩
      · exact ih timed tailMember

/-- A sufficiently old winner episode was already active at history start. -/
theorem TimedPairShiftHistory.winner_old_at_initial
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
    {cutoff : ℕ} (cutoffLe : cutoff ≤ initialEvents.length)
    {timed : TimedAnnotatedPairShiftSnapshot n}
    (member : timed ∈ snapshots)
    (old : timed.winnerStartEvent < cutoff) :
    initialLedger timed.annotated.winner =
        some timed.annotated.winnerStart ∧
      initialClock timed.annotated.winner =
        timed.winnerStartEvent := by
  induction history generalizing cutoff with
  | nil valid clockSound =>
      simp at member
  | @cons before middle final beforeLabels finalLabels beforeLedger
      finalLedger beforeClock finalClock beforeEvents finalEvents
      operation operations tailSnapshots aligned exact clockSound head tail
      ih =>
      rcases List.mem_append.mp member with headMember | tailMember
      · have facts :=
          episode_facts_of_mem_operationTimedPairShiftSnapshots
            before middle beforeLabels beforeLedger beforeClock beforeEvents
            operation exact head aligned headMember
        exact ⟨facts.1, facts.2.2.1⟩
      · have nextCutoffLe :
            cutoff ≤
              (beforeEvents ++
                operationValueChangeEvents operation).length := by
          rw [List.length_append]
          exact cutoffLe.trans
            (Nat.le_add_right beforeEvents.length
              (operationValueChangeEvents operation).length)
        have tailOld :=
          ih nextCutoffLe tailMember old
        have afterClockLt :
            EpisodeClock.after beforeEvents.length beforeClock operation
                timed.annotated.winner <
              cutoff := by
          rw [tailOld.2]
          exact old
        have previous :=
          old_episode_of_after_clock_lt cutoffLe head tailOld.1
            afterClockLt
        exact ⟨previous.1, previous.2.trans tailOld.2⟩

/-- A sufficiently old loser episode was already active at history start. -/
theorem TimedPairShiftHistory.loser_old_at_initial
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
    {cutoff : ℕ} (cutoffLe : cutoff ≤ initialEvents.length)
    {timed : TimedAnnotatedPairShiftSnapshot n}
    (member : timed ∈ snapshots)
    (old : timed.loserStartEvent < cutoff) :
    initialLedger timed.annotated.loser =
        some timed.annotated.loserStart ∧
      initialClock timed.annotated.loser =
        timed.loserStartEvent := by
  induction history generalizing cutoff with
  | nil valid clockSound =>
      simp at member
  | @cons before middle final beforeLabels finalLabels beforeLedger
      finalLedger beforeClock finalClock beforeEvents finalEvents
      operation operations tailSnapshots aligned exact clockSound head tail
      ih =>
      rcases List.mem_append.mp member with headMember | tailMember
      · have facts :=
          episode_facts_of_mem_operationTimedPairShiftSnapshots
            before middle beforeLabels beforeLedger beforeClock beforeEvents
            operation exact head aligned headMember
        exact ⟨facts.2.1, facts.2.2.2.1⟩
      · have nextCutoffLe :
            cutoff ≤
              (beforeEvents ++
                operationValueChangeEvents operation).length := by
          rw [List.length_append]
          exact cutoffLe.trans
            (Nat.le_add_right beforeEvents.length
              (operationValueChangeEvents operation).length)
        have tailOld :=
          ih nextCutoffLe tailMember old
        have afterClockLt :
            EpisodeClock.after beforeEvents.length beforeClock operation
                timed.annotated.loser <
              cutoff := by
          rw [tailOld.2]
          exact old
        have previous :=
          old_episode_of_after_clock_lt cutoffLe head tailOld.1
            afterClockLt
        exact ⟨previous.1, previous.2.trans tailOld.2⟩

/--
Once a root block is shrinking, every later episode still active in that
lineage retains a pre-cut clock.
-/
theorem TimedPairShiftHistory.snapshot_clocks_lt_of_root_shrinking
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
    (phase : RootLineagePhase initial initialLabels)
    {root : RootId} {rootBlock : Block n}
    (rootFound : initial.block? root = some rootBlock)
    (rootShrinking : rootBlock.mode = .shrinking)
    {cutoff : ℕ}
    (bounded :
      RootActiveClocksBefore initialLedger initialClock root cutoff) :
    ∀ timed ∈ snapshots,
      timed.annotated.sourceRoot = root →
        timed.winnerStartEvent < cutoff ∧
          timed.loserStartEvent < cutoff := by
  induction history generalizing rootBlock with
  | nil valid clockSound =>
      simp
  | @cons before middle final beforeLabels finalLabels beforeLedger
      finalLedger beforeClock finalClock beforeEvents finalEvents
      operation operations tailSnapshots aligned exact clockSound head tail
      ih =>
      intro timed member sourceRoot
      rcases List.mem_append.mp member with headMember | tailMember
      · have facts :=
          episode_facts_of_mem_operationTimedPairShiftSnapshots
            before middle beforeLabels beforeLedger beforeClock beforeEvents
            operation exact head aligned headMember
        have winnerRoot :
            timed.annotated.winnerStart.join.destinationRoot = root :=
          facts.2.2.2.2.1.trans sourceRoot
        have loserRoot :
            timed.annotated.loserStart.join.destinationRoot = root :=
          facts.2.2.2.2.2.1.trans sourceRoot
        constructor
        · rw [← facts.2.2.1]
          exact
            bounded timed.annotated.winner timed.annotated.winnerStart
              facts.1 winnerRoot
        · rw [← facts.2.2.2.1]
          exact
            bounded timed.annotated.loser timed.annotated.loserStart
              facts.2.1 loserRoot
      · have noGrowing :
            NoGrowingInLineage before beforeLabels root :=
          phase.growingIsRoot.noGrowingInLineage_of_root_shrinking
            rootFound rootShrinking
        have nextBounded :=
          bounded.after_step_of_noGrowing
            (events := beforeEvents)
            phase.growingIsRoot noGrowing head
        obtain ⟨nextRootBlock, nextRootFound, nextRootShrinking⟩ :=
          RootLineagePhase.shrinking_block_after_step
            head rootFound rootShrinking
        exact
          ih (phase.after_step aligned head)
            nextRootFound nextRootShrinking nextBounded
              timed tailMember sourceRoot

/--
If a snapshot straddles an event already present in the initial prefix, its
source root was still growing at that common initial state.
-/
theorem TimedPairShiftHistory.sourceRoot_growing_at_initial_of_straddles
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
    (aligned : initialLabels.length = initial.blocks.length)
    (exact : EpisodeLedger.ExactAt initial initialLabels initialLedger)
    (phase : RootLineagePhase initial initialLabels)
    {eventIndex : ℕ}
    (eventCutLe : eventIndex + 1 ≤ initialEvents.length)
    (allOld :
      AllActiveClocksBefore initialLedger initialClock (eventIndex + 1))
    {timed : TimedAnnotatedPairShiftSnapshot n}
    (member : timed ∈ snapshots)
    (straddles : timed.UClockStraddlesAt eventIndex) :
    ∃ rootBlock,
      initial.block? timed.annotated.sourceRoot = some rootBlock ∧
        rootBlock.mode = .growing ∧
        rootBlock.creator = timed.annotated.sourceCreator := by
  have snapshotFacts := history.snapshot_episode_facts timed member
  have rootBounded :
      RootActiveClocksBefore initialLedger initialClock
        timed.annotated.sourceRoot (eventIndex + 1) := by
    intro element start active _startRoot
    exact allOld element start active
  have late :
      eventIndex + 1 ≤ timed.winnerStartEvent ∨
        eventIndex + 1 ≤ timed.loserStartEvent := by
    rcases straddles with winnerEarly | loserEarly
    · exact Or.inr (by omega)
    · exact Or.inl (by omega)
  have growingOfOld
      (element : Element n) (start : EpisodeStart n)
      (active : initialLedger element = some start)
      (startRoot :
        start.join.destinationRoot = timed.annotated.sourceRoot)
      (startCreator :
        start.join.destinationCreator =
          timed.annotated.sourceCreator) :
      ∃ rootBlock,
        initial.block? timed.annotated.sourceRoot = some rootBlock ∧
          rootBlock.mode = .growing ∧
          rootBlock.creator = timed.annotated.sourceCreator := by
    have sound := exact.sound element start active
    have payload :
        element ∈
          lineageElements initial initialLabels
            timed.annotated.sourceRoot := by
      rw [← startRoot]
      exact sound.2
    obtain ⟨blockId, block, blockFound, blockRootFound, blockMember⟩ :=
      (mem_lineageElements_iff aligned).mp payload
    obtain ⟨placementId, placementBlock, placementFound,
        placementMember, placementCreator⟩ :=
      exact.placement element start active
    have idsEq :
        blockId = placementId :=
      history.initialValid.blockId_eq_of_element_mem
        blockFound blockMember placementFound placementMember
    subst placementId
    rw [blockFound] at placementFound
    have placementBlockEq : placementBlock = block :=
      Option.some.inj placementFound.symm
    subst placementBlock
    have blockCreator :
        block.creator = timed.annotated.sourceCreator :=
      placementCreator.trans startCreator
    obtain ⟨rootBlock, rootFound⟩ :=
      phase.rootsRealized blockId timed.annotated.sourceRoot
        blockRootFound
    cases rootMode : rootBlock.mode with
    | growing =>
        have blockNonempty : block.elements ≠ [] := by
          exact List.ne_nil_of_mem blockMember
        have blockIdEq :
            blockId = timed.annotated.sourceRoot :=
          phase.growingOnly timed.annotated.sourceRoot rootBlock
            rootFound rootMode blockId block blockFound blockRootFound
            blockNonempty
        subst blockId
        rw [rootFound] at blockFound
        have blockEq : block = rootBlock :=
          Option.some.inj blockFound.symm
        subst block
        exact ⟨rootBlock, rootFound, rootMode, blockCreator⟩
    | shrinking =>
        have oldBounds :=
          history.snapshot_clocks_lt_of_root_shrinking phase
            rootFound rootMode rootBounded timed member rfl
        rcases late with winnerLate | loserLate <;> omega
  rcases straddles with winnerEarly | loserEarly
  · have oldWinner :=
      history.winner_old_at_initial eventCutLe member (by omega)
    exact
      growingOfOld timed.annotated.winner
        timed.annotated.winnerStart oldWinner.1
        snapshotFacts.1 snapshotFacts.2.2.1
  · have oldLoser :=
      history.loser_old_at_initial eventCutLe member (by omega)
    exact
      growingOfOld timed.annotated.loser
        timed.annotated.loserStart oldLoser.1
        snapshotFacts.2.1 snapshotFacts.2.2.2

/--
Splitting a timed history at a selected value-change event supplies the one
common state in which all roots incident to that event are growing.
-/
theorem TimedPairShiftHistory.eventGrowingRoots_from_prefix
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
    (aligned : initialLabels.length = initial.blocks.length)
    (exact : EpisodeLedger.ExactAt initial initialLabels initialLedger)
    (phase : RootLineagePhase initial initialLabels)
    (event : Fin finalEvents.length)
    (prefixLe : initialEvents.length ≤ event.val) :
    ∃ state : State n,
      state.Valid params ∧
        ∀ timed ∈
            uIncidentTimedSnapshots finalEvents event snapshots,
          ∃ block,
            state.block? timed.annotated.sourceRoot = some block ∧
              block.mode = .growing ∧
              block.creator = (finalEvents.get event).element := by
  induction history with
  | nil valid clockSound =>
      have eventLt := event.isLt
      omega
  | @cons before middle final beforeLabels finalLabels beforeLedger
      finalLedger beforeClock finalClock beforeEvents finalEvents
      operation operations tailSnapshots alignedAtHead exactAtHead
      clockSound head tail ih =>
      let nextEvents :=
        beforeEvents ++ operationValueChangeEvents operation
      have nextAligned :
          (RootLabels.after beforeLabels operation).length =
            middle.blocks.length :=
        (HistoryStep.mk head rfl).labels_length aligned
      have nextExact :=
        exact.after_step head aligned
      have nextPhase :=
        phase.after_step aligned head
      by_cases atHead : event.val < nextEvents.length
      · cases operation with
        | convert blockId =>
            simp [nextEvents, operationValueChangeEvents] at atHead
            omega
        | create creator =>
            simp [nextEvents, operationValueChangeEvents] at atHead
            omega
        | insert blockId inserted =>
            simp [nextEvents, operationValueChangeEvents] at atHead
            omega
        | delete blockId deleted =>
            simp [nextEvents, operationValueChangeEvents] at atHead
            omega
        | pass source matching =>
            simp [nextEvents, operationValueChangeEvents] at atHead
            omega
        | split source prefixLength =>
            simp [nextEvents, operationValueChangeEvents] at atHead
            omega
        | valueChange changed delta =>
            cases delta with
            | decrease =>
                have eventEq : event.val = beforeEvents.length := by
                  simp [nextEvents, operationValueChangeEvents] at atHead
                  omega
                have allOld :
                    AllActiveClocksBefore
                      (EpisodeLedger.after before beforeLabels beforeLedger
                        (.valueChange changed .decrease))
                      (EpisodeClock.after beforeEvents.length beforeClock
                        (.valueChange changed .decrease))
                      (event.val + 1) := by
                  intro element start active
                  have activeBefore :
                      beforeLedger element = some start := by
                    simpa using active
                  have clockLe :=
                    (clockSound element start activeBefore).1
                  simpa [EpisodeClock.after, eventEq] using
                    (show beforeClock element <
                        beforeEvents.length + 1 by omega)
                refine ⟨middle, head.2.2, ?_⟩
                intro timed incident
                have tailIncident :
                    timed ∈
                      uIncidentTimedSnapshots finalEvents event
                        tailSnapshots := by
                  simpa [operationTimedPairShiftSnapshots,
                    uIncidentTimedSnapshots] using incident
                have rawTail : timed ∈ tailSnapshots :=
                  (List.mem_filter.mp tailIncident).1
                have straddles :=
                  (mem_uIncidentTimedSnapshots_clockStraddles
                    finalEvents event tailSnapshots tailIncident).2.2
                have eventCutLe :
                    event.val + 1 ≤
                      (beforeEvents ++
                        operationValueChangeEvents
                          (.valueChange changed .decrease)).length := by
                  simp [operationValueChangeEvents, eventEq]
                obtain ⟨block, blockFound, blockGrowing, blockCreator⟩ :=
                  tail.sourceRoot_growing_at_initial_of_straddles
                    nextAligned nextExact nextPhase eventCutLe allOld
                    rawTail straddles
                have creatorEq :=
                  eventElement_eq_sourceCreator_of_mem_uIncident
                    finalEvents event tailSnapshots tailIncident
                exact
                  ⟨block, blockFound, blockGrowing,
                    blockCreator.trans creatorEq.symm⟩
            | increase =>
                have eventEq : event.val = beforeEvents.length := by
                  simp [nextEvents, operationValueChangeEvents] at atHead
                  omega
                have allOld :
                    AllActiveClocksBefore
                      (EpisodeLedger.after before beforeLabels beforeLedger
                        (.valueChange changed .increase))
                      (EpisodeClock.after beforeEvents.length beforeClock
                        (.valueChange changed .increase))
                      (event.val + 1) := by
                  intro element start active
                  have activeBefore :
                      beforeLedger element = some start := by
                    simpa using active
                  have clockLe :=
                    (clockSound element start activeBefore).1
                  simpa [EpisodeClock.after, eventEq] using
                    (show beforeClock element <
                        beforeEvents.length + 1 by omega)
                refine ⟨middle, head.2.2, ?_⟩
                intro timed incident
                have tailIncident :
                    timed ∈
                      uIncidentTimedSnapshots finalEvents event
                        tailSnapshots := by
                  simpa [operationTimedPairShiftSnapshots,
                    uIncidentTimedSnapshots] using incident
                have rawTail : timed ∈ tailSnapshots :=
                  (List.mem_filter.mp tailIncident).1
                have straddles :=
                  (mem_uIncidentTimedSnapshots_clockStraddles
                    finalEvents event tailSnapshots tailIncident).2.2
                have eventCutLe :
                    event.val + 1 ≤
                      (beforeEvents ++
                        operationValueChangeEvents
                          (.valueChange changed .increase)).length := by
                  simp [operationValueChangeEvents, eventEq]
                obtain ⟨block, blockFound, blockGrowing, blockCreator⟩ :=
                  tail.sourceRoot_growing_at_initial_of_straddles
                    nextAligned nextExact nextPhase eventCutLe allOld
                    rawTail straddles
                have creatorEq :=
                  eventElement_eq_sourceCreator_of_mem_uIncident
                    finalEvents event tailSnapshots tailIncident
                exact
                  ⟨block, blockFound, blockGrowing,
                    blockCreator.trans creatorEq.symm⟩
      · have nextPrefixLe : nextEvents.length ≤ event.val :=
          Nat.le_of_not_gt atHead
        obtain ⟨state, stateValid, rootSpec⟩ :=
          ih nextAligned nextExact nextPhase event nextPrefixLe
        refine ⟨state, stateValid, ?_⟩
        intro timed incident
        let headSnapshots :=
          operationTimedPairShiftSnapshots before middle beforeLabels
            beforeLedger beforeClock beforeEvents operation exact head aligned
        have headIncidentEmpty :
            uIncidentTimedSnapshots finalEvents event headSnapshots = [] :=
          uIncident_operation_eq_nil_of_eventsBefore_le
            finalEvents event before middle beforeLabels beforeLedger
              beforeClock beforeEvents operation exact head aligned prefixLe
        have selectedAppend :
            uIncidentTimedSnapshots finalEvents event
                (headSnapshots ++ tailSnapshots) =
              uIncidentTimedSnapshots finalEvents event headSnapshots ++
                uIncidentTimedSnapshots finalEvents event tailSnapshots := by
          simp [uIncidentTimedSnapshots]
        have tailIncident :
            timed ∈
              uIncidentTimedSnapshots finalEvents event tailSnapshots := by
          change
            timed ∈
              uIncidentTimedSnapshots finalEvents event
                (headSnapshots ++ tailSnapshots) at incident
          rw [selectedAppend, headIncidentEmpty] at incident
          simpa using incident
        exact rootSpec timed tailIncident

/--
The concrete timed history lifted from an empty interface initial state
satisfies the event-state growing-root bridge at every significance threshold.
-/
theorem TimedPairShiftHistory.uEventGrowingRoots_of_initial
    {n : ℕ} {params : Parameters}
    {initial final : State n}
    {finalLabels : RootLabels}
    {finalLedger : EpisodeLedger n}
    {finalClock : EpisodeClock n}
    {finalEvents : List (ValueChangeEvent n)}
    {operations : List (Operation n)}
    {snapshots : List (TimedAnnotatedPairShiftSnapshot n)}
    (history :
      TimedPairShiftHistory params initial []
        (EpisodeLedger.empty : EpisodeLedger n)
        (fun _ => 0) [] operations snapshots
        final finalLabels finalLedger finalClock finalEvents)
    (initialState : initial.Initial params)
    (threshold : ℕ) :
    UEventGrowingRoots params finalEvents threshold snapshots := by
  intro event
  have aligned : ([] : RootLabels).length = initial.blocks.length := by
    simp [initialState.2]
  have exact :
      EpisodeLedger.ExactAt initial []
        (EpisodeLedger.empty : EpisodeLedger n) :=
    EpisodeLedger.ExactAt.initial initialState
  have phase : RootLineagePhase initial [] :=
    RootLineagePhase.initial initialState
  obtain ⟨state, stateValid, rootSpec⟩ :=
    history.eventGrowingRoots_from_prefix aligned exact phase event (by simp)
  refine ⟨state, stateValid, ?_⟩
  intro timed incident
  have significantMember :
      timed ∈ significantTimedSnapshots threshold snapshots :=
    (List.mem_filter.mp incident).1
  have rawMember : timed ∈ snapshots :=
    (List.mem_filter.mp significantMember).1
  have selected :
      decide (timed.uTemporalCharge finalEvents event ≠ 0) = true :=
    (List.mem_filter.mp incident).2
  have rawIncident :
      timed ∈ uIncidentTimedSnapshots finalEvents event snapshots :=
    List.mem_filter.mpr ⟨rawMember, selected⟩
  exact rootSpec timed rawIncident

end LifetimeHistory

end Splay.Interface
