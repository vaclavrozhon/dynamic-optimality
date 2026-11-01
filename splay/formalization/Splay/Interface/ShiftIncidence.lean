import Splay.Interface.ValueShiftHistory
import Splay.Interface.WShiftTrace
import Splay.Interface.EventIntervalCharge
import Splay.Interface.ActivityTail

namespace Splay.Interface

/--
One pair-shift snapshot together with the exact source lineage, physical block,
pre-pass counter, and matching endpoints that produced it.
-/
structure AnnotatedPairShiftSnapshot (n : ℕ) where
  snapshot : PairShiftSnapshot
  sourceRoot : RootId
  source : BlockId
  sourcePassCount : ℕ
  sourceCreator : Element n
  winner : Element n
  loser : Element n
  winnerStart : EpisodeStart n
  loserStart : EpisodeStart n

/-- A pass is significant exactly while its inherited counter is below `τ`. -/
def AnnotatedPairShiftSnapshot.IsSignificant {n : ℕ}
    (threshold : ℕ) (annotated : AnnotatedPairShiftSnapshot n) : Prop :=
  annotated.sourcePassCount < threshold

/-- Boolean form used to split finite chronological annotation lists. -/
def AnnotatedPairShiftSnapshot.significantDecision {n : ℕ}
    (threshold : ℕ) (annotated : AnnotatedPairShiftSnapshot n) : Bool :=
  decide (annotated.sourcePassCount < threshold)

/-- Chronological significant prefix-level occurrences. -/
def significantAnnotatedSnapshots {n : ℕ}
    (threshold : ℕ) (snapshots : List (AnnotatedPairShiftSnapshot n)) :
    List (AnnotatedPairShiftSnapshot n) :=
  snapshots.filter
    (AnnotatedPairShiftSnapshot.significantDecision threshold)

/-- Chronological complementary insignificant occurrences. -/
def insignificantAnnotatedSnapshots {n : ℕ}
    (threshold : ℕ) (snapshots : List (AnnotatedPairShiftSnapshot n)) :
    List (AnnotatedPairShiftSnapshot n) :=
  snapshots.filter fun snapshot =>
    !(AnnotatedPairShiftSnapshot.significantDecision threshold snapshot)

/-- One chronological unit value-change event. -/
structure ValueChangeEvent (n : ℕ) where
  element : Element n
  delta : ℤ
  deriving DecidableEq, Repr

namespace ValueChangeEvent

/-- Contribution of an event to one selected element. -/
def signedFor {n : ℕ} (event : ValueChangeEvent n)
    (target : Element n) : ℤ :=
  if event.element = target then event.delta else 0

/-- Boolean selector for the events of one fixed element. -/
def isFor {n : ℕ} (target : Element n)
    (event : ValueChangeEvent n) : Bool :=
  decide (event.element = target)

end ValueChangeEvent

/-- The zero-or-one event list contributed by one operation. -/
def operationValueChangeEvents {n : ℕ} :
    Operation n → List (ValueChangeEvent n)
  | .valueChange element .decrease =>
      [{ element := element, delta := -1 }]
  | .valueChange element .increase =>
      [{ element := element, delta := 1 }]
  | _ => []

/-- Chronological value-change events of a complete operation list. -/
def valueChangeEvents {n : ℕ}
    (operations : List (Operation n)) : List (ValueChangeEvent n) :=
  operations.flatMap operationValueChangeEvents

/-- Signed drift of one element over an event sublist. -/
def eventDrift {n : ℕ} (target : Element n)
    (events : List (ValueChangeEvent n)) : ℤ :=
  (events.map fun event => event.signedFor target).sum

/-- The concrete unit-event delta vector used by temporal charging. -/
def valueChangeDeltaVector {n : ℕ}
    (events : List (ValueChangeEvent n)) :
    Fin events.length → ℤ :=
  eventDeltaVector events ValueChangeEvent.delta

/-- Selected generic event sums coincide with the semantic element drift. -/
theorem selectedEventDeltaSum_isFor {n : ℕ}
    (events : List (ValueChangeEvent n)) (target : Element n) :
    selectedEventDeltaSum events ValueChangeEvent.delta
        (ValueChangeEvent.isFor target) =
      eventDrift target events := by
  induction events with
  | nil =>
      rfl
  | cons event events ih =>
      change
        (((events.filter
          (ValueChangeEvent.isFor target)).map
            ValueChangeEvent.delta).sum) =
          eventDrift target events at ih
      by_cases same : event.element = target
      · simp [selectedEventDeltaSum, ValueChangeEvent.isFor,
          eventDrift, ValueChangeEvent.signedFor, same, ih]
      · simp [selectedEventDeltaSum, ValueChangeEvent.isFor,
          eventDrift, ValueChangeEvent.signedFor, same, ih]

/-- An event interval computes exactly the drift of its selected element. -/
theorem temporalShift_valueChange_interval
    {n : ℕ} (events : List (ValueChangeEvent n))
    (target : Element n) (start stop : ℕ)
    (startLe : start ≤ stop) (stopLe : stop ≤ events.length) :
    temporalShift (valueChangeDeltaVector events)
        (eventIntervalCharge events
          (ValueChangeEvent.isFor target) start stop) =
      eventDrift target ((events.take stop).drop start) := by
  unfold valueChangeDeltaVector
  rw [temporalShift_eventIntervalCharge events ValueChangeEvent.delta
    (ValueChangeEvent.isFor target) start stop startLe stopLe]
  exact selectedEventDeltaSum_isFor _ _

/-- Temporal shift is linear under reversal of an incidence vector. -/
theorem temporalShift_neg_charge
    {eventCount : ℕ} (deltas charge : Fin eventCount → ℤ) :
    temporalShift deltas (fun event => -charge event) =
      -temporalShift deltas charge := by
  unfold temporalShift
  calc
    (∑ event, -charge event * deltas event) =
        ∑ event, -(charge event * deltas event) := by
          apply Finset.sum_congr rfl
          intro event _member
          ring
    _ = -(∑ event, charge event * deltas event) := by
          rw [Finset.sum_neg_distrib]

/-- Temporal shift is linear under subtraction of incidence vectors. -/
theorem temporalShift_sub_charge
    {eventCount : ℕ} (deltas first second : Fin eventCount → ℤ) :
    temporalShift deltas
        (fun event => first event - second event) =
      temporalShift deltas first - temporalShift deltas second := by
  unfold temporalShift
  calc
    (∑ event, (first event - second event) * deltas event) =
        ∑ event,
          (first event * deltas event -
            second event * deltas event) := by
          apply Finset.sum_congr rfl
          intro event _member
          ring
    _ =
        (∑ event, first event * deltas event) -
          ∑ event, second event * deltas event := by
          rw [Finset.sum_sub_distrib]

/-- Event extraction has exactly the interface value-change count. -/
@[simp]
theorem length_operationValueChangeEvents {n : ℕ}
    (operation : Operation n) :
    (operationValueChangeEvents operation).length =
      operation.valueChangeCount := by
  cases operation with
  | convert blockId =>
      rfl
  | create creator =>
      rfl
  | insert blockId element =>
      rfl
  | delete blockId element =>
      rfl
  | pass blockId matching =>
      rfl
  | split blockId prefixLength =>
      rfl
  | valueChange element delta =>
      cases delta <;> rfl

/-- The global event list has exactly `totalValueChanges` entries. -/
@[simp]
theorem length_valueChangeEvents {n : ℕ}
    (operations : List (Operation n)) :
    (valueChangeEvents operations).length =
      totalValueChanges operations := by
  induction operations with
  | nil =>
      rfl
  | cons operation operations ih =>
      simp [valueChangeEvents, totalValueChanges]

/-- Every extracted event is a signed unit event. -/
theorem delta_abs_le_one_of_mem_operationValueChangeEvents
    {n : ℕ} {operation : Operation n} {event : ValueChangeEvent n}
    (member : event ∈ operationValueChangeEvents operation) :
    |event.delta| ≤ 1 := by
  cases operation with
  | convert blockId =>
      simp [operationValueChangeEvents] at member
  | create creator =>
      simp [operationValueChangeEvents] at member
  | insert blockId element =>
      simp [operationValueChangeEvents] at member
  | delete blockId element =>
      simp [operationValueChangeEvents] at member
  | pass blockId matching =>
      simp [operationValueChangeEvents] at member
  | split blockId prefixLength =>
      simp [operationValueChangeEvents] at member
  | valueChange element delta =>
      cases delta <;>
        simp only [operationValueChangeEvents,
          List.mem_singleton] at member <;>
        subst event <;> norm_num

/-- Every event extracted from a complete operation list is a signed unit. -/
theorem delta_abs_le_one_of_mem_valueChangeEvents
    {n : ℕ} {operations : List (Operation n)}
    {event : ValueChangeEvent n}
    (member : event ∈ valueChangeEvents operations) :
    |event.delta| ≤ 1 := by
  obtain ⟨operation, operationMem, eventMem⟩ :=
    List.mem_flatMap.mp member
  exact
    delta_abs_le_one_of_mem_operationValueChangeEvents eventMem

/-- Extracted event drift is exactly the operation's signed value change. -/
theorem eventDrift_operationValueChangeEvents
    {n : ℕ} (target : Element n) (operation : Operation n) :
    eventDrift target (operationValueChangeEvents operation) =
      operation.signedValueChange target := by
  cases operation with
  | convert blockId =>
      rfl
  | create creator =>
      rfl
  | insert blockId element =>
      rfl
  | delete blockId element =>
      rfl
  | pass blockId matching =>
      rfl
  | split blockId prefixLength =>
      rfl
  | valueChange element delta =>
      cases delta <;>
        simp [eventDrift, operationValueChangeEvents,
          ValueChangeEvent.signedFor, Operation.signedValueChange]

/-- Event drift distributes over chronological concatenation. -/
theorem eventDrift_append {n : ℕ} (target : Element n)
    (first second : List (ValueChangeEvent n)) :
    eventDrift target (first ++ second) =
      eventDrift target first + eventDrift target second := by
  simp [eventDrift]

/-- Number of already-seen value-change events at each episode's opening. -/
abbrev EpisodeClock (n : ℕ) :=
  Element n → ℕ

namespace EpisodeClock

/-- Install a common event time for all loser episodes opened by one pass. -/
def installPassStarts {n : ℕ} (eventCount : ℕ) :
    EpisodeClock n → List (Pairing n) → EpisodeClock n
  | clock, [] => clock
  | clock, pairing :: matching =>
      installPassStarts eventCount
        (Function.update clock pairing.loser eventCount) matching

/-- Deterministic episode-opening clock update of one operation. -/
def after {n : ℕ} (eventCount : ℕ)
    (clock : EpisodeClock n) : Operation n → EpisodeClock n
  | .insert _ element =>
      Function.update clock element eventCount
  | .pass _ matching =>
      installPassStarts eventCount clock matching
  | _ => clock

/-- Non-losers retain their previous episode time through a pass. -/
theorem installPassStarts_apply_of_not_mem
    {n : ℕ} (eventCount : ℕ) (clock : EpisodeClock n)
    (matching : List (Pairing n)) (element : Element n)
    (notLoser : element ∉ pairingLosers matching) :
    installPassStarts eventCount clock matching element =
      clock element := by
  induction matching generalizing clock with
  | nil =>
      rfl
  | cons pairing matching ih =>
      have notCons :
          element ∉ pairing.loser :: pairingLosers matching := by
        simpa [pairingLosers] using notLoser
      have elementNe : element ≠ pairing.loser :=
        (List.ne_and_not_mem_of_not_mem_cons notCons).1
      have notTail : element ∉ pairingLosers matching :=
        (List.ne_and_not_mem_of_not_mem_cons notCons).2
      rw [installPassStarts]
      rw [ih _ notTail]
      simp [Function.update, elementNe]

/-- Distinct losers receive exactly the pass's current event time. -/
theorem installPassStarts_apply_of_mem
    {n : ℕ} (eventCount : ℕ) (clock : EpisodeClock n)
    {matching : List (Pairing n)}
    (losersNodup : (pairingLosers matching).Nodup)
    {pairing : Pairing n} (pairingMem : pairing ∈ matching) :
    installPassStarts eventCount clock matching pairing.loser =
      eventCount := by
  induction matching generalizing clock pairing with
  | nil =>
      simp at pairingMem
  | cons head matching ih =>
      rcases List.mem_cons.mp pairingMem with pairingEq | pairingTail
      · subst pairing
        have headNotTail :
            head.loser ∉ pairingLosers matching := by
          simpa [pairingLosers] using
            (List.nodup_cons.mp losersNodup).1
        rw [installPassStarts]
        rw [installPassStarts_apply_of_not_mem
          eventCount _ matching head.loser headNotTail]
        simp
      · have tailNodup : (pairingLosers matching).Nodup := by
          simpa [pairingLosers] using
            (List.nodup_cons.mp losersNodup).2
        rw [installPassStarts]
        exact ih _ tailNodup pairingTail

/--
The clock is semantically sound when every active start reconstructs both the
joining element's current value and its creator's current value from the
events seen since that start.
-/
def SoundAt {n : ℕ} (state : State n) (ledger : EpisodeLedger n)
    (clock : EpisodeClock n) (events : List (ValueChangeEvent n)) : Prop :=
  ∀ element start, ledger element = some start →
    clock element ≤ events.length ∧
      (state.value element : ℤ) =
        (start.join.valueAtJoin : ℤ) +
          eventDrift element (events.drop (clock element)) ∧
      (state.value start.join.destinationCreator : ℤ) =
        (start.creatorValueAtJoin : ℤ) +
          eventDrift start.join.destinationCreator
            (events.drop (clock element))

/-- The empty active ledger is clock-sound for any event prefix. -/
theorem soundAt_empty {n : ℕ}
    (state : State n) (clock : EpisodeClock n)
    (events : List (ValueChangeEvent n)) :
    SoundAt state (EpisodeLedger.empty : EpisodeLedger n)
      clock events := by
  intro element start active
  simp [EpisodeLedger.empty] at active

end EpisodeClock

/-- Drift of a suffix after appending one event batch. -/
theorem eventDrift_drop_append
    {n : ℕ} (target : Element n)
    (events more : List (ValueChangeEvent n)) (start : ℕ)
    (startLe : start ≤ events.length) :
    eventDrift target ((events ++ more).drop start) =
      eventDrift target (events.drop start) +
        eventDrift target more := by
  rw [List.drop_append_of_le_length startLe]
  exact eventDrift_append target _ _

/-- An unchanged active episode remains clock-sound across one exact step. -/
theorem EpisodeClock.existing_sound_after_step
    {n : ℕ} {params : Parameters}
    {before afterState : State n} {operation : Operation n}
    {ledger : EpisodeLedger n} {clock : EpisodeClock n}
    {events : List (ValueChangeEvent n)}
    {element : Element n} {start : EpisodeStart n}
    (sound : EpisodeClock.SoundAt before ledger clock events)
    (active : ledger element = some start)
    (step : Step params before operation afterState) :
    clock element ≤
          (events ++ operationValueChangeEvents operation).length ∧
      (afterState.value element : ℤ) =
        (start.join.valueAtJoin : ℤ) +
          eventDrift element
            ((events ++ operationValueChangeEvents operation).drop
              (clock element)) ∧
      (afterState.value start.join.destinationCreator : ℤ) =
        (start.creatorValueAtJoin : ℤ) +
          eventDrift start.join.destinationCreator
            ((events ++ operationValueChangeEvents operation).drop
              (clock element)) := by
  have old := sound element start active
  have elementDrift :=
    step.2.1.value_eq_add_signedValueChange element
  have creatorDrift :=
    step.2.1.value_eq_add_signedValueChange
      start.join.destinationCreator
  constructor
  · rw [List.length_append]
    omega
  constructor
  · rw [eventDrift_drop_append element events
      (operationValueChangeEvents operation) (clock element) old.1]
    rw [eventDrift_operationValueChangeEvents]
    rw [elementDrift, old.2.1]
    ring
  · rw [eventDrift_drop_append start.join.destinationCreator events
      (operationValueChangeEvents operation) (clock element) old.1]
    rw [eventDrift_operationValueChangeEvents]
    rw [creatorDrift, old.2.2]
    ring

/-- The event clock remains sound under the exact ledger/event update. -/
theorem EpisodeClock.SoundAt.after_step
    {n : ℕ} {params : Parameters}
    {before afterState : State n} {labels : RootLabels}
    {operation : Operation n} {ledger : EpisodeLedger n}
    {clock : EpisodeClock n} {events : List (ValueChangeEvent n)}
    (sound : EpisodeClock.SoundAt before ledger clock events)
    (step : Step params before operation afterState) :
    EpisodeClock.SoundAt afterState
      (EpisodeLedger.after before labels ledger operation)
      (EpisodeClock.after events.length clock operation)
      (events ++ operationValueChangeEvents operation) := by
  cases operation with
  | convert blockId =>
      intro element start active
      exact
        EpisodeClock.existing_sound_after_step sound
          (by simpa using active) step
  | create creator =>
      intro element start active
      exact
        EpisodeClock.existing_sound_after_step sound
          (by simpa using active) step
  | insert destination inserted =>
      intro element start active
      by_cases elementEq : element = inserted
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
        rw [installed] at active
        have startEq :
            EpisodeStart.ofJoin before joined = start :=
          Option.some.inj active
        subst start
        cases step.2.1 with
        | insert destinationFound growing unassigned valueOrder
            blocksEq valuesEq =>
            constructor
            · simp [EpisodeClock.after]
            constructor
            · simp [EpisodeClock.after, operationValueChangeEvents,
                EpisodeStart.ofJoin, joined, makeJoinOccurrence,
                valuesEq, eventDrift]
            · simp [EpisodeClock.after, operationValueChangeEvents,
                EpisodeStart.ofJoin, joined, makeJoinOccurrence,
                valuesEq, eventDrift]
      · have oldActive : ledger element = some start := by
          simpa [EpisodeLedger.after, elementEq] using active
        have existing :=
          EpisodeClock.existing_sound_after_step sound oldActive step
        simpa [EpisodeClock.after, Function.update, elementEq] using
          existing
  | delete source deleted =>
      intro element start active
      by_cases elementEq : element = deleted
      · subst element
        simp [EpisodeLedger.after] at active
      · have oldActive : ledger element = some start := by
          simpa [EpisodeLedger.after, elementEq] using active
        exact
          EpisodeClock.existing_sound_after_step sound oldActive step
  | pass source matching =>
      intro element start active
      obtain ⟨sourceBlock, sourceFound, validMatching⟩ :
          ∃ sourceBlock,
            before.block? source = some sourceBlock ∧
              MatchingValid params before source sourceBlock matching := by
        cases step.2.1 with
        | pass found valid blocksEq valuesEq =>
            exact ⟨_, found, valid⟩
      have losersNodup : (pairingLosers matching).Nodup :=
        pairingLosers_nodup validMatching.2.1
      by_cases loserMem : element ∈ pairingLosers matching
      · obtain ⟨pairing, pairingMem, loserEq⟩ :=
          List.mem_map.mp (by
            simpa [pairingLosers] using loserMem)
        subst element
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
        change
          EpisodeLedger.after before labels ledger
              (.pass source matching) pairing.loser =
            some (EpisodeStart.ofJoin before joined) at installed
        rw [installed] at active
        have startEq :
            EpisodeStart.ofJoin before joined = start :=
          Option.some.inj active
        subst start
        have clockInstalled :
            EpisodeClock.after events.length clock
                (.pass source matching) pairing.loser =
              events.length := by
          exact
            EpisodeClock.installPassStarts_apply_of_mem
              events.length clock losersNodup pairingMem
        cases step.2.1 with
        | pass found valid blocksEq valuesEq =>
            constructor
            · simp [clockInstalled, operationValueChangeEvents]
            constructor
            · simp [clockInstalled, operationValueChangeEvents,
                EpisodeStart.ofJoin, joined, makeJoinOccurrence,
                valuesEq, eventDrift]
            · simp [clockInstalled, operationValueChangeEvents,
                EpisodeStart.ofJoin, joined, makeJoinOccurrence,
                valuesEq, eventDrift]
      · have oldActive : ledger element = some start := by
          change
            EpisodeLedger.installPassJoins before labels source ledger
                matching element =
              some start at active
          rw [EpisodeLedger.installPassJoins_apply_of_not_mem
            before labels source ledger matching element loserMem] at active
          exact active
        have existing :=
          EpisodeClock.existing_sound_after_step sound oldActive step
        have clockUnchanged :
            EpisodeClock.after events.length clock
                (.pass source matching) element =
              clock element :=
          EpisodeClock.installPassStarts_apply_of_not_mem
            events.length clock matching element loserMem
        simpa [clockUnchanged] using existing
  | split source prefixLength =>
      intro element start active
      exact
        EpisodeClock.existing_sound_after_step sound
          (by simpa using active) step
  | valueChange element delta =>
      intro assigned start active
      exact
        EpisodeClock.existing_sound_after_step sound
          (by simpa using active) step

/--
A physical lower bound on the pass counter of every block containing one
fixed element.
-/
def PassFloorAt {n : ℕ} (state : State n)
    (element : Element n) (floor : ℕ) : Prop :=
  ∀ blockId block,
    state.block? blockId = some block →
      element ∈ block.elements →
      floor ≤ block.passCount

/--
The pass floor is relevant only while the element's current episode predates
the selected event cutoff.
-/
def ClockedPassFloorAt {n : ℕ} (state : State n)
    (clock : EpisodeClock n) (cutoff : ℕ)
    (element : Element n) (floor : ℕ) : Prop :=
  clock element < cutoff → PassFloorAt state element floor

private theorem pairingWinners_sublist
    {n : ℕ} (matching : List (Pairing n)) :
    (matching.map Pairing.winner).Sublist
      (matching.flatMap fun pairing =>
        [pairing.winner, pairing.loser]) := by
  induction matching with
  | nil =>
      exact .slnil
  | cons pairing matching ih =>
      exact (ih.cons pairing.loser).cons_cons pairing.winner

private theorem pairingWinners_nodup
    {n : ℕ} {matching : List (Pairing n)}
    (endpointsNodup :
      (matching.flatMap fun pairing =>
        [pairing.winner, pairing.loser]).Nodup) :
    (matching.map Pairing.winner).Nodup :=
  (pairingWinners_sublist matching).nodup endpointsNodup

private theorem pairingWinner_not_mem_pairingLosers
    {n : ℕ} {matching : List (Pairing n)}
    (endpointsNodup :
      (matching.flatMap fun pairing =>
        [pairing.winner, pairing.loser]).Nodup)
    {pairing : Pairing n} (pairingMem : pairing ∈ matching) :
    pairing.winner ∉ pairingLosers matching := by
  induction matching with
  | nil =>
      simp at pairingMem
  | cons head matching ih =>
      have expanded :
          (head.winner :: head.loser ::
            matching.flatMap fun later =>
              [later.winner, later.loser]).Nodup := by
        simpa using endpointsNodup
      have headFresh := (List.nodup_cons.mp expanded).1
      have afterHead := (List.nodup_cons.mp expanded).2
      have loserFresh := (List.nodup_cons.mp afterHead).1
      have tailNodup := (List.nodup_cons.mp afterHead).2
      rcases List.mem_cons.mp pairingMem with pairingEq | tailMem
      · subst pairing
        have headParts :
            head.winner ≠ head.loser ∧
              head.winner ∉
                matching.flatMap fun later =>
                  [later.winner, later.loser] := by
          simpa only [List.mem_cons, not_or] using headFresh
        have headNe : head.winner ≠ head.loser :=
          headParts.1
        have notTail :
            head.winner ∉ pairingLosers matching := by
          intro loserMem
          apply headParts.2
          exact
            (pairingLosers_sublist matching).subset loserMem
        intro loserMem
        rcases (by
          simpa [pairingLosers] using loserMem) with
          loserEq | ⟨other, otherMem, otherEq⟩
        · exact headNe loserEq
        · apply notTail
          simpa [pairingLosers] using
            (show ∃ later ∈ matching,
                later.loser = head.winner from
              ⟨other, otherMem, otherEq⟩)
      · have winnerMem :
            pairing.winner ∈
              matching.flatMap fun later =>
                [later.winner, later.loser] :=
          List.mem_flatMap.mpr
            ⟨pairing, tailMem, by simp⟩
        have winnerNe : pairing.winner ≠ head.loser := by
          intro same
          apply loserFresh
          simpa [same] using winnerMem
        have notTail :=
          ih tailNodup tailMem
        intro loserMem
        rcases (by
          simpa [pairingLosers] using loserMem) with
          loserEq | ⟨other, otherMem, otherEq⟩
        · exact winnerNe loserEq
        · apply notTail
          simpa [pairingLosers] using
            (show ∃ later ∈ matching,
                later.loser = pairing.winner from
              ⟨other, otherMem, otherEq⟩)

private theorem lookup_modify_preserves
    {α : Type*} {P : α → Prop}
    (values : List α) (index : ℕ) (update : α → α)
    (all :
      ∀ (valueId : ℕ) (value : α),
        values[valueId]? = some value → P value)
    (preserves : ∀ (value : α), P value → P (update value)) :
    ∀ (valueId : ℕ) (value : α),
      (values.modify index update)[valueId]? = some value →
        P value := by
  intro valueId value found
  rw [List.getElem?_modify] at found
  cases originalFound : values[valueId]? with
  | none =>
      simp [originalFound] at found
  | some original =>
      by_cases same : index = valueId
      · simp [originalFound, same] at found
        subst value
        exact preserves original (all valueId original originalFound)
      · simp [originalFound, same] at found
        subst value
        exact all valueId original originalFound

private theorem passFloor_modify_fixed
    {n : ℕ} (blocks : List (Block n)) (index : ℕ)
    (source replacement : Block n)
    (sourceFound : blocks[index]? = some source)
    (element : Element n) (floor : ℕ)
    (all :
      ∀ (blockId : ℕ) (block : Block n),
        blocks[blockId]? = some block →
          element ∈ block.elements →
          floor ≤ block.passCount)
    (replacementOk :
      element ∈ replacement.elements →
        floor ≤ replacement.passCount) :
    ∀ (blockId : ℕ) (block : Block n),
      (blocks.modify index fun _ => replacement)[blockId]? =
          some block →
        element ∈ block.elements →
        floor ≤ block.passCount := by
  intro blockId block found member
  rw [List.getElem?_modify] at found
  cases originalFound : blocks[blockId]? with
  | none =>
      simp [originalFound] at found
  | some original =>
      by_cases same : index = blockId
      · subst blockId
        rw [sourceFound] at originalFound
        have originalEq : original = source :=
          Option.some.inj originalFound.symm
        subst original
        simp [sourceFound] at found
        subst block
        exact replacementOk member
      · simp [originalFound, same] at found
        subst block
        exact all blockId original originalFound member

private theorem mem_of_mem_removeLosers
    {n : ℕ} {element : Element n}
    {elements : List (Element n)}
    {matching : List (Pairing n)}
    (member : element ∈ removeLosers elements matching) :
    element ∈ elements := by
  induction matching generalizing elements with
  | nil =>
      simpa [removeLosers] using member
  | cons pairing matching ih =>
      apply List.mem_of_mem_erase
      exact ih (by simpa [removeLosers] using member)

private theorem passFloor_insertAtDestinations
    {n : ℕ} (blocks : List (Block n))
    (matching : List (Pairing n))
    (element : Element n) (floor : ℕ)
    (all :
      ∀ (blockId : ℕ) (block : Block n),
        blocks[blockId]? = some block →
          element ∈ block.elements →
          floor ≤ block.passCount)
    (notLoser : element ∉ pairingLosers matching) :
    ∀ (blockId : ℕ) (block : Block n),
      (insertAtDestinations blocks matching)[blockId]? =
          some block →
        element ∈ block.elements →
        floor ≤ block.passCount := by
  induction matching generalizing blocks with
  | nil =>
      exact all
  | cons pairing matching ih =>
      let updated :=
        blocks.modify pairing.destination fun destination =>
          { destination with
            elements := pairing.loser :: destination.elements }
      have elementNe : element ≠ pairing.loser := by
        intro same
        apply notLoser
        simp [pairingLosers, same]
      have tailNotLoser : element ∉ pairingLosers matching := by
        intro tailMember
        apply notLoser
        change element ∈ pairing.loser :: pairingLosers matching
        exact List.mem_cons_of_mem _ tailMember
      apply ih updated
      · apply lookup_modify_preserves blocks pairing.destination
          (fun destination =>
            { destination with
              elements := pairing.loser :: destination.elements })
          (P := fun block =>
            element ∈ block.elements → floor ≤ block.passCount)
          all
        intro destination destinationOk member
        apply destinationOk
        simpa [elementNe] using member
      · exact tailNotLoser

/--
An event-relative physical pass floor survives every legal step.  Episode
resets are harmless: their new clock is the current event count, so they make
the strict pre-cutoff premise false.
-/
theorem ClockedPassFloorAt.after_step
    {n : ℕ} {params : Parameters}
    {before after : State n} {operation : Operation n}
    {clock : EpisodeClock n}
    {events : List (ValueChangeEvent n)}
    {cutoff floor : ℕ} {element : Element n}
    (invariant :
      ClockedPassFloorAt before clock cutoff element floor)
    (cutoffLe : cutoff ≤ events.length)
    (step : Step params before operation after) :
    ClockedPassFloorAt after
      (EpisodeClock.after events.length clock operation)
      cutoff element floor := by
  intro nextClockLow
  have oldFloor (oldClockLow : clock element < cutoff) :
      PassFloorAt before element floor :=
    invariant oldClockLow
  unfold PassFloorAt
  intro query block found member
  unfold State.block? at found
  cases operation with
  | convert sourceId =>
      have oldClockLow : clock element < cutoff := by
        simpa [EpisodeClock.after] using nextClockLow
      cases step.2.1 with
      | convert sourceFound sourceGrowing blocksEq valuesEq =>
          rw [blocksEq] at found
          apply
            lookup_modify_preserves before.blocks sourceId
              (fun current => { current with mode := .shrinking })
              (P := fun current =>
                element ∈ current.elements →
                  floor ≤ current.passCount)
              (by
                intro blockId current currentFound
                exact oldFloor oldClockLow
                  blockId current
                  (by simpa [State.block?] using currentFound))
              (by
                intro current currentOk
                simpa using currentOk)
              query block found member
  | create creator =>
      have oldClockLow : clock element < cutoff := by
        simpa [EpisodeClock.after] using nextClockLow
      cases step.2.1 with
      | create room blocksEq valuesEq =>
          rw [blocksEq, List.getElem?_append] at found
          by_cases old : query < before.blocks.length
          · simp only [old, if_pos] at found
            exact oldFloor oldClockLow query block
              (by simpa [State.block?] using found) member
          · simp only [old] at found
            have offsetLt :
                query - before.blocks.length < 1 :=
              (List.getElem?_eq_some_iff.mp found).choose
            have offsetZero :
                query - before.blocks.length = 0 :=
              Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ offsetLt)
            simp [offsetZero] at found
            subst block
            simp at member
  | insert target inserted =>
      by_cases insertedEq : element = inserted
      · subst inserted
        simp [EpisodeClock.after] at nextClockLow
        omega
      · have oldClockLow : clock element < cutoff := by
          simpa [EpisodeClock.after, Function.update, insertedEq] using
            nextClockLow
        cases step.2.1 with
        | insert targetFound targetGrowing unassigned valueOrder
            blocksEq valuesEq =>
            rw [blocksEq] at found
            apply
              lookup_modify_preserves before.blocks target
                (fun current =>
                  { current with
                    elements := inserted :: current.elements })
                (P := fun current =>
                  element ∈ current.elements →
                    floor ≤ current.passCount)
                (by
                  intro blockId current currentFound
                  exact oldFloor oldClockLow
                    blockId current
                    (by simpa [State.block?] using currentFound))
                (by
                  intro current currentOk updatedMember
                  apply currentOk
                  simpa [insertedEq] using updatedMember)
                query block found member
  | delete source deleted =>
      have oldClockLow : clock element < cutoff := by
        simpa [EpisodeClock.after] using nextClockLow
      cases step.2.1 with
      | delete sourceFound sourceShrinking present blocksEq valuesEq =>
          rw [blocksEq] at found
          apply
            lookup_modify_preserves before.blocks source
              (fun current =>
                { current with
                  elements := current.elements.erase deleted })
              (P := fun current =>
                element ∈ current.elements →
                  floor ≤ current.passCount)
              (by
                intro blockId current currentFound
                exact oldFloor oldClockLow
                  blockId current
                  (by simpa [State.block?] using currentFound))
              (by
                intro current currentOk updatedMember
                exact currentOk (List.mem_of_mem_erase updatedMember))
              query block found member
  | pass source matching =>
      obtain ⟨sourceBlock, sourceFound, validMatching⟩ :
          ∃ sourceBlock,
            before.block? source = some sourceBlock ∧
              MatchingValid params before source sourceBlock matching := by
        cases step.2.1 with
        | pass found validMatching blocksEq valuesEq =>
            exact ⟨_, found, validMatching⟩
      have losersNodup :
          (pairingLosers matching).Nodup :=
        pairingLosers_nodup validMatching.2.1
      have notLoser : element ∉ pairingLosers matching := by
        intro loserMember
        obtain ⟨pairing, pairingMem, loserEq⟩ :=
          List.mem_map.mp (by
            simpa [pairingLosers] using loserMember)
        have installed :=
          EpisodeClock.installPassStarts_apply_of_mem
            events.length clock losersNodup pairingMem
        rw [loserEq] at installed
        change
          EpisodeClock.installPassStarts events.length clock matching
              element <
            cutoff at nextClockLow
        rw [installed] at nextClockLow
        omega
      have oldClockLow : clock element < cutoff := by
        change
          EpisodeClock.installPassStarts events.length clock matching
              element <
            cutoff at nextClockLow
        rw [EpisodeClock.installPassStarts_apply_of_not_mem
          events.length clock matching element notLoser] at nextClockLow
        exact nextClockLow
      cases step.2.1 with
      | pass actualFound _validMatching blocksEq valuesEq =>
          rename_i actualSource
          have actualSourceEq : actualSource = sourceBlock := by
            rw [sourceFound] at actualFound
            exact (Option.some.inj actualFound).symm
          subst actualSource
          rw [blocksEq] at found
          unfold passBlocks at found
          let sourceAfter : Block n :=
            { sourceBlock with
              passCount := sourceBlock.passCount + 1
              elements := removeLosers sourceBlock.elements matching }
          have sourceUpdatedFloor :
              ∀ (blockId : ℕ) (current : Block n),
                (before.blocks.modify source fun _ =>
                    sourceAfter)[blockId]? = some current →
                  element ∈ current.elements →
                  floor ≤ current.passCount := by
            apply passFloor_modify_fixed before.blocks source sourceBlock
              sourceAfter
              (by simpa [State.block?] using sourceFound)
              element floor
            · intro blockId current currentFound
              exact oldFloor oldClockLow
                blockId current
                (by simpa [State.block?] using currentFound)
            · intro sourceMember
              have originalMember :
                  element ∈ sourceBlock.elements :=
                mem_of_mem_removeLosers sourceMember
              have sourceFloor :=
                oldFloor oldClockLow source sourceBlock sourceFound
                  originalMember
              simp [sourceAfter]
              omega
          exact
            passFloor_insertAtDestinations
              (before.blocks.modify source fun _ => sourceAfter)
              matching element floor sourceUpdatedFloor notLoser
              query block (by simpa [sourceAfter] using found) member
  | split source prefixLength =>
      have oldClockLow : clock element < cutoff := by
        simpa [EpisodeClock.after] using nextClockLow
      cases step.2.1 with
      | split sourceFound sourceShrinking prefixLe blocksEq valuesEq =>
          rename_i sourceBlock
          rw [blocksEq] at found
          unfold splitBlocks at found
          rw [List.getElem?_append] at found
          by_cases old :
              query <
                (before.blocks.modify source fun current =>
                  { current with elements := [] }).length
          · simp only [old, if_pos] at found
            apply
              lookup_modify_preserves before.blocks source
                (fun current => { current with elements := [] })
                (P := fun current =>
                  element ∈ current.elements →
                    floor ≤ current.passCount)
                (by
                  intro blockId current currentFound
                  exact oldFloor oldClockLow
                    blockId current
                    (by simpa [State.block?] using currentFound))
                (by
                  intro current currentOk updatedMember
                  simp at updatedMember)
                query block found member
          · simp only [List.length_modify] at old
            simp only [List.length_modify, old, if_false] at found
            change
              (([{ sourceBlock with
                    elements :=
                      sourceBlock.elements.take prefixLength },
                  { sourceBlock with
                    elements :=
                      sourceBlock.elements.drop prefixLength }] :
                List (Block n)))[query - before.blocks.length]? =
                  some block at found
            have offsetLt :
                query - before.blocks.length < 2 :=
              by
                simpa using
                  (List.getElem?_eq_some_iff.mp found).choose
            have offsetCases :
                query - before.blocks.length = 0 ∨
                  query - before.blocks.length = 1 :=
              Nat.le_one_iff_eq_zero_or_eq_one.mp
                (Nat.le_of_lt_succ offsetLt)
            have sourceFloor :
                floor ≤ sourceBlock.passCount :=
              oldFloor oldClockLow source sourceBlock sourceFound
                (by
                  rcases offsetCases with offset | offset <;>
                    simp [offset] at found <;>
                    subst block
                  · exact List.mem_of_mem_take member
                  · exact List.mem_of_mem_drop member)
            rcases offsetCases with offset | offset <;>
              simp [offset] at found <;>
              subst block <;>
              exact sourceFloor
  | valueChange changed delta =>
      have oldClockLow : clock element < cutoff := by
        simpa [EpisodeClock.after] using nextClockLow
      cases step.2.1 with
      | decrease canDecrease blocksEq valuesEq =>
          exact oldFloor oldClockLow query block
            (by simpa [State.block?, blocksEq] using found) member
      | increase canIncrease blocksEq valuesEq =>
          exact oldFloor oldClockLow query block
            (by simpa [State.block?, blocksEq] using found) member

namespace AnnotatedPairShiftSnapshot

/-- Canonical annotation of one pairing in an exact legal pass. -/
noncomputable def ofLifetimePass
    {n : ℕ} {params : Parameters}
    {before after : State n} {labels : RootLabels}
    {ledger : EpisodeLedger n} {source : BlockId}
    {matching : List (Pairing n)} {pairing : Pairing n}
    (exact : EpisodeLedger.ExactAt before labels ledger)
    (step : Step params before (.pass source matching) after)
    (aligned : labels.length = before.blocks.length)
    (pairingMem : pairing ∈ matching) :
    AnnotatedPairShiftSnapshot n :=
  let starts :=
    exact.pass_pairing_starts step aligned pairingMem
  { snapshot :=
      PairShiftSnapshot.ofEpisodeStarts before pairing
        starts.winnerStart starts.loserStart starts.winnerJoinValid
    sourceRoot := starts.sourceRoot
    source := source
    sourcePassCount := starts.sourceBlock.passCount
    sourceCreator := starts.sourceBlock.creator
    winner := pairing.winner
    loser := pairing.loser
    winnerStart := starts.winnerStart
    loserStart := starts.loserStart }

/-- The annotation's underlying snapshot is the canonical lifetime snapshot. -/
@[simp]
theorem snapshot_ofLifetimePass
    {n : ℕ} {params : Parameters}
    {before after : State n} {labels : RootLabels}
    {ledger : EpisodeLedger n} {source : BlockId}
    {matching : List (Pairing n)} {pairing : Pairing n}
    (exact : EpisodeLedger.ExactAt before labels ledger)
    (step : Step params before (.pass source matching) after)
    (aligned : labels.length = before.blocks.length)
    (pairingMem : pairing ∈ matching) :
    (ofLifetimePass exact step aligned pairingMem).snapshot =
      PairShiftSnapshot.ofLifetimePass exact step aligned pairingMem :=
  rfl

/-- Exact source lookup facts retained by the annotation. -/
theorem source_lookup_ofLifetimePass
    {n : ℕ} {params : Parameters}
    {before after : State n} {labels : RootLabels}
    {ledger : EpisodeLedger n} {source : BlockId}
    {matching : List (Pairing n)} {pairing : Pairing n}
    (exact : EpisodeLedger.ExactAt before labels ledger)
    (step : Step params before (.pass source matching) after)
    (aligned : labels.length = before.blocks.length)
    (pairingMem : pairing ∈ matching) :
    ∃ sourceBlock,
      before.block? source = some sourceBlock ∧
        RootLabels.root? labels source =
          some (ofLifetimePass exact step aligned pairingMem).sourceRoot ∧
        sourceBlock.passCount =
          (ofLifetimePass exact step aligned pairingMem).sourcePassCount ∧
        sourceBlock.creator =
          (ofLifetimePass exact step aligned pairingMem).sourceCreator ∧
        (ofLifetimePass exact step aligned pairingMem).source = source ∧
        (ofLifetimePass exact step aligned pairingMem).winner =
          pairing.winner ∧
        (ofLifetimePass exact step aligned pairingMem).loser =
          pairing.loser := by
  let starts :=
    exact.pass_pairing_starts step aligned pairingMem
  exact
    ⟨starts.sourceBlock, starts.sourceFound, starts.sourceRootFound,
      rfl, rfl, rfl, rfl, rfl⟩

/-- Immediately after a pass, its winner lies above the consumed source count. -/
theorem passFloorAt_winner_after_ofLifetimePass
    {n : ℕ} {params : Parameters}
    {before after : State n} {labels : RootLabels}
    {ledger : EpisodeLedger n} {source : BlockId}
    {matching : List (Pairing n)} {pairing : Pairing n}
    (exact : EpisodeLedger.ExactAt before labels ledger)
    (step : Step params before (.pass source matching) after)
    (aligned : labels.length = before.blocks.length)
    (pairingMem : pairing ∈ matching) :
    PassFloorAt after pairing.winner
      ((ofLifetimePass exact step aligned pairingMem).sourcePassCount + 1) := by
  let starts :=
    exact.pass_pairing_starts step aligned pairingMem
  obtain ⟨actualSource, actualFound, validMatching⟩ :
      ∃ sourceBlock,
        before.block? source = some sourceBlock ∧
          MatchingValid params before source sourceBlock matching := by
    cases step.2.1 with
    | pass found validMatching blocksEq valuesEq =>
        exact ⟨_, found, validMatching⟩
  have sourceEq : actualSource = starts.sourceBlock := by
    rw [starts.sourceFound] at actualFound
    exact Option.some.inj actualFound.symm
  subst actualSource
  have winnerMem : pairing.winner ∈ starts.sourceBlock.elements :=
    (validMatching.2.2.2.1 pairing pairingMem).1.first_mem
  have winnerNotLoser :
      pairing.winner ∉ pairingLosers matching :=
    pairingWinner_not_mem_pairingLosers validMatching.2.1 pairingMem
  have winnerAfterMem :
      pairing.winner ∈
        removeLosers starts.sourceBlock.elements matching :=
    mem_removeLosers_of_mem_of_not_loser winnerMem winnerNotLoser
  obtain ⟨sourceBefore, sourceBeforeFound, sourceAfterFound⟩ :=
    step.2.1.pass_source?
  have sourceBeforeEq : sourceBefore = starts.sourceBlock := by
    rw [starts.sourceFound] at sourceBeforeFound
    exact Option.some.inj sourceBeforeFound.symm
  subst sourceBefore
  intro blockId block blockFound blockMember
  have blockIdEq : blockId = source :=
    step.2.2.blockId_eq_of_element_mem
      blockFound blockMember sourceAfterFound winnerAfterMem
  subst blockId
  rw [sourceAfterFound] at blockFound
  have blockEq :
      block =
        { starts.sourceBlock with
          passCount := starts.sourceBlock.passCount + 1
          elements :=
            removeLosers starts.sourceBlock.elements matching } :=
    Option.some.inj blockFound.symm
  subst block
  rfl

/-- Both retained episode starts currently occupy this common source lineage. -/
theorem episode_facts_ofLifetimePass
    {n : ℕ} {params : Parameters}
    {before after : State n} {labels : RootLabels}
    {ledger : EpisodeLedger n} {source : BlockId}
    {matching : List (Pairing n)} {pairing : Pairing n}
    (exact : EpisodeLedger.ExactAt before labels ledger)
    (step : Step params before (.pass source matching) after)
    (aligned : labels.length = before.blocks.length)
    (pairingMem : pairing ∈ matching) :
    let annotated := ofLifetimePass exact step aligned pairingMem
    ledger pairing.winner = some annotated.winnerStart ∧
      ledger pairing.loser = some annotated.loserStart ∧
      annotated.winnerStart.join.destinationRoot =
        annotated.sourceRoot ∧
      annotated.loserStart.join.destinationRoot =
        annotated.sourceRoot ∧
      annotated.winnerStart.join.destinationCreator =
        annotated.sourceCreator ∧
      annotated.loserStart.join.destinationCreator =
        annotated.sourceCreator := by
  let starts :=
    exact.pass_pairing_starts step aligned pairingMem
  exact
    ⟨starts.winnerActive, starts.loserActive,
      starts.winnerRoot, starts.loserRoot,
      starts.winnerCreator, starts.loserCreator⟩

end AnnotatedPairShiftSnapshot

/--
An annotated pass snapshot with the value-change event clock at both episode
starts and the exact event prefix immediately before the pass.
-/
structure TimedAnnotatedPairShiftSnapshot (n : ℕ) where
  annotated : AnnotatedPairShiftSnapshot n
  winnerStartEvent : ℕ
  loserStartEvent : ℕ
  eventsBefore : List (ValueChangeEvent n)

namespace TimedAnnotatedPairShiftSnapshot

/-- Canonical timed annotation of one exact pass pairing. -/
noncomputable def ofLifetimePass
    {n : ℕ} {params : Parameters}
    {before after : State n} {labels : RootLabels}
    {ledger : EpisodeLedger n} {source : BlockId}
    {matching : List (Pairing n)} {pairing : Pairing n}
    (clock : EpisodeClock n) (events : List (ValueChangeEvent n))
    (exact : EpisodeLedger.ExactAt before labels ledger)
    (step : Step params before (.pass source matching) after)
    (aligned : labels.length = before.blocks.length)
    (pairingMem : pairing ∈ matching) :
    TimedAnnotatedPairShiftSnapshot n :=
  { annotated :=
      AnnotatedPairShiftSnapshot.ofLifetimePass
        exact step aligned pairingMem
    winnerStartEvent := clock pairing.winner
    loserStartEvent := clock pairing.loser
    eventsBefore := events }

/-- Oriented winner-value interval of one timed snapshot. -/
def vTemporalCharge {n : ℕ}
    (finalEvents : List (ValueChangeEvent n))
    (timed : TimedAnnotatedPairShiftSnapshot n) :
    TemporalCharge finalEvents.length :=
  fun event =>
    -eventIntervalCharge finalEvents
      (ValueChangeEvent.isFor timed.annotated.winner)
      timed.winnerStartEvent timed.eventsBefore.length event

/-- Difference of the two source-creator intervals of one timed snapshot. -/
def uTemporalCharge {n : ℕ}
    (finalEvents : List (ValueChangeEvent n))
    (timed : TimedAnnotatedPairShiftSnapshot n) :
    TemporalCharge finalEvents.length :=
  fun event =>
    eventIntervalCharge finalEvents
        (ValueChangeEvent.isFor timed.annotated.sourceCreator)
        timed.winnerStartEvent timed.eventsBefore.length event -
      eventIntervalCharge finalEvents
        (ValueChangeEvent.isFor timed.annotated.sourceCreator)
        timed.loserStartEvent timed.eventsBefore.length event

/-- A winner interval has coefficient magnitude at most one. -/
theorem abs_vTemporalCharge_le_one {n : ℕ}
    (finalEvents : List (ValueChangeEvent n))
    (timed : TimedAnnotatedPairShiftSnapshot n)
    (event : Fin finalEvents.length) :
    |timed.vTemporalCharge finalEvents event| ≤ 1 := by
  unfold vTemporalCharge eventIntervalCharge
  split <;> norm_num

/-- A difference of two creator intervals still has magnitude at most one. -/
theorem abs_uTemporalCharge_le_one {n : ℕ}
    (finalEvents : List (ValueChangeEvent n))
    (timed : TimedAnnotatedPairShiftSnapshot n)
    (event : Fin finalEvents.length) :
    |timed.uTemporalCharge finalEvents event| ≤ 1 := by
  unfold uTemporalCharge eventIntervalCharge
  split <;> split <;> norm_num

end TimedAnnotatedPairShiftSnapshot

open TimedAnnotatedPairShiftSnapshot

/-- Timed snapshots selected by the same inherited-counter predicate. -/
def significantTimedSnapshots {n : ℕ}
    (threshold : ℕ)
    (snapshots : List (TimedAnnotatedPairShiftSnapshot n)) :
    List (TimedAnnotatedPairShiftSnapshot n) :=
  snapshots.filter fun timed =>
    AnnotatedPairShiftSnapshot.significantDecision
      threshold timed.annotated

/-- Forgetting clocks commutes with significant filtering. -/
@[simp]
theorem map_annotated_significantTimedSnapshots {n : ℕ}
    (threshold : ℕ)
    (snapshots : List (TimedAnnotatedPairShiftSnapshot n)) :
    (significantTimedSnapshots threshold snapshots).map
        TimedAnnotatedPairShiftSnapshot.annotated =
      significantAnnotatedSnapshots threshold
        (snapshots.map TimedAnnotatedPairShiftSnapshot.annotated) := by
  induction snapshots with
  | nil =>
      rfl
  | cons timed snapshots ih =>
      unfold significantTimedSnapshots significantAnnotatedSnapshots at ih ⊢
      simp only [List.filter_cons, List.map_cons]
      split <;> simp_all

/-- Timed snapshots whose winner interval contains one fixed event. -/
def vIncidentTimedSnapshots {n : ℕ}
    (finalEvents : List (ValueChangeEvent n))
    (event : Fin finalEvents.length)
    (snapshots : List (TimedAnnotatedPairShiftSnapshot n)) :
    List (TimedAnnotatedPairShiftSnapshot n) :=
  snapshots.filter fun timed =>
    decide (timed.vTemporalCharge finalEvents event ≠ 0)

/-- Timed snapshots whose creator-interval difference contains one event. -/
def uIncidentTimedSnapshots {n : ℕ}
    (finalEvents : List (ValueChangeEvent n))
    (event : Fin finalEvents.length)
    (snapshots : List (TimedAnnotatedPairShiftSnapshot n)) :
    List (TimedAnnotatedPairShiftSnapshot n) :=
  snapshots.filter fun timed =>
    decide (timed.uTemporalCharge finalEvents event ≠ 0)

/-- Every snapshot in a v-column has the event's changed element as winner. -/
theorem winner_eq_eventElement_of_mem_vIncidentTimedSnapshots
    {n : ℕ} {finalEvents : List (ValueChangeEvent n)}
    {event : Fin finalEvents.length}
    {snapshots : List (TimedAnnotatedPairShiftSnapshot n)}
    {timed : TimedAnnotatedPairShiftSnapshot n}
    (member :
      timed ∈
        vIncidentTimedSnapshots finalEvents event snapshots) :
    timed.annotated.winner = (finalEvents.get event).element := by
  have nonzero := (List.mem_filter.mp member).2
  simp [vTemporalCharge, eventIntervalCharge,
    ValueChangeEvent.isFor] at nonzero
  exact nonzero.2.2.symm

/-- Membership in a v-column exposes the exact half-open event interval. -/
theorem start_le_event_lt_end_of_mem_vIncidentTimedSnapshots
    {n : ℕ} {finalEvents : List (ValueChangeEvent n)}
    {event : Fin finalEvents.length}
    {snapshots : List (TimedAnnotatedPairShiftSnapshot n)}
    {timed : TimedAnnotatedPairShiftSnapshot n}
    (member :
      timed ∈
        vIncidentTimedSnapshots finalEvents event snapshots) :
    timed.winnerStartEvent ≤ event.val ∧
      event.val < timed.eventsBefore.length := by
  have nonzero := (List.mem_filter.mp member).2
  simp [vTemporalCharge, eventIntervalCharge,
    ValueChangeEvent.isFor] at nonzero
  exact ⟨nonzero.1, nonzero.2.1⟩

private theorem length_le_one_of_map_nodup_of_constant
    {α β : Type*} [DecidableEq β]
    (values : List α) (project : α → β) (constant : β)
    (nodup : (values.map project).Nodup)
    (all : ∀ value ∈ values, project value = constant) :
    values.length ≤ 1 := by
  cases values with
  | nil =>
      simp
  | cons value values =>
      have tailEmpty : values = [] := by
        by_contra nonempty
        obtain ⟨later, laterMem⟩ :=
          List.exists_mem_of_ne_nil values nonempty
        have headEq := all value (by simp)
        have laterEq := all later (by simp [laterMem])
        have mappedNodup :
            (project value :: values.map project).Nodup := by
          simpa only [List.map_cons] using nodup
        have fresh := (List.nodup_cons.mp mappedNodup).1
        apply fresh
        apply List.mem_map.mpr
        exact ⟨later, laterMem, by simpa [headEq, laterEq]⟩
      subst values
      simp

private theorem abs_eq_one_of_ne_zero_of_abs_le_one
    (value : ℤ) (nonzero : value ≠ 0) (bound : |value| ≤ 1) :
    |value| = 1 := by
  have nonnegative : 0 ≤ |value| := abs_nonneg value
  have absNonzero : |value| ≠ 0 := abs_ne_zero.mpr nonzero
  omega

/-- Absolute winner-column weight is exactly the number of incident snapshots. -/
theorem sum_abs_vTemporalCharge_eq_incident_length {n : ℕ}
    (finalEvents : List (ValueChangeEvent n))
    (event : Fin finalEvents.length)
    (snapshots : List (TimedAnnotatedPairShiftSnapshot n)) :
    (snapshots.map fun timed =>
        |timed.vTemporalCharge finalEvents event|).sum =
      ((vIncidentTimedSnapshots finalEvents event snapshots).length : ℤ) := by
  induction snapshots with
  | nil =>
      rfl
  | cons timed snapshots ih =>
      by_cases nonzero :
          timed.vTemporalCharge finalEvents event ≠ 0
      · have unit :
            |timed.vTemporalCharge finalEvents event| = 1 :=
          abs_eq_one_of_ne_zero_of_abs_le_one _ nonzero
            (timed.abs_vTemporalCharge_le_one finalEvents event)
        simp [vIncidentTimedSnapshots, nonzero, unit, ih, add_comm]
      · have zero :
            timed.vTemporalCharge finalEvents event = 0 :=
          not_ne_iff.mp nonzero
        simp [vIncidentTimedSnapshots, zero, ih]

/-- Absolute creator-column weight is exactly the number of incident snapshots. -/
theorem sum_abs_uTemporalCharge_eq_incident_length {n : ℕ}
    (finalEvents : List (ValueChangeEvent n))
    (event : Fin finalEvents.length)
    (snapshots : List (TimedAnnotatedPairShiftSnapshot n)) :
    (snapshots.map fun timed =>
        |timed.uTemporalCharge finalEvents event|).sum =
      ((uIncidentTimedSnapshots finalEvents event snapshots).length : ℤ) := by
  induction snapshots with
  | nil =>
      rfl
  | cons timed snapshots ih =>
      by_cases nonzero :
          timed.uTemporalCharge finalEvents event ≠ 0
      · have unit :
            |timed.uTemporalCharge finalEvents event| = 1 :=
          abs_eq_one_of_ne_zero_of_abs_le_one _ nonzero
            (timed.abs_uTemporalCharge_le_one finalEvents event)
        simp [uIncidentTimedSnapshots, nonzero, unit, ih, add_comm]
      · have zero :
            timed.uTemporalCharge finalEvents event = 0 :=
          not_ne_iff.mp nonzero
        simp [uIncidentTimedSnapshots, zero, ih]

/--
Distinct inherited counters below `τ` give the sharp `τ` bound on a finite
snapshot family.
-/
theorem snapshots_length_le_threshold_of_passCounts_nodup
    {n threshold : ℕ}
    (snapshots : List (TimedAnnotatedPairShiftSnapshot n))
    (significant :
      ∀ timed ∈ snapshots,
        timed.annotated.sourcePassCount < threshold)
    (countsNodup :
      (snapshots.map fun timed =>
        timed.annotated.sourcePassCount).Nodup) :
    snapshots.length ≤ threshold := by
  let counts :=
    snapshots.map fun timed => timed.annotated.sourcePassCount
  have subset :
      counts.toFinset ⊆ Finset.range threshold := by
    intro count member
    have countMem : count ∈ counts := by
      simpa using member
    obtain ⟨timed, timedMem, countEq⟩ :=
      List.mem_map.mp countMem
    subst count
    exact Finset.mem_range.mpr (significant timed timedMem)
  calc
    snapshots.length = counts.length := by
      simp [counts]
    _ = counts.toFinset.card :=
      (List.toFinset_card_of_nodup countsNodup).symm
    _ ≤ (Finset.range threshold).card :=
      Finset.card_le_card subset
    _ = threshold :=
      Finset.card_range threshold

/-- Significant v-incidence is bounded once its inherited counters are unique. -/
theorem vIncident_length_le_of_passCounts_nodup
    {n threshold : ℕ}
    (finalEvents : List (ValueChangeEvent n))
    (event : Fin finalEvents.length)
    (snapshots : List (TimedAnnotatedPairShiftSnapshot n))
    (countsNodup :
      ((vIncidentTimedSnapshots finalEvents event
          (significantTimedSnapshots threshold snapshots)).map fun timed =>
        timed.annotated.sourcePassCount).Nodup) :
    (vIncidentTimedSnapshots finalEvents event
        (significantTimedSnapshots threshold snapshots)).length ≤
      threshold := by
  apply snapshots_length_le_threshold_of_passCounts_nodup _ _ countsNodup
  intro timed member
  have significantMember :
      timed ∈ significantTimedSnapshots threshold snapshots :=
    (List.mem_filter.mp member).1
  simpa [AnnotatedPairShiftSnapshot.significantDecision] using
    (List.mem_filter.mp significantMember).2

/--
Distinct `(root, passCount)` keys below `τ`, supported on at most `g` roots,
give the product bound `g * τ`.
-/
theorem snapshots_length_le_growing_mul_threshold_of_runKeys_nodup
    {n threshold growingLimit : ℕ}
    (snapshots : List (TimedAnnotatedPairShiftSnapshot n))
    (significant :
      ∀ timed ∈ snapshots,
        timed.annotated.sourcePassCount < threshold)
    (keysNodup :
      (snapshots.map fun timed =>
        (timed.annotated.sourceRoot,
          timed.annotated.sourcePassCount)).Nodup)
    (rootsBound :
      (snapshots.map fun timed =>
        timed.annotated.sourceRoot).toFinset.card ≤ growingLimit) :
    snapshots.length ≤ growingLimit * threshold := by
  let keys :=
    snapshots.map fun timed =>
      (timed.annotated.sourceRoot,
        timed.annotated.sourcePassCount)
  let roots :=
    (snapshots.map fun timed =>
      timed.annotated.sourceRoot).toFinset
  have subset :
      keys.toFinset ⊆ roots.product (Finset.range threshold) := by
    intro key member
    have keyMem : key ∈ keys := by
      simpa using member
    obtain ⟨timed, timedMem, keyEq⟩ :=
      List.mem_map.mp keyMem
    subst key
    apply Finset.mem_product.mpr
    constructor
    · change
        timed.annotated.sourceRoot ∈
          (snapshots.map fun current =>
            current.annotated.sourceRoot).toFinset
      simpa only [List.mem_toFinset] using
        (List.mem_map.mpr
          ⟨timed, timedMem, rfl⟩)
    · exact Finset.mem_range.mpr (significant timed timedMem)
  calc
    snapshots.length = keys.length := by
      simp [keys]
    _ = keys.toFinset.card :=
      (List.toFinset_card_of_nodup keysNodup).symm
    _ ≤ (roots.product (Finset.range threshold)).card :=
      Finset.card_le_card subset
    _ = roots.card * threshold := by
      simp
    _ ≤ growingLimit * threshold :=
      Nat.mul_le_mul_right threshold rootsBound

/--
Significant u-incidence is bounded by root/count uniqueness and the number of
roots represented in the event column.
-/
theorem uIncident_length_le_of_runKeys_nodup
    {n threshold growingLimit : ℕ}
    (finalEvents : List (ValueChangeEvent n))
    (event : Fin finalEvents.length)
    (snapshots : List (TimedAnnotatedPairShiftSnapshot n))
    (keysNodup :
      ((uIncidentTimedSnapshots finalEvents event
          (significantTimedSnapshots threshold snapshots)).map fun timed =>
        (timed.annotated.sourceRoot,
          timed.annotated.sourcePassCount)).Nodup)
    (rootsBound :
      ((uIncidentTimedSnapshots finalEvents event
          (significantTimedSnapshots threshold snapshots)).map fun timed =>
        timed.annotated.sourceRoot).toFinset.card ≤ growingLimit) :
    (uIncidentTimedSnapshots finalEvents event
        (significantTimedSnapshots threshold snapshots)).length ≤
      growingLimit * threshold := by
  apply
    snapshots_length_le_growing_mul_threshold_of_runKeys_nodup
      _ _ keysNodup rootsBound
  intro timed member
  have significantMember :
      timed ∈ significantTimedSnapshots threshold snapshots :=
    (List.mem_filter.mp member).1
  simpa [AnnotatedPairShiftSnapshot.significantDecision] using
    (List.mem_filter.mp significantMember).2

namespace TimedAnnotatedPairShiftSnapshot

/-- The winner's `v`-shift is its exact oriented post-join event interval. -/
theorem vShift_eq_eventDrift
    {n : ℕ} {params : Parameters}
    {before after : State n} {labels : RootLabels}
    {ledger : EpisodeLedger n} {source : BlockId}
    {matching : List (Pairing n)} {pairing : Pairing n}
    (clock : EpisodeClock n) (events : List (ValueChangeEvent n))
    (exact : EpisodeLedger.ExactAt before labels ledger)
    (clockSound : EpisodeClock.SoundAt before ledger clock events)
    (step : Step params before (.pass source matching) after)
    (aligned : labels.length = before.blocks.length)
    (pairingMem : pairing ∈ matching) :
    let timed :=
      ofLifetimePass clock events exact step aligned pairingMem
    timed.annotated.snapshot.vShift =
      -eventDrift pairing.winner
        (events.drop timed.winnerStartEvent) := by
  let starts :=
    exact.pass_pairing_starts step aligned pairingMem
  have winnerClock :=
    clockSound pairing.winner starts.winnerStart starts.winnerActive
  change
    (starts.winnerStart.join.valueAtJoin : ℤ) -
        (before.value pairing.winner : ℤ) =
      -eventDrift pairing.winner
        (events.drop (clock pairing.winner))
  rw [winnerClock.2.1]
  ring

/--
The `u`-shift is the difference of the two exact source-creator event suffixes.
-/
theorem uShift_eq_eventDrifts
    {n : ℕ} {params : Parameters}
    {before after : State n} {labels : RootLabels}
    {ledger : EpisodeLedger n} {source : BlockId}
    {matching : List (Pairing n)} {pairing : Pairing n}
    (clock : EpisodeClock n) (events : List (ValueChangeEvent n))
    (exact : EpisodeLedger.ExactAt before labels ledger)
    (clockSound : EpisodeClock.SoundAt before ledger clock events)
    (step : Step params before (.pass source matching) after)
    (aligned : labels.length = before.blocks.length)
    (pairingMem : pairing ∈ matching) :
    let timed :=
      ofLifetimePass clock events exact step aligned pairingMem
    timed.annotated.snapshot.uShift =
      eventDrift timed.annotated.sourceCreator
          (events.drop timed.winnerStartEvent) -
        eventDrift timed.annotated.sourceCreator
          (events.drop timed.loserStartEvent) := by
  let starts :=
    exact.pass_pairing_starts step aligned pairingMem
  have winnerClock :=
    clockSound pairing.winner starts.winnerStart starts.winnerActive
  have loserClock :=
    clockSound pairing.loser starts.loserStart starts.loserActive
  have winnerCreator :
      starts.winnerStart.join.destinationCreator =
        starts.sourceBlock.creator :=
    starts.winnerCreator
  have loserCreator :
      starts.loserStart.join.destinationCreator =
        starts.sourceBlock.creator :=
    starts.loserCreator
  have commonValue :
      (starts.winnerStart.creatorValueAtJoin : ℤ) +
          eventDrift starts.sourceBlock.creator
            (events.drop (clock pairing.winner)) =
        (starts.loserStart.creatorValueAtJoin : ℤ) +
          eventDrift starts.sourceBlock.creator
            (events.drop (clock pairing.loser)) := by
    calc
      (starts.winnerStart.creatorValueAtJoin : ℤ) +
            eventDrift starts.sourceBlock.creator
              (events.drop (clock pairing.winner)) =
          (before.value starts.sourceBlock.creator : ℤ) := by
            have current := winnerClock.2.2
            rw [winnerCreator] at current
            exact current.symm
      _ =
          (starts.loserStart.creatorValueAtJoin : ℤ) +
            eventDrift starts.sourceBlock.creator
              (events.drop (clock pairing.loser)) := by
            have current := loserClock.2.2
            rw [loserCreator] at current
            exact current
  change
    (starts.loserStart.creatorValueAtJoin : ℤ) -
        (starts.winnerStart.creatorValueAtJoin : ℤ) =
      eventDrift starts.sourceBlock.creator
          (events.drop (clock pairing.winner)) -
        eventDrift starts.sourceBlock.creator
          (events.drop (clock pairing.loser))
  omega

/-- The canonical winner shift is the dot product with its final-event charge. -/
theorem vShift_eq_temporalCharge
    {n : ℕ} {params : Parameters}
    {before after : State n} {labels : RootLabels}
    {ledger : EpisodeLedger n} {source : BlockId}
    {matching : List (Pairing n)} {pairing : Pairing n}
    (clock : EpisodeClock n) (events finalEvents :
      List (ValueChangeEvent n))
    (exact : EpisodeLedger.ExactAt before labels ledger)
    (clockSound : EpisodeClock.SoundAt before ledger clock events)
    (step : Step params before (.pass source matching) after)
    (aligned : labels.length = before.blocks.length)
    (pairingMem : pairing ∈ matching)
    (eventsPrefix : events <+: finalEvents) :
    let timed :=
      ofLifetimePass clock events exact step aligned pairingMem
    timed.annotated.snapshot.vShift =
      temporalShift (valueChangeDeltaVector finalEvents)
        (vTemporalCharge finalEvents timed) := by
  let timed :=
    ofLifetimePass clock events exact step aligned pairingMem
  let starts :=
    exact.pass_pairing_starts step aligned pairingMem
  have startLe :
      clock pairing.winner ≤ events.length :=
    (clockSound pairing.winner starts.winnerStart
      starts.winnerActive).1
  have stopLe : events.length ≤ finalEvents.length :=
    eventsPrefix.length_le
  obtain ⟨suffix, prefixEq⟩ := eventsPrefix
  have takeEq :
      finalEvents.take events.length = events := by
    rw [← prefixEq]
    simp
  have interval :=
    temporalShift_valueChange_interval finalEvents pairing.winner
      (clock pairing.winner) events.length startLe stopLe
  rw [takeEq] at interval
  have shiftEq :
      timed.annotated.snapshot.vShift =
        -eventDrift pairing.winner
          (events.drop (clock pairing.winner)) := by
    simpa [timed, ofLifetimePass] using
      vShift_eq_eventDrift clock events exact clockSound step aligned
        pairingMem
  calc
    timed.annotated.snapshot.vShift =
        -eventDrift pairing.winner
          (events.drop (clock pairing.winner)) :=
      shiftEq
    _ =
        -temporalShift (valueChangeDeltaVector finalEvents)
          (eventIntervalCharge finalEvents
            (ValueChangeEvent.isFor pairing.winner)
            (clock pairing.winner) events.length) := by
      rw [interval]
    _ =
        temporalShift (valueChangeDeltaVector finalEvents)
          (vTemporalCharge finalEvents timed) := by
      rw [show
        vTemporalCharge finalEvents timed =
          fun event =>
            -eventIntervalCharge finalEvents
              (ValueChangeEvent.isFor pairing.winner)
              (clock pairing.winner) events.length event by
        rfl]
      exact
        (temporalShift_neg_charge
          (valueChangeDeltaVector finalEvents)
          (eventIntervalCharge finalEvents
            (ValueChangeEvent.isFor pairing.winner)
            (clock pairing.winner) events.length)).symm

/-- The canonical creator shift is the dot product with its difference charge. -/
theorem uShift_eq_temporalCharge
    {n : ℕ} {params : Parameters}
    {before after : State n} {labels : RootLabels}
    {ledger : EpisodeLedger n} {source : BlockId}
    {matching : List (Pairing n)} {pairing : Pairing n}
    (clock : EpisodeClock n) (events finalEvents :
      List (ValueChangeEvent n))
    (exact : EpisodeLedger.ExactAt before labels ledger)
    (clockSound : EpisodeClock.SoundAt before ledger clock events)
    (step : Step params before (.pass source matching) after)
    (aligned : labels.length = before.blocks.length)
    (pairingMem : pairing ∈ matching)
    (eventsPrefix : events <+: finalEvents) :
    let timed :=
      ofLifetimePass clock events exact step aligned pairingMem
    timed.annotated.snapshot.uShift =
      temporalShift (valueChangeDeltaVector finalEvents)
        (uTemporalCharge finalEvents timed) := by
  let timed :=
    ofLifetimePass clock events exact step aligned pairingMem
  let starts :=
    exact.pass_pairing_starts step aligned pairingMem
  have winnerStartLe :
      clock pairing.winner ≤ events.length :=
    (clockSound pairing.winner starts.winnerStart
      starts.winnerActive).1
  have loserStartLe :
      clock pairing.loser ≤ events.length :=
    (clockSound pairing.loser starts.loserStart
      starts.loserActive).1
  have stopLe : events.length ≤ finalEvents.length :=
    eventsPrefix.length_le
  obtain ⟨suffix, prefixEq⟩ := eventsPrefix
  have takeEq :
      finalEvents.take events.length = events := by
    rw [← prefixEq]
    simp
  have winnerInterval :=
    temporalShift_valueChange_interval finalEvents
      timed.annotated.sourceCreator
      (clock pairing.winner) events.length winnerStartLe stopLe
  have loserInterval :=
    temporalShift_valueChange_interval finalEvents
      timed.annotated.sourceCreator
      (clock pairing.loser) events.length loserStartLe stopLe
  rw [takeEq] at winnerInterval loserInterval
  have shiftEq :
      timed.annotated.snapshot.uShift =
        eventDrift timed.annotated.sourceCreator
            (events.drop (clock pairing.winner)) -
          eventDrift timed.annotated.sourceCreator
            (events.drop (clock pairing.loser)) := by
    simpa [timed, ofLifetimePass] using
      uShift_eq_eventDrifts clock events exact clockSound step aligned
        pairingMem
  calc
    timed.annotated.snapshot.uShift =
        eventDrift timed.annotated.sourceCreator
            (events.drop (clock pairing.winner)) -
          eventDrift timed.annotated.sourceCreator
            (events.drop (clock pairing.loser)) :=
      shiftEq
    _ =
        temporalShift (valueChangeDeltaVector finalEvents)
              (eventIntervalCharge finalEvents
                (ValueChangeEvent.isFor timed.annotated.sourceCreator)
                (clock pairing.winner) events.length) -
          temporalShift (valueChangeDeltaVector finalEvents)
              (eventIntervalCharge finalEvents
                (ValueChangeEvent.isFor timed.annotated.sourceCreator)
                (clock pairing.loser) events.length) := by
      rw [winnerInterval, loserInterval]
    _ =
        temporalShift (valueChangeDeltaVector finalEvents)
          (uTemporalCharge finalEvents timed) := by
      rw [show
        uTemporalCharge finalEvents timed =
          fun event =>
            eventIntervalCharge finalEvents
                (ValueChangeEvent.isFor
                  timed.annotated.sourceCreator)
                (clock pairing.winner) events.length event -
              eventIntervalCharge finalEvents
                (ValueChangeEvent.isFor
                  timed.annotated.sourceCreator)
                (clock pairing.loser) events.length event by
        rfl]
      exact
        (temporalShift_sub_charge
          (valueChangeDeltaVector finalEvents)
          (eventIntervalCharge finalEvents
            (ValueChangeEvent.isFor timed.annotated.sourceCreator)
            (clock pairing.winner) events.length)
          (eventIntervalCharge finalEvents
            (ValueChangeEvent.isFor timed.annotated.sourceCreator)
            (clock pairing.loser) events.length)).symm

end TimedAnnotatedPairShiftSnapshot

/-- Timed annotations for every pairing of one exact pass. -/
noncomputable def timedLifetimePassSnapshots
    {n : ℕ} {params : Parameters}
    {before after : State n} {labels : RootLabels}
    {ledger : EpisodeLedger n} {source : BlockId}
    {matching : List (Pairing n)}
    (clock : EpisodeClock n) (events : List (ValueChangeEvent n))
    (exact : EpisodeLedger.ExactAt before labels ledger)
    (step : Step params before (.pass source matching) after)
    (aligned : labels.length = before.blocks.length) :
    List (TimedAnnotatedPairShiftSnapshot n) :=
  matching.attach.map fun pairing =>
    TimedAnnotatedPairShiftSnapshot.ofLifetimePass
      clock events exact step aligned pairing.2

/-- One timed annotation is produced for every pairing. -/
@[simp]
theorem length_timedLifetimePassSnapshots
    {n : ℕ} {params : Parameters}
    {before after : State n} {labels : RootLabels}
    {ledger : EpisodeLedger n} {source : BlockId}
    {matching : List (Pairing n)}
    (clock : EpisodeClock n) (events : List (ValueChangeEvent n))
    (exact : EpisodeLedger.ExactAt before labels ledger)
    (step : Step params before (.pass source matching) after)
    (aligned : labels.length = before.blocks.length) :
    (timedLifetimePassSnapshots clock events exact step aligned).length =
      matching.length := by
  simp [timedLifetimePassSnapshots]

/-- Canonical annotated list for all pairings of one exact pass. -/
noncomputable def annotatedLifetimePassSnapshots
    {n : ℕ} {params : Parameters}
    {before after : State n} {labels : RootLabels}
    {ledger : EpisodeLedger n} {source : BlockId}
    {matching : List (Pairing n)}
    (exact : EpisodeLedger.ExactAt before labels ledger)
    (step : Step params before (.pass source matching) after)
    (aligned : labels.length = before.blocks.length) :
    List (AnnotatedPairShiftSnapshot n) :=
  matching.attach.map fun pairing =>
    AnnotatedPairShiftSnapshot.ofLifetimePass
      exact step aligned pairing.2

/-- Annotation erasure recovers the exact one-pass snapshot list. -/
@[simp]
theorem map_snapshot_annotatedLifetimePassSnapshots
    {n : ℕ} {params : Parameters}
    {before after : State n} {labels : RootLabels}
    {ledger : EpisodeLedger n} {source : BlockId}
    {matching : List (Pairing n)}
    (exact : EpisodeLedger.ExactAt before labels ledger)
    (step : Step params before (.pass source matching) after)
    (aligned : labels.length = before.blocks.length) :
    (annotatedLifetimePassSnapshots exact step aligned).map
        AnnotatedPairShiftSnapshot.snapshot =
      PairShiftSnapshot.lifetimePassSnapshots exact step aligned := by
  simp [annotatedLifetimePassSnapshots,
    PairShiftSnapshot.lifetimePassSnapshots, Function.comp_def]

/-- One annotation is produced for every pairing. -/
@[simp]
theorem length_annotatedLifetimePassSnapshots
    {n : ℕ} {params : Parameters}
    {before after : State n} {labels : RootLabels}
    {ledger : EpisodeLedger n} {source : BlockId}
    {matching : List (Pairing n)}
    (exact : EpisodeLedger.ExactAt before labels ledger)
    (step : Step params before (.pass source matching) after)
    (aligned : labels.length = before.blocks.length) :
    (annotatedLifetimePassSnapshots exact step aligned).length =
      matching.length := by
  simp [annotatedLifetimePassSnapshots]

/-- Every annotation of one pass carries the pass source's actual counter. -/
theorem sourcePassCount_eq_of_mem_annotatedLifetimePassSnapshots
    {n : ℕ} {params : Parameters}
    {before after : State n} {labels : RootLabels}
    {ledger : EpisodeLedger n} {source : BlockId}
    {matching : List (Pairing n)} {sourceBlock : Block n}
    (exact : EpisodeLedger.ExactAt before labels ledger)
    (step : Step params before (.pass source matching) after)
    (aligned : labels.length = before.blocks.length)
    (sourceFound : before.block? source = some sourceBlock)
    {annotated : AnnotatedPairShiftSnapshot n}
    (member :
      annotated ∈
        annotatedLifetimePassSnapshots exact step aligned) :
    annotated.sourcePassCount = sourceBlock.passCount := by
  obtain ⟨attached, attachedMem, annotatedEq⟩ :=
    List.mem_map.mp member
  subst annotated
  obtain ⟨actualSource, actualFound, _rootFound, countEq,
      _creatorEq, _sourceEq, _winnerEq, _loserEq⟩ :=
    AnnotatedPairShiftSnapshot.source_lookup_ofLifetimePass
      exact step aligned attached.2
  have actualSourceEq : actualSource = sourceBlock := by
    rw [sourceFound] at actualFound
    exact Option.some.inj actualFound.symm
  subst actualSource
  exact countEq.symm

/-- Forgetting event times recovers the one-pass annotated snapshot list. -/
@[simp]
theorem map_annotated_timedLifetimePassSnapshots
    {n : ℕ} {params : Parameters}
    {before after : State n} {labels : RootLabels}
    {ledger : EpisodeLedger n} {source : BlockId}
    {matching : List (Pairing n)}
    (clock : EpisodeClock n) (events : List (ValueChangeEvent n))
    (exact : EpisodeLedger.ExactAt before labels ledger)
    (step : Step params before (.pass source matching) after)
    (aligned : labels.length = before.blocks.length) :
    (timedLifetimePassSnapshots clock events exact step aligned).map
        TimedAnnotatedPairShiftSnapshot.annotated =
      annotatedLifetimePassSnapshots exact step aligned := by
  simp [timedLifetimePassSnapshots,
    annotatedLifetimePassSnapshots,
    TimedAnnotatedPairShiftSnapshot.ofLifetimePass,
    Function.comp_def]

/-- Annotated snapshots contributed by one arbitrary exact operation. -/
noncomputable def operationAnnotatedPairShiftSnapshots
    {n : ℕ} {params : Parameters}
    (before after : State n) (labels : RootLabels)
    (ledger : EpisodeLedger n) (operation : Operation n)
    (exact : EpisodeLedger.ExactAt before labels ledger)
    (step : Step params before operation after)
    (aligned : labels.length = before.blocks.length) :
    List (AnnotatedPairShiftSnapshot n) :=
  match operation with
  | .pass _ _ =>
      annotatedLifetimePassSnapshots exact step aligned
  | _ => []

/-- Erasing operation annotations recovers the operation snapshot list. -/
@[simp]
theorem map_snapshot_operationAnnotatedPairShiftSnapshots
    {n : ℕ} {params : Parameters}
    (before after : State n) (labels : RootLabels)
    (ledger : EpisodeLedger n) (operation : Operation n)
    (exact : EpisodeLedger.ExactAt before labels ledger)
    (step : Step params before operation after)
    (aligned : labels.length = before.blocks.length) :
    (operationAnnotatedPairShiftSnapshots before after labels ledger
        operation exact step aligned).map
        AnnotatedPairShiftSnapshot.snapshot =
      operationPairShiftSnapshots before after labels ledger operation
        exact step aligned := by
  cases operation <;>
    simp [operationAnnotatedPairShiftSnapshots,
      operationPairShiftSnapshots]

/-- One operation annotation is produced per unit of pass activity. -/
@[simp]
theorem length_operationAnnotatedPairShiftSnapshots
    {n : ℕ} {params : Parameters}
    (before after : State n) (labels : RootLabels)
    (ledger : EpisodeLedger n) (operation : Operation n)
    (exact : EpisodeLedger.ExactAt before labels ledger)
    (step : Step params before operation after)
    (aligned : labels.length = before.blocks.length) :
    (operationAnnotatedPairShiftSnapshots before after labels ledger
        operation exact step aligned).length =
      operation.activity := by
  cases operation <;>
    simp [operationAnnotatedPairShiftSnapshots, Operation.activity]

/-- Every annotation produced by one operation inherits the frozen-value bound. -/
theorem valuesBound_operationAnnotatedPairShiftSnapshots
    {n : ℕ} {params : Parameters}
    (before after : State n) (labels : RootLabels)
    (ledger : EpisodeLedger n) (operation : Operation n)
    (exact : EpisodeLedger.ExactAt before labels ledger)
    (frozen : EpisodeLedger.FrozenValuesBound params ledger)
    (step : Step params before operation after)
    (aligned : labels.length = before.blocks.length) :
    ∀ annotated ∈
        operationAnnotatedPairShiftSnapshots before after labels ledger
          operation exact step aligned,
      annotated.snapshot.ValuesBound params.valueBound := by
  intro annotated member
  cases operation with
  | convert blockId =>
      simp [operationAnnotatedPairShiftSnapshots] at member
  | create creator =>
      simp [operationAnnotatedPairShiftSnapshots] at member
  | insert blockId element =>
      simp [operationAnnotatedPairShiftSnapshots] at member
  | delete blockId element =>
      simp [operationAnnotatedPairShiftSnapshots] at member
  | @pass source matching =>
      obtain ⟨attached, _attachedMem, annotatedEq⟩ :=
        List.mem_map.mp member
      subst annotated
      simpa using
        PairShiftSnapshot.valuesBound_ofLifetimePass
          exact frozen step aligned attached.2
  | split blockId prefixLength =>
      simp [operationAnnotatedPairShiftSnapshots] at member
  | valueChange element delta =>
      cases delta <;>
        simp [operationAnnotatedPairShiftSnapshots] at member

/--
For one exact operation, the complementary counter filter is exactly the
high-pass-count tail of the canonical activity occurrences.
-/
theorem length_insignificant_operationAnnotatedPairShiftSnapshots
    {n : ℕ} {params : Parameters}
    (threshold : ℕ)
    (before after : State n) (labels : RootLabels)
    (ledger : EpisodeLedger n) (operation : Operation n)
    (exact : EpisodeLedger.ExactAt before labels ledger)
    (step : Step params before operation after)
    (aligned : labels.length = before.blocks.length) :
    (insignificantAnnotatedSnapshots threshold
        (operationAnnotatedPairShiftSnapshots before after labels ledger
          operation exact step aligned)).length =
      tailActivity
        (operationActivityOccurrences before labels operation) threshold := by
  cases operation with
  | convert blockId =>
      rfl
  | create creator =>
      rfl
  | insert blockId element =>
      rfl
  | delete blockId element =>
      rfl
  | @pass source matching =>
      obtain ⟨sourceBlock, sourceFound, _afterFound⟩ :=
        step.2.1.pass_source?
      change
        (insignificantAnnotatedSnapshots threshold
            (annotatedLifetimePassSnapshots exact step aligned)).length =
          tailActivity
            (operationActivityOccurrences before labels
              (.pass source matching)) threshold
      by_cases high : threshold ≤ sourceBlock.passCount
      · have annotationFilter :
            insignificantAnnotatedSnapshots threshold
                (annotatedLifetimePassSnapshots exact step aligned) =
              annotatedLifetimePassSnapshots exact step aligned := by
          apply List.filter_eq_self.mpr
          intro annotated member
          have countEq :=
            sourcePassCount_eq_of_mem_annotatedLifetimePassSnapshots
              exact step aligned sourceFound member
          simp [AnnotatedPairShiftSnapshot.significantDecision,
            countEq, high]
        rw [annotationFilter]
        simp [tailActivity, operationActivityOccurrences, sourceFound]
        rw [List.filter_map]
        simp [Function.comp_def, high]
      · have low : sourceBlock.passCount < threshold :=
          Nat.lt_of_not_ge high
        have annotationFilter :
            insignificantAnnotatedSnapshots threshold
                (annotatedLifetimePassSnapshots exact step aligned) =
              [] := by
          apply List.filter_eq_nil_iff.mpr
          intro annotated member
          have countEq :=
            sourcePassCount_eq_of_mem_annotatedLifetimePassSnapshots
              exact step aligned sourceFound member
          simp [AnnotatedPairShiftSnapshot.significantDecision,
            countEq, low]
        rw [annotationFilter]
        simp [tailActivity, operationActivityOccurrences, sourceFound]
        rw [List.filter_map]
        simp [Function.comp_def, high]
  | split blockId prefixLength =>
      rfl
  | valueChange element delta =>
      cases delta <;> rfl

/-- Plain pair snapshots selected by the significant counter predicate. -/
def significantPairShiftSnapshots {n : ℕ}
    (threshold : ℕ) (snapshots : List (AnnotatedPairShiftSnapshot n)) :
    List PairShiftSnapshot :=
  (significantAnnotatedSnapshots threshold snapshots).map
    AnnotatedPairShiftSnapshot.snapshot

/-- Plain pair snapshots in the complementary insignificant class. -/
def insignificantPairShiftSnapshots {n : ℕ}
    (threshold : ℕ) (snapshots : List (AnnotatedPairShiftSnapshot n)) :
    List PairShiftSnapshot :=
  (insignificantAnnotatedSnapshots threshold snapshots).map
    AnnotatedPairShiftSnapshot.snapshot

/-- The counter classification is an exact annotated-list permutation. -/
theorem perm_significant_append_insignificant {n : ℕ}
    (threshold : ℕ) (snapshots : List (AnnotatedPairShiftSnapshot n)) :
    snapshots.Perm
      (significantAnnotatedSnapshots threshold snapshots ++
        insignificantAnnotatedSnapshots threshold snapshots) := by
  simpa [significantAnnotatedSnapshots,
    insignificantAnnotatedSnapshots] using
    List.perm_filter_append_filter_not
      (AnnotatedPairShiftSnapshot.significantDecision threshold)
      snapshots

/-- Erasing annotations preserves the exact significance partition. -/
theorem perm_map_snapshot_significance {n : ℕ}
    (threshold : ℕ) (snapshots : List (AnnotatedPairShiftSnapshot n)) :
    (snapshots.map AnnotatedPairShiftSnapshot.snapshot).Perm
      (significantPairShiftSnapshots threshold snapshots ++
        insignificantPairShiftSnapshots threshold snapshots) := by
  have mapped :=
    (perm_significant_append_insignificant threshold snapshots).map
      AnnotatedPairShiftSnapshot.snapshot
  simpa [significantPairShiftSnapshots,
    insignificantPairShiftSnapshots, List.map_append] using mapped

/-- Exact semantic membership criterion for the significant sublist. -/
theorem mem_significantAnnotatedSnapshots_iff
    {n : ℕ} {threshold : ℕ}
    {snapshots : List (AnnotatedPairShiftSnapshot n)}
    {snapshot : AnnotatedPairShiftSnapshot n} :
    snapshot ∈ significantAnnotatedSnapshots threshold snapshots ↔
      snapshot ∈ snapshots ∧ snapshot.sourcePassCount < threshold := by
  simp [significantAnnotatedSnapshots,
    AnnotatedPairShiftSnapshot.significantDecision]

/-- Exact semantic membership criterion for the insignificant sublist. -/
theorem mem_insignificantAnnotatedSnapshots_iff
    {n : ℕ} {threshold : ℕ}
    {snapshots : List (AnnotatedPairShiftSnapshot n)}
    {snapshot : AnnotatedPairShiftSnapshot n} :
    snapshot ∈ insignificantAnnotatedSnapshots threshold snapshots ↔
      snapshot ∈ snapshots ∧ threshold ≤ snapshot.sourcePassCount := by
  simp [insignificantAnnotatedSnapshots,
    AnnotatedPairShiftSnapshot.significantDecision]

/--
Pointwise value bounds turn the semantic counter split into the abstract
partition consumed by `ShiftAccounting`.
-/
def annotatedSignificancePartition
    {n : ℕ} (valueBound threshold : ℕ)
    (snapshots : List (AnnotatedPairShiftSnapshot n))
    (valuesBound :
      ∀ annotated ∈ snapshots,
        annotated.snapshot.ValuesBound valueBound) :
    SnapshotSignificancePartition valueBound
      (insignificantAnnotatedSnapshots threshold snapshots).length
      (snapshots.map AnnotatedPairShiftSnapshot.snapshot) :=
  { significant := significantPairShiftSnapshots threshold snapshots
    insignificant := insignificantPairShiftSnapshots threshold snapshots
    permuted := perm_map_snapshot_significance threshold snapshots
    insignificant_count := by
      simp [insignificantPairShiftSnapshots]
    values_bound := by
      intro snapshot member
      obtain ⟨annotated, annotatedMember, snapshotEq⟩ :=
        List.mem_map.mp member
      subst snapshot
      exact valuesBound annotated annotatedMember }

/-- Pointwise winner-charge identities sum exactly over a finite timed list. -/
theorem totalVShift_map_annotated_eq_totalTemporalShift
    {n eventCount : ℕ}
    (deltas : Fin eventCount → ℤ)
    (charge :
      TimedAnnotatedPairShiftSnapshot n →
        TemporalCharge eventCount)
    (snapshots : List (TimedAnnotatedPairShiftSnapshot n))
    (exact :
      ∀ timed ∈ snapshots,
        timed.annotated.snapshot.vShift =
          temporalShift deltas (charge timed)) :
    totalVShift
        (snapshots.map fun timed => timed.annotated.snapshot) =
      totalTemporalShift deltas (snapshots.map charge) := by
  induction snapshots with
  | nil =>
      rfl
  | cons timed snapshots ih =>
      have headEq := exact timed (by simp)
      have tailEq :=
        ih (by
          intro later member
          exact exact later (by simp [member]))
      change
        timed.annotated.snapshot.vShift +
            totalVShift
              (snapshots.map fun current =>
                current.annotated.snapshot) =
          temporalShift deltas (charge timed) +
            totalTemporalShift deltas (snapshots.map charge)
      rw [headEq, tailEq]

/-- Pointwise creator-charge identities sum exactly over a finite timed list. -/
theorem totalUShift_map_annotated_eq_totalTemporalShift
    {n eventCount : ℕ}
    (deltas : Fin eventCount → ℤ)
    (charge :
      TimedAnnotatedPairShiftSnapshot n →
        TemporalCharge eventCount)
    (snapshots : List (TimedAnnotatedPairShiftSnapshot n))
    (exact :
      ∀ timed ∈ snapshots,
        timed.annotated.snapshot.uShift =
          temporalShift deltas (charge timed)) :
    totalUShift
        (snapshots.map fun timed => timed.annotated.snapshot) =
      totalTemporalShift deltas (snapshots.map charge) := by
  induction snapshots with
  | nil =>
      rfl
  | cons timed snapshots ih =>
      have headEq := exact timed (by simp)
      have tailEq :=
        ih (by
          intro later member
          exact exact later (by simp [member]))
      change
        timed.annotated.snapshot.uShift +
            totalUShift
              (snapshots.map fun current =>
                current.annotated.snapshot) =
          temporalShift deltas (charge timed) +
            totalTemporalShift deltas (snapshots.map charge)
      rw [headEq, tailEq]

/--
The remaining model-specific content of significant incidence, separated from
the generic temporal double-counting arithmetic.

`vCharges` and `uCharges` are oriented join-time intervals over the same
chronological list of unit value-change events.
-/
structure SignificantTemporalIncidence
    {n : ℕ} (threshold growingLimit eventCount : ℕ)
    (snapshots : List (AnnotatedPairShiftSnapshot n)) where
  deltas : Fin eventCount → ℤ
  vCharges : List (TemporalCharge eventCount)
  uCharges : List (TemporalCharge eventCount)
  deltaUnit : ∀ event, |deltas event| ≤ 1
  vShift_eq :
    totalVShift (significantPairShiftSnapshots threshold snapshots) =
      totalTemporalShift deltas vCharges
  uShift_eq :
    totalUShift (significantPairShiftSnapshots threshold snapshots) =
      totalTemporalShift deltas uCharges
  vIncidence :
    ∀ event,
      (vCharges.map fun charge => |charge event|).sum ≤
        (threshold : ℤ)
  uIncidence :
    ∀ event,
      (uCharges.map fun charge => |charge event|).sum ≤
        (growingLimit * threshold : ℕ)

namespace SignificantTemporalIncidence

/-- Temporal v-incidence immediately gives the desired significant v-budget. -/
theorem totalVShift_le
    {n threshold growingLimit eventCount : ℕ}
    {snapshots : List (AnnotatedPairShiftSnapshot n)}
    (incidence :
      SignificantTemporalIncidence threshold growingLimit eventCount
        snapshots) :
    totalVShift (significantPairShiftSnapshots threshold snapshots) ≤
      ((threshold * eventCount : ℕ) : ℤ) := by
  rw [incidence.vShift_eq]
  exact
    totalTemporalShift_le_incidence incidence.deltas
      incidence.vCharges incidence.deltaUnit incidence.vIncidence

/-- Temporal u-incidence gives the desired `growingLimit * threshold` budget. -/
theorem totalUShift_le
    {n threshold growingLimit eventCount : ℕ}
    {snapshots : List (AnnotatedPairShiftSnapshot n)}
    (incidence :
      SignificantTemporalIncidence threshold growingLimit eventCount
        snapshots) :
    totalUShift (significantPairShiftSnapshots threshold snapshots) ≤
      ((growingLimit * threshold * eventCount : ℕ) : ℤ) := by
  rw [incidence.uShift_eq]
  exact
    totalTemporalShift_le_incidence incidence.deltas
      incidence.uCharges incidence.deltaUnit incidence.uIncidence

end SignificantTemporalIncidence

/-- Timed annotations contributed by one arbitrary exact operation. -/
noncomputable def operationTimedPairShiftSnapshots
    {n : ℕ} {params : Parameters}
    (before after : State n) (labels : RootLabels)
    (ledger : EpisodeLedger n) (clock : EpisodeClock n)
    (events : List (ValueChangeEvent n)) (operation : Operation n)
    (exact : EpisodeLedger.ExactAt before labels ledger)
    (step : Step params before operation after)
    (aligned : labels.length = before.blocks.length) :
    List (TimedAnnotatedPairShiftSnapshot n) :=
  match operation with
  | .pass _ _ =>
      timedLifetimePassSnapshots clock events exact step aligned
  | _ => []

/-- Erasing event times recovers the operation annotated list. -/
@[simp]
theorem map_annotated_operationTimedPairShiftSnapshots
    {n : ℕ} {params : Parameters}
    (before after : State n) (labels : RootLabels)
    (ledger : EpisodeLedger n) (clock : EpisodeClock n)
    (events : List (ValueChangeEvent n)) (operation : Operation n)
    (exact : EpisodeLedger.ExactAt before labels ledger)
    (step : Step params before operation after)
    (aligned : labels.length = before.blocks.length) :
    (operationTimedPairShiftSnapshots before after labels ledger clock
        events operation exact step aligned).map
        TimedAnnotatedPairShiftSnapshot.annotated =
      operationAnnotatedPairShiftSnapshots before after labels ledger
        operation exact step aligned := by
  cases operation <;>
    simp [operationTimedPairShiftSnapshots,
      operationAnnotatedPairShiftSnapshots]

/-- One timed annotation is produced per unit of pass activity. -/
@[simp]
theorem length_operationTimedPairShiftSnapshots
    {n : ℕ} {params : Parameters}
    (before after : State n) (labels : RootLabels)
    (ledger : EpisodeLedger n) (clock : EpisodeClock n)
    (events : List (ValueChangeEvent n)) (operation : Operation n)
    (exact : EpisodeLedger.ExactAt before labels ledger)
    (step : Step params before operation after)
    (aligned : labels.length = before.blocks.length) :
    (operationTimedPairShiftSnapshots before after labels ledger clock
        events operation exact step aligned).length =
      operation.activity := by
  cases operation <;>
    simp [operationTimedPairShiftSnapshots, Operation.activity]

/-- Distinct matching endpoints make operation-snapshot winners distinct. -/
theorem map_winner_operationTimedPairShiftSnapshots_nodup
    {n : ℕ} {params : Parameters}
    (before after : State n) (labels : RootLabels)
    (ledger : EpisodeLedger n) (clock : EpisodeClock n)
    (events : List (ValueChangeEvent n)) (operation : Operation n)
    (exact : EpisodeLedger.ExactAt before labels ledger)
    (step : Step params before operation after)
    (aligned : labels.length = before.blocks.length) :
    ((operationTimedPairShiftSnapshots before after labels ledger clock
        events operation exact step aligned).map fun timed =>
      timed.annotated.winner).Nodup := by
  cases operation with
  | convert blockId =>
      simp [operationTimedPairShiftSnapshots]
  | create creator =>
      simp [operationTimedPairShiftSnapshots]
  | insert blockId element =>
      simp [operationTimedPairShiftSnapshots]
  | delete blockId element =>
      simp [operationTimedPairShiftSnapshots]
  | @pass source matching =>
      have endpointsNodup :
          (matching.flatMap fun pairing =>
            [pairing.winner, pairing.loser]).Nodup := by
        cases step.2.1 with
        | pass found validMatching blocksEq valuesEq =>
            exact validMatching.2.1
      simpa [operationTimedPairShiftSnapshots,
        timedLifetimePassSnapshots,
        TimedAnnotatedPairShiftSnapshot.ofLifetimePass,
        AnnotatedPairShiftSnapshot.ofLifetimePass,
        Function.comp_def] using
        pairingWinners_nodup endpointsNodup
  | split blockId prefixLength =>
      simp [operationTimedPairShiftSnapshots]
  | valueChange element delta =>
      cases delta <;>
        simp [operationTimedPairShiftSnapshots]

/-- One operation contributes at most one snapshot to a fixed v-column. -/
theorem length_vIncident_significant_operationTimed_le_one
    {n : ℕ} {params : Parameters}
    (threshold : ℕ) (finalEvents : List (ValueChangeEvent n))
    (event : Fin finalEvents.length)
    (before after : State n) (labels : RootLabels)
    (ledger : EpisodeLedger n) (clock : EpisodeClock n)
    (events : List (ValueChangeEvent n)) (operation : Operation n)
    (exact : EpisodeLedger.ExactAt before labels ledger)
    (step : Step params before operation after)
    (aligned : labels.length = before.blocks.length) :
    (vIncidentTimedSnapshots finalEvents event
        (significantTimedSnapshots threshold
          (operationTimedPairShiftSnapshots before after labels ledger clock
            events operation exact step aligned))).length ≤ 1 := by
  let operationSnapshots :=
    operationTimedPairShiftSnapshots before after labels ledger clock
      events operation exact step aligned
  let selected :=
    vIncidentTimedSnapshots finalEvents event
      (significantTimedSnapshots threshold operationSnapshots)
  have selectedSublist : selected.Sublist operationSnapshots := by
    dsimp [selected, operationSnapshots]
    exact List.filter_sublist.trans List.filter_sublist
  have winnersNodup :
      (selected.map fun timed => timed.annotated.winner).Nodup :=
    (selectedSublist.map fun timed =>
      timed.annotated.winner).nodup
        (map_winner_operationTimedPairShiftSnapshots_nodup
          before after labels ledger clock events operation exact step aligned)
  apply
    length_le_one_of_map_nodup_of_constant selected
      (fun timed => timed.annotated.winner)
      (finalEvents.get event).element winnersNodup
  intro timed member
  exact winner_eq_eventElement_of_mem_vIncidentTimedSnapshots member

/-- Every timed snapshot of an operation ends at that operation's event prefix. -/
theorem eventsBefore_eq_of_mem_operationTimedPairShiftSnapshots
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
    timed.eventsBefore = events := by
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
      rfl
  | split blockId prefixLength =>
      simp [operationTimedPairShiftSnapshots] at member
  | valueChange element delta =>
      cases delta <;>
        simp [operationTimedPairShiftSnapshots] at member

/-- Both episode clocks of an operation snapshot lie in its event prefix. -/
theorem startEvents_le_of_mem_operationTimedPairShiftSnapshots
    {n : ℕ} {params : Parameters}
    (before after : State n) (labels : RootLabels)
    (ledger : EpisodeLedger n) (clock : EpisodeClock n)
    (events : List (ValueChangeEvent n)) (operation : Operation n)
    (exact : EpisodeLedger.ExactAt before labels ledger)
    (clockSound : EpisodeClock.SoundAt before ledger clock events)
    (step : Step params before operation after)
    (aligned : labels.length = before.blocks.length)
    {timed : TimedAnnotatedPairShiftSnapshot n}
    (member :
      timed ∈
        operationTimedPairShiftSnapshots before after labels ledger clock
          events operation exact step aligned) :
    timed.winnerStartEvent ≤ timed.eventsBefore.length ∧
      timed.loserStartEvent ≤ timed.eventsBefore.length := by
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
      let starts :=
        exact.pass_pairing_starts step aligned attached.2
      exact
        ⟨(clockSound attached.1.winner starts.winnerStart
              starts.winnerActive).1,
          (clockSound attached.1.loser starts.loserStart
              starts.loserActive).1⟩
  | split blockId prefixLength =>
      simp [operationTimedPairShiftSnapshots] at member
  | valueChange element delta =>
      cases delta <;>
        simp [operationTimedPairShiftSnapshots] at member

/-- An operation snapshot records the current clock of its winner exactly. -/
theorem winnerStartEvent_eq_clock_of_mem_operationTimedPairShiftSnapshots
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
    timed.winnerStartEvent = clock timed.annotated.winner := by
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
      rfl
  | split blockId prefixLength =>
      simp [operationTimedPairShiftSnapshots] at member
  | valueChange element delta =>
      cases delta <;>
        simp [operationTimedPairShiftSnapshots] at member

/-- A physical pass floor bounds the source counter of every winner snapshot. -/
theorem passFloor_le_sourcePassCount_of_mem_operationTimedPairShiftSnapshots
    {n : ℕ} {params : Parameters}
    (before after : State n) (labels : RootLabels)
    (ledger : EpisodeLedger n) (clock : EpisodeClock n)
    (events : List (ValueChangeEvent n)) (operation : Operation n)
    (exact : EpisodeLedger.ExactAt before labels ledger)
    (step : Step params before operation after)
    (aligned : labels.length = before.blocks.length)
    {element : Element n} {floor : ℕ}
    (floorAt : PassFloorAt before element floor)
    {timed : TimedAnnotatedPairShiftSnapshot n}
    (member :
      timed ∈
        operationTimedPairShiftSnapshots before after labels ledger clock
          events operation exact step aligned)
    (winnerEq : timed.annotated.winner = element) :
    floor ≤ timed.annotated.sourcePassCount := by
  cases operation with
  | convert blockId =>
      simp [operationTimedPairShiftSnapshots] at member
  | create creator =>
      simp [operationTimedPairShiftSnapshots] at member
  | insert blockId inserted =>
      simp [operationTimedPairShiftSnapshots] at member
  | delete blockId deleted =>
      simp [operationTimedPairShiftSnapshots] at member
  | @pass source matching =>
      obtain ⟨attached, _attachedMem, timedEq⟩ :=
        List.mem_map.mp member
      subst timed
      have actualWinnerEq : attached.1.winner = element := by
        change attached.1.winner = element at winnerEq
        exact winnerEq
      let starts :=
        exact.pass_pairing_starts step aligned attached.2
      have validMatchingForStarts :
          MatchingValid params before source starts.sourceBlock matching := by
        cases step.2.1 with
        | pass found validMatching blocksEq valuesEq =>
            rename_i actualSource
            have sourceEq : actualSource = starts.sourceBlock := by
              rw [starts.sourceFound] at found
              exact (Option.some.inj found).symm
            subst actualSource
            exact validMatching
      have winnerMem : attached.1.winner ∈ starts.sourceBlock.elements :=
        (validMatchingForStarts.2.2.2.1
          attached.1 attached.2).1.first_mem
      change
        floor ≤
          (AnnotatedPairShiftSnapshot.ofLifetimePass
            exact step aligned attached.2).sourcePassCount
      change floor ≤ starts.sourceBlock.passCount
      apply floorAt source starts.sourceBlock starts.sourceFound
      simpa [actualWinnerEq] using winnerMem
  | split blockId prefixLength =>
      simp [operationTimedPairShiftSnapshots] at member
  | valueChange changed delta =>
      cases delta <;>
        simp [operationTimedPairShiftSnapshots] at member

/-- A winner snapshot installs the strict successor floor in the post-state. -/
theorem passFloorAt_winner_after_of_mem_operationTimedPairShiftSnapshots
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
    PassFloorAt after timed.annotated.winner
      (timed.annotated.sourcePassCount + 1) := by
  cases operation with
  | convert blockId =>
      simp [operationTimedPairShiftSnapshots] at member
  | create creator =>
      simp [operationTimedPairShiftSnapshots] at member
  | insert blockId inserted =>
      simp [operationTimedPairShiftSnapshots] at member
  | delete blockId deleted =>
      simp [operationTimedPairShiftSnapshots] at member
  | @pass source matching =>
      obtain ⟨attached, _attachedMem, timedEq⟩ :=
        List.mem_map.mp member
      subst timed
      simpa [TimedAnnotatedPairShiftSnapshot.ofLifetimePass,
        AnnotatedPairShiftSnapshot.ofLifetimePass] using
        AnnotatedPairShiftSnapshot.passFloorAt_winner_after_ofLifetimePass
          exact step aligned attached.2
  | split blockId prefixLength =>
      simp [operationTimedPairShiftSnapshots] at member
  | valueChange changed delta =>
      cases delta <;>
        simp [operationTimedPairShiftSnapshots] at member

/-- Every operation snapshot realizes its winner shift on any extending event list. -/
theorem vShift_eq_temporalCharge_of_mem_operationTimedPairShiftSnapshots
    {n : ℕ} {params : Parameters}
    (before after : State n) (labels : RootLabels)
    (ledger : EpisodeLedger n) (clock : EpisodeClock n)
    (events finalEvents : List (ValueChangeEvent n))
    (operation : Operation n)
    (exact : EpisodeLedger.ExactAt before labels ledger)
    (clockSound : EpisodeClock.SoundAt before ledger clock events)
    (step : Step params before operation after)
    (aligned : labels.length = before.blocks.length)
    (eventsPrefix : events <+: finalEvents)
    {timed : TimedAnnotatedPairShiftSnapshot n}
    (member :
      timed ∈
        operationTimedPairShiftSnapshots before after labels ledger clock
          events operation exact step aligned) :
    timed.annotated.snapshot.vShift =
      temporalShift (valueChangeDeltaVector finalEvents)
        (timed.vTemporalCharge finalEvents) := by
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
      exact
        TimedAnnotatedPairShiftSnapshot.vShift_eq_temporalCharge
          clock events finalEvents exact clockSound step aligned attached.2
          eventsPrefix
  | split blockId prefixLength =>
      simp [operationTimedPairShiftSnapshots] at member
  | valueChange element delta =>
      cases delta <;>
        simp [operationTimedPairShiftSnapshots] at member

/-- Every operation snapshot realizes its creator shift on the same event list. -/
theorem uShift_eq_temporalCharge_of_mem_operationTimedPairShiftSnapshots
    {n : ℕ} {params : Parameters}
    (before after : State n) (labels : RootLabels)
    (ledger : EpisodeLedger n) (clock : EpisodeClock n)
    (events finalEvents : List (ValueChangeEvent n))
    (operation : Operation n)
    (exact : EpisodeLedger.ExactAt before labels ledger)
    (clockSound : EpisodeClock.SoundAt before ledger clock events)
    (step : Step params before operation after)
    (aligned : labels.length = before.blocks.length)
    (eventsPrefix : events <+: finalEvents)
    {timed : TimedAnnotatedPairShiftSnapshot n}
    (member :
      timed ∈
        operationTimedPairShiftSnapshots before after labels ledger clock
          events operation exact step aligned) :
    timed.annotated.snapshot.uShift =
      temporalShift (valueChangeDeltaVector finalEvents)
        (timed.uTemporalCharge finalEvents) := by
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
      exact
        TimedAnnotatedPairShiftSnapshot.uShift_eq_temporalCharge
          clock events finalEvents exact clockSound step aligned attached.2
          eventsPrefix
  | split blockId prefixLength =>
      simp [operationTimedPairShiftSnapshots] at member
  | valueChange element delta =>
      cases delta <;>
        simp [operationTimedPairShiftSnapshots] at member

namespace LifetimeHistory

/-- Chronological annotated pair snapshots over an exact lifetime history. -/
inductive AnnotatedPairShiftHistory {n : ℕ} (params : Parameters) :
    State n → RootLabels → EpisodeLedger n →
      List (Operation n) → List (AnnotatedPairShiftSnapshot n) →
      State n → RootLabels → EpisodeLedger n → Prop
  | nil {state : State n} {labels : RootLabels}
      {ledger : EpisodeLedger n}
      (valid : state.Valid params) :
      AnnotatedPairShiftHistory params state labels ledger
        [] [] state labels ledger
  | cons {before middle final : State n}
      {beforeLabels finalLabels : RootLabels}
      {beforeLedger finalLedger : EpisodeLedger n}
      {operation : Operation n} {operations : List (Operation n)}
      {tailSnapshots : List (AnnotatedPairShiftSnapshot n)}
      (aligned : beforeLabels.length = before.blocks.length)
      (exact :
        EpisodeLedger.ExactAt before beforeLabels beforeLedger)
      (head : Step params before operation middle)
      (tail :
        AnnotatedPairShiftHistory params middle
          (RootLabels.after beforeLabels operation)
          (EpisodeLedger.after before beforeLabels beforeLedger operation)
          operations tailSnapshots final finalLabels finalLedger) :
      AnnotatedPairShiftHistory params before beforeLabels beforeLedger
        (operation :: operations)
        (operationAnnotatedPairShiftSnapshots before middle beforeLabels
            beforeLedger operation exact head aligned ++ tailSnapshots)
        final finalLabels finalLedger

/-- Every exact lifetime history admits chronological annotated snapshots. -/
theorem lift_annotatedPairShiftSnapshots
    {n : ℕ} {params : Parameters}
    {initial final : State n} {initialLabels finalLabels : RootLabels}
    {initialLedger finalLedger : EpisodeLedger n}
    {operations : List (Operation n)}
    {joins : List (JoinOccurrence n)}
    {leaves : List (LeaveOccurrence n)}
    {closed : List (ClosedEpisode n)}
    (history :
      LifetimeHistory params initial initialLabels initialLedger
        operations joins leaves closed final finalLabels finalLedger)
    (aligned : initialLabels.length = initial.blocks.length)
    (exact :
      EpisodeLedger.ExactAt initial initialLabels initialLedger) :
    ∃ snapshots,
      AnnotatedPairShiftHistory params initial initialLabels initialLedger
        operations snapshots final finalLabels finalLedger := by
  induction history with
  | nil valid =>
      exact ⟨[], .nil valid⟩
  | @cons before middle final beforeLabels finalLabels beforeLedger
      finalLedger operation operations tailJoins tailLeaves tailClosed
      head tail ih =>
      have middleAligned :
          (RootLabels.after beforeLabels operation).length =
            middle.blocks.length :=
        (HistoryStep.mk head rfl).labels_length aligned
      have middleExact :=
        exact.after_step head aligned
      obtain ⟨tailSnapshots, tailHistory⟩ :=
        ih middleAligned middleExact
      exact
        ⟨operationAnnotatedPairShiftSnapshots before middle beforeLabels
              beforeLedger operation exact head aligned ++
            tailSnapshots,
          .cons aligned exact head tailHistory⟩

/-- The annotated history erases to a chronological plain snapshot history. -/
theorem AnnotatedPairShiftHistory.erase
    {n : ℕ} {params : Parameters}
    {initial final : State n} {initialLabels finalLabels : RootLabels}
    {initialLedger finalLedger : EpisodeLedger n}
    {operations : List (Operation n)}
    {snapshots : List (AnnotatedPairShiftSnapshot n)}
    (history :
      AnnotatedPairShiftHistory params initial initialLabels initialLedger
        operations snapshots final finalLabels finalLedger) :
    PairShiftSnapshotHistory params initial initialLabels initialLedger
      operations (snapshots.map AnnotatedPairShiftSnapshot.snapshot)
      final finalLabels finalLedger := by
  induction history with
  | nil valid =>
      exact .nil valid
  | cons aligned exact head tail ih =>
      rw [List.map_append,
        map_snapshot_operationAnnotatedPairShiftSnapshots]
      exact .cons aligned exact head ih

/-- Every annotated chronological history has exactly total activity length. -/
theorem AnnotatedPairShiftHistory.snapshots_length
    {n : ℕ} {params : Parameters}
    {initial final : State n} {initialLabels finalLabels : RootLabels}
    {initialLedger finalLedger : EpisodeLedger n}
    {operations : List (Operation n)}
    {snapshots : List (AnnotatedPairShiftSnapshot n)}
    (history :
      AnnotatedPairShiftHistory params initial initialLabels initialLedger
        operations snapshots final finalLabels finalLedger) :
    snapshots.length = totalActivity operations := by
  induction history with
  | nil valid =>
      rfl
  | cons aligned exact head tail ih =>
      rw [List.length_append,
        length_operationAnnotatedPairShiftSnapshots,
        ih]
      rfl

/-- Frozen-value boundedness holds pointwise over the full annotation history. -/
theorem AnnotatedPairShiftHistory.valuesBound
    {n : ℕ} {params : Parameters}
    {initial final : State n} {initialLabels finalLabels : RootLabels}
    {initialLedger finalLedger : EpisodeLedger n}
    {operations : List (Operation n)}
    {snapshots : List (AnnotatedPairShiftSnapshot n)}
    (history :
      AnnotatedPairShiftHistory params initial initialLabels initialLedger
        operations snapshots final finalLabels finalLedger)
    (frozen :
      EpisodeLedger.FrozenValuesBound params initialLedger) :
    ∀ annotated ∈ snapshots,
      annotated.snapshot.ValuesBound params.valueBound := by
  revert frozen
  induction history with
  | nil valid =>
      intro frozen annotated member
      simp at member
  | @cons before middle final beforeLabels finalLabels beforeLedger
      finalLedger operation operations tailSnapshots aligned exact head tail
      ih =>
      intro frozen annotated member
      rcases List.mem_append.mp member with headMember | tailMember
      · exact
          valuesBound_operationAnnotatedPairShiftSnapshots
            before middle beforeLabels beforeLedger operation exact frozen
            head aligned annotated headMember
      · exact ih (frozen.after_step head) annotated tailMember

/-- The exact global significance partition carried by an annotated history. -/
def AnnotatedPairShiftHistory.significancePartition
    {n : ℕ} {params : Parameters}
    {initial final : State n} {initialLabels finalLabels : RootLabels}
    {initialLedger finalLedger : EpisodeLedger n}
    {operations : List (Operation n)}
    {snapshots : List (AnnotatedPairShiftSnapshot n)}
    (history :
      AnnotatedPairShiftHistory params initial initialLabels initialLedger
        operations snapshots final finalLabels finalLedger)
    (frozen :
      EpisodeLedger.FrozenValuesBound params initialLedger)
    (threshold : ℕ) :
    SnapshotSignificancePartition params.valueBound
      (insignificantAnnotatedSnapshots threshold snapshots).length
      (snapshots.map AnnotatedPairShiftSnapshot.snapshot) :=
  annotatedSignificancePartition params.valueBound threshold snapshots
    (history.valuesBound frozen)

/--
Every annotated lifetime history admits a synchronized activity history whose
high-pass-count tail is exactly the global insignificant snapshot count.
-/
theorem AnnotatedPairShiftHistory.lift_activityHistory_with_tail
    {n : ℕ} {params : Parameters}
    {initial final : State n} {initialLabels finalLabels : RootLabels}
    {initialLedger finalLedger : EpisodeLedger n}
    {operations : List (Operation n)}
    {snapshots : List (AnnotatedPairShiftSnapshot n)}
    (threshold : ℕ)
    (history :
      AnnotatedPairShiftHistory params initial initialLabels initialLedger
        operations snapshots final finalLabels finalLedger) :
    ∃ occurrences,
      ActivityHistory params initial initialLabels operations occurrences
          final finalLabels ∧
        (insignificantAnnotatedSnapshots threshold snapshots).length =
          tailActivity occurrences threshold := by
  induction history with
  | nil valid =>
      exact ⟨[], .nil valid, rfl⟩
  | @cons before middle final beforeLabels finalLabels beforeLedger
      finalLedger operation operations tailSnapshots aligned exact head tail
      ih =>
      obtain ⟨tailOccurrences, activityTail, tailCount⟩ := ih
      refine
        ⟨operationActivityOccurrences before beforeLabels operation ++
            tailOccurrences,
          .cons head activityTail, ?_⟩
      calc
        (insignificantAnnotatedSnapshots threshold
            (operationAnnotatedPairShiftSnapshots before middle
                beforeLabels beforeLedger operation exact head aligned ++
              tailSnapshots)).length =
            (insignificantAnnotatedSnapshots threshold
                (operationAnnotatedPairShiftSnapshots before middle
                  beforeLabels beforeLedger operation exact head
                  aligned)).length +
              (insignificantAnnotatedSnapshots threshold
                tailSnapshots).length := by
              simp [insignificantAnnotatedSnapshots]
        _ =
            tailActivity
                (operationActivityOccurrences before beforeLabels operation)
                threshold +
              tailActivity tailOccurrences threshold := by
              rw [
                length_insignificant_operationAnnotatedPairShiftSnapshots
                  threshold before middle beforeLabels beforeLedger operation
                  exact head aligned,
                tailCount]
        _ =
            tailActivity
              (operationActivityOccurrences before beforeLabels operation ++
                tailOccurrences) threshold := by
              simp [tailActivity]

/--
Chronological timed pair snapshots, threading the exact episode clock and
value-change event prefix alongside the lifetime history.
-/
inductive TimedPairShiftHistory {n : ℕ} (params : Parameters) :
    State n → RootLabels → EpisodeLedger n → EpisodeClock n →
      List (ValueChangeEvent n) →
      List (Operation n) → List (TimedAnnotatedPairShiftSnapshot n) →
      State n → RootLabels → EpisodeLedger n → EpisodeClock n →
      List (ValueChangeEvent n) → Prop
  | nil {state : State n} {labels : RootLabels}
      {ledger : EpisodeLedger n} {clock : EpisodeClock n}
      {events : List (ValueChangeEvent n)}
      (valid : state.Valid params)
      (clockSound : EpisodeClock.SoundAt state ledger clock events) :
      TimedPairShiftHistory params state labels ledger clock events
        [] [] state labels ledger clock events
  | cons {before middle final : State n}
      {beforeLabels finalLabels : RootLabels}
      {beforeLedger finalLedger : EpisodeLedger n}
      {beforeClock finalClock : EpisodeClock n}
      {beforeEvents finalEvents : List (ValueChangeEvent n)}
      {operation : Operation n} {operations : List (Operation n)}
      {tailSnapshots : List (TimedAnnotatedPairShiftSnapshot n)}
      (aligned : beforeLabels.length = before.blocks.length)
      (exact :
        EpisodeLedger.ExactAt before beforeLabels beforeLedger)
      (clockSound :
        EpisodeClock.SoundAt before beforeLedger beforeClock beforeEvents)
      (head : Step params before operation middle)
      (tail :
        TimedPairShiftHistory params middle
          (RootLabels.after beforeLabels operation)
          (EpisodeLedger.after before beforeLabels beforeLedger operation)
          (EpisodeClock.after beforeEvents.length beforeClock operation)
          (beforeEvents ++ operationValueChangeEvents operation)
          operations tailSnapshots final finalLabels finalLedger
          finalClock finalEvents) :
      TimedPairShiftHistory params before beforeLabels beforeLedger
        beforeClock beforeEvents (operation :: operations)
        (operationTimedPairShiftSnapshots before middle beforeLabels
            beforeLedger beforeClock beforeEvents operation exact head
            aligned ++
          tailSnapshots)
        final finalLabels finalLedger finalClock finalEvents

/-- Every exact lifetime history admits its timed chronological annotation. -/
theorem lift_timedPairShiftSnapshots
    {n : ℕ} {params : Parameters}
    {initial final : State n} {initialLabels finalLabels : RootLabels}
    {initialLedger finalLedger : EpisodeLedger n}
    {operations : List (Operation n)}
    {joins : List (JoinOccurrence n)}
    {leaves : List (LeaveOccurrence n)}
    {closed : List (ClosedEpisode n)}
    (history :
      LifetimeHistory params initial initialLabels initialLedger
        operations joins leaves closed final finalLabels finalLedger)
    (initialClock : EpisodeClock n)
    (initialEvents : List (ValueChangeEvent n))
    (aligned : initialLabels.length = initial.blocks.length)
    (exact :
      EpisodeLedger.ExactAt initial initialLabels initialLedger)
    (clockSound :
      EpisodeClock.SoundAt initial initialLedger initialClock initialEvents) :
    ∃ finalClock finalEvents snapshots,
      TimedPairShiftHistory params initial initialLabels initialLedger
        initialClock initialEvents operations snapshots
        final finalLabels finalLedger finalClock finalEvents := by
  induction history generalizing initialClock initialEvents with
  | nil valid =>
      exact ⟨initialClock, initialEvents, [], .nil valid clockSound⟩
  | @cons before middle final beforeLabels finalLabels beforeLedger
      finalLedger operation operations tailJoins tailLeaves tailClosed
      head tail ih =>
      have middleAligned :
          (RootLabels.after beforeLabels operation).length =
            middle.blocks.length :=
        (HistoryStep.mk head rfl).labels_length aligned
      have middleExact :=
        exact.after_step head aligned
      have middleClockSound :=
        EpisodeClock.SoundAt.after_step
          (labels := beforeLabels) clockSound head
      obtain ⟨finalClock, finalEvents, tailSnapshots, tailHistory⟩ :=
        ih
          (EpisodeClock.after initialEvents.length initialClock operation)
          (initialEvents ++ operationValueChangeEvents operation)
          middleAligned middleExact middleClockSound
      exact
        ⟨finalClock, finalEvents,
          operationTimedPairShiftSnapshots before middle beforeLabels
              beforeLedger initialClock initialEvents operation exact head
              aligned ++
            tailSnapshots,
          .cons aligned exact clockSound head tailHistory⟩

/-- Timed annotations erase to the chronological annotated snapshot history. -/
theorem TimedPairShiftHistory.erase
    {n : ℕ} {params : Parameters}
    {initial final : State n} {initialLabels finalLabels : RootLabels}
    {initialLedger finalLedger : EpisodeLedger n}
    {initialClock finalClock : EpisodeClock n}
    {initialEvents finalEvents : List (ValueChangeEvent n)}
    {operations : List (Operation n)}
    {snapshots : List (TimedAnnotatedPairShiftSnapshot n)}
    (history :
      TimedPairShiftHistory params initial initialLabels initialLedger
        initialClock initialEvents operations snapshots
        final finalLabels finalLedger finalClock finalEvents) :
    AnnotatedPairShiftHistory params initial initialLabels initialLedger
      operations (snapshots.map TimedAnnotatedPairShiftSnapshot.annotated)
      final finalLabels finalLedger := by
  induction history with
  | nil valid clockSound =>
      exact .nil valid
  | cons aligned exact clockSound head tail ih =>
      rw [List.map_append,
        map_annotated_operationTimedPairShiftSnapshots]
      exact .cons aligned exact head ih

/-- Timed chronological histories still contain exactly total activity. -/
theorem TimedPairShiftHistory.snapshots_length
    {n : ℕ} {params : Parameters}
    {initial final : State n} {initialLabels finalLabels : RootLabels}
    {initialLedger finalLedger : EpisodeLedger n}
    {initialClock finalClock : EpisodeClock n}
    {initialEvents finalEvents : List (ValueChangeEvent n)}
    {operations : List (Operation n)}
    {snapshots : List (TimedAnnotatedPairShiftSnapshot n)}
    (history :
      TimedPairShiftHistory params initial initialLabels initialLedger
        initialClock initialEvents operations snapshots
        final finalLabels finalLedger finalClock finalEvents) :
    snapshots.length = totalActivity operations := by
  simpa using history.erase.snapshots_length

/-- The final event list is the initial prefix followed by all trace changes. -/
theorem TimedPairShiftHistory.finalEvents_eq
    {n : ℕ} {params : Parameters}
    {initial final : State n} {initialLabels finalLabels : RootLabels}
    {initialLedger finalLedger : EpisodeLedger n}
    {initialClock finalClock : EpisodeClock n}
    {initialEvents finalEvents : List (ValueChangeEvent n)}
    {operations : List (Operation n)}
    {snapshots : List (TimedAnnotatedPairShiftSnapshot n)}
    (history :
      TimedPairShiftHistory params initial initialLabels initialLedger
        initialClock initialEvents operations snapshots
        final finalLabels finalLedger finalClock finalEvents) :
    finalEvents = initialEvents ++ valueChangeEvents operations := by
  induction history with
  | nil valid clockSound =>
      simp [valueChangeEvents]
  | @cons before middle final beforeLabels finalLabels beforeLedger
      finalLedger beforeClock finalClock beforeEvents finalEvents
      operation operations tailSnapshots aligned exact clockSound head tail
      ih =>
      rw [ih]
      simp [valueChangeEvents, List.append_assoc]

/-- The endpoint clock remains semantically sound. -/
theorem TimedPairShiftHistory.finalClockSound
    {n : ℕ} {params : Parameters}
    {initial final : State n} {initialLabels finalLabels : RootLabels}
    {initialLedger finalLedger : EpisodeLedger n}
    {initialClock finalClock : EpisodeClock n}
    {initialEvents finalEvents : List (ValueChangeEvent n)}
    {operations : List (Operation n)}
    {snapshots : List (TimedAnnotatedPairShiftSnapshot n)}
    (history :
      TimedPairShiftHistory params initial initialLabels initialLedger
        initialClock initialEvents operations snapshots
        final finalLabels finalLedger finalClock finalEvents) :
    EpisodeClock.SoundAt final finalLedger finalClock finalEvents := by
  induction history with
  | nil valid clockSound =>
      exact clockSound
  | cons aligned exact clockSound head tail ih =>
      exact ih

/-- Every pass prefix retained by a timed snapshot is a prefix of all events. -/
theorem TimedPairShiftHistory.snapshot_eventsBefore_prefix_final
    {n : ℕ} {params : Parameters}
    {initial final : State n} {initialLabels finalLabels : RootLabels}
    {initialLedger finalLedger : EpisodeLedger n}
    {initialClock finalClock : EpisodeClock n}
    {initialEvents finalEvents : List (ValueChangeEvent n)}
    {operations : List (Operation n)}
    {snapshots : List (TimedAnnotatedPairShiftSnapshot n)}
    (history :
      TimedPairShiftHistory params initial initialLabels initialLedger
        initialClock initialEvents operations snapshots
        final finalLabels finalLedger finalClock finalEvents) :
    ∀ timed ∈ snapshots, timed.eventsBefore <+: finalEvents := by
  induction history with
  | nil valid clockSound =>
      simp
  | @cons before middle final beforeLabels finalLabels beforeLedger
      finalLedger beforeClock finalClock beforeEvents finalEvents
      operation operations tailSnapshots aligned exact clockSound head tail
      ih =>
      intro timed member
      rcases List.mem_append.mp member with headMember | tailMember
      · have eventsEq :=
          eventsBefore_eq_of_mem_operationTimedPairShiftSnapshots
            before middle beforeLabels beforeLedger beforeClock beforeEvents
            operation exact head aligned headMember
        rw [eventsEq]
        rw [tail.finalEvents_eq]
        simpa [List.append_assoc] using
          List.prefix_append beforeEvents
            (operationValueChangeEvents operation ++
              valueChangeEvents operations)
      · exact ih timed tailMember

/-- Both episode starts of every timed snapshot precede the final event list. -/
theorem TimedPairShiftHistory.snapshot_startEvents_le_final
    {n : ℕ} {params : Parameters}
    {initial final : State n} {initialLabels finalLabels : RootLabels}
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
      timed.winnerStartEvent ≤ timed.eventsBefore.length ∧
        timed.loserStartEvent ≤ timed.eventsBefore.length ∧
        timed.eventsBefore.length ≤ finalEvents.length := by
  intro timed member
  have startBounds :
      timed.winnerStartEvent ≤ timed.eventsBefore.length ∧
        timed.loserStartEvent ≤ timed.eventsBefore.length := by
    induction history with
    | nil valid clockSound =>
        simp at member
    | @cons before middle final beforeLabels finalLabels beforeLedger
        finalLedger beforeClock finalClock beforeEvents finalEvents
        operation operations tailSnapshots aligned exact clockSound head tail
        ih =>
        rcases List.mem_append.mp member with headMember | tailMember
        · exact
            startEvents_le_of_mem_operationTimedPairShiftSnapshots
              before middle beforeLabels beforeLedger beforeClock beforeEvents
              operation exact clockSound head aligned headMember
        · exact ih tailMember
  have endBound :=
    (history.snapshot_eventsBefore_prefix_final timed member).length_le
  exact ⟨startBounds.1, startBounds.2, endBound⟩

/--
An event-relative pass floor at the beginning of a timed history bounds every
later winner whose episode clock still lies before that cutoff.
-/
theorem TimedPairShiftHistory.sourcePassCount_ge_of_clockedFloor
    {n : ℕ} {params : Parameters}
    {initial final : State n} {initialLabels finalLabels : RootLabels}
    {initialLedger finalLedger : EpisodeLedger n}
    {initialClock finalClock : EpisodeClock n}
    {initialEvents finalEvents : List (ValueChangeEvent n)}
    {operations : List (Operation n)}
    {snapshots : List (TimedAnnotatedPairShiftSnapshot n)}
    (history :
      TimedPairShiftHistory params initial initialLabels initialLedger
        initialClock initialEvents operations snapshots
        final finalLabels finalLedger finalClock finalEvents)
    {cutoff floor : ℕ} {element : Element n}
    (cutoffLe : cutoff ≤ initialEvents.length)
    (floorAt :
      ClockedPassFloorAt initial initialClock cutoff element floor) :
    ∀ timed ∈ snapshots,
      timed.annotated.winner = element →
        timed.winnerStartEvent < cutoff →
        floor ≤ timed.annotated.sourcePassCount := by
  induction history generalizing cutoff floor element with
  | nil valid clockSound =>
      simp
  | @cons before middle final beforeLabels finalLabels beforeLedger
      finalLedger beforeClock finalClock beforeEvents finalEvents
      operation operations tailSnapshots aligned exact clockSound head tail
      ih =>
      intro timed member winnerEq startBefore
      rcases List.mem_append.mp member with headMember | tailMember
      · have clockEq :=
          winnerStartEvent_eq_clock_of_mem_operationTimedPairShiftSnapshots
            before middle beforeLabels beforeLedger beforeClock beforeEvents
            operation exact head aligned headMember
        have oldClockLow : beforeClock element < cutoff := by
          rw [winnerEq] at clockEq
          omega
        exact
          passFloor_le_sourcePassCount_of_mem_operationTimedPairShiftSnapshots
            before middle beforeLabels beforeLedger beforeClock beforeEvents
            operation exact head aligned (floorAt oldClockLow) headMember
            winnerEq
      · have nextCutoffLe :
            cutoff ≤
              (beforeEvents ++
                operationValueChangeEvents operation).length := by
          simpa using cutoffLe.trans
            (Nat.le_add_right beforeEvents.length
              (operationValueChangeEvents operation).length)
        have nextFloor :=
          ClockedPassFloorAt.after_step floorAt cutoffLe head
        exact
          ih nextCutoffLe nextFloor timed tailMember winnerEq startBefore

/-- Every chronological winner shift is exactly its concrete final-event charge. -/
theorem TimedPairShiftHistory.snapshot_vShift_eq_temporalCharge
    {n : ℕ} {params : Parameters}
    {initial final : State n} {initialLabels finalLabels : RootLabels}
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
      timed.annotated.snapshot.vShift =
        temporalShift (valueChangeDeltaVector finalEvents)
          (timed.vTemporalCharge finalEvents) := by
  induction history with
  | nil valid clockSound =>
      simp
  | @cons before middle final beforeLabels finalLabels beforeLedger
      finalLedger beforeClock finalClock beforeEvents finalEvents
      operation operations tailSnapshots aligned exact clockSound head tail
      ih =>
      intro timed member
      rcases List.mem_append.mp member with headMember | tailMember
      · have eventsPrefix : beforeEvents <+: finalEvents := by
          rw [tail.finalEvents_eq]
          simpa [List.append_assoc] using
            List.prefix_append beforeEvents
              (operationValueChangeEvents operation ++
                valueChangeEvents operations)
        exact
          vShift_eq_temporalCharge_of_mem_operationTimedPairShiftSnapshots
            before middle beforeLabels beforeLedger beforeClock beforeEvents
            finalEvents operation exact clockSound head aligned eventsPrefix
            headMember
      · exact ih timed tailMember

/-- Every chronological creator shift is exactly its concrete final-event charge. -/
theorem TimedPairShiftHistory.snapshot_uShift_eq_temporalCharge
    {n : ℕ} {params : Parameters}
    {initial final : State n} {initialLabels finalLabels : RootLabels}
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
      timed.annotated.snapshot.uShift =
        temporalShift (valueChangeDeltaVector finalEvents)
          (timed.uTemporalCharge finalEvents) := by
  induction history with
  | nil valid clockSound =>
      simp
  | @cons before middle final beforeLabels finalLabels beforeLedger
      finalLedger beforeClock finalClock beforeEvents finalEvents
      operation operations tailSnapshots aligned exact clockSound head tail
      ih =>
      intro timed member
      rcases List.mem_append.mp member with headMember | tailMember
      · have eventsPrefix : beforeEvents <+: finalEvents := by
          rw [tail.finalEvents_eq]
          simpa [List.append_assoc] using
            List.prefix_append beforeEvents
              (operationValueChangeEvents operation ++
                valueChangeEvents operations)
        exact
          uShift_eq_temporalCharge_of_mem_operationTimedPairShiftSnapshots
            before middle beforeLabels beforeLedger beforeClock beforeEvents
            finalEvents operation exact clockSound head aligned eventsPrefix
            headMember
      · exact ih timed tailMember

/-- Final events of a history started at the empty prefix are all signed units. -/
theorem TimedPairShiftHistory.final_deltaUnit_of_empty
    {n : ℕ} {params : Parameters}
    {initial final : State n} {initialLabels finalLabels : RootLabels}
    {initialLedger finalLedger : EpisodeLedger n}
    {initialClock finalClock : EpisodeClock n}
    {finalEvents : List (ValueChangeEvent n)}
    {operations : List (Operation n)}
    {snapshots : List (TimedAnnotatedPairShiftSnapshot n)}
    (history :
      TimedPairShiftHistory params initial initialLabels initialLedger
        initialClock [] operations snapshots
        final finalLabels finalLedger finalClock finalEvents) :
    ∀ event : Fin finalEvents.length,
      |valueChangeDeltaVector finalEvents event| ≤ 1 := by
  intro event
  have finalEq := history.finalEvents_eq
  simp only [List.nil_append] at finalEq
  change |(finalEvents.get event).delta| ≤ 1
  apply delta_abs_le_one_of_mem_valueChangeEvents
  rw [← finalEq]
  exact List.get_mem _ event

/--
The concrete timed history supplies all algebraic fields of significant
temporal incidence.  Only the two genuinely combinatorial column bounds
remain as explicit premises.
-/
def TimedPairShiftHistory.significantTemporalIncidence
    {n : ℕ} {params : Parameters}
    {initial final : State n} {initialLabels finalLabels : RootLabels}
    {initialLedger finalLedger : EpisodeLedger n}
    {initialClock finalClock : EpisodeClock n}
    {initialEvents finalEvents : List (ValueChangeEvent n)}
    {operations : List (Operation n)}
    {snapshots : List (TimedAnnotatedPairShiftSnapshot n)}
    (history :
      TimedPairShiftHistory params initial initialLabels initialLedger
        initialClock initialEvents operations snapshots
        final finalLabels finalLedger finalClock finalEvents)
    (threshold growingLimit : ℕ)
    (deltaUnit :
      ∀ event : Fin finalEvents.length,
        |valueChangeDeltaVector finalEvents event| ≤ 1)
    (vIncidence :
      ∀ event : Fin finalEvents.length,
        ((significantTimedSnapshots threshold snapshots).map fun timed =>
          |timed.vTemporalCharge finalEvents event|).sum ≤
            (threshold : ℤ))
    (uIncidence :
      ∀ event : Fin finalEvents.length,
        ((significantTimedSnapshots threshold snapshots).map fun timed =>
          |timed.uTemporalCharge finalEvents event|).sum ≤
            ((growingLimit * threshold : ℕ) : ℤ)) :
    SignificantTemporalIncidence threshold growingLimit finalEvents.length
      (snapshots.map TimedAnnotatedPairShiftSnapshot.annotated) :=
  { deltas := valueChangeDeltaVector finalEvents
    vCharges :=
      (significantTimedSnapshots threshold snapshots).map fun timed =>
        timed.vTemporalCharge finalEvents
    uCharges :=
      (significantTimedSnapshots threshold snapshots).map fun timed =>
        timed.uTemporalCharge finalEvents
    deltaUnit := deltaUnit
    vShift_eq := by
      have aggregate :=
        totalVShift_map_annotated_eq_totalTemporalShift
          (valueChangeDeltaVector finalEvents)
          (fun timed => timed.vTemporalCharge finalEvents)
          (significantTimedSnapshots threshold snapshots)
          (by
            intro timed member
            apply history.snapshot_vShift_eq_temporalCharge
            exact
              (List.mem_filter.mp member).1)
      change
        totalVShift
            ((significantAnnotatedSnapshots threshold
              (snapshots.map
                TimedAnnotatedPairShiftSnapshot.annotated)).map
                  AnnotatedPairShiftSnapshot.snapshot) =
          _
      have snapshotsEq :
          (significantTimedSnapshots threshold snapshots).map
              (fun timed => timed.annotated.snapshot) =
            (significantAnnotatedSnapshots threshold
              (snapshots.map
                TimedAnnotatedPairShiftSnapshot.annotated)).map
                  AnnotatedPairShiftSnapshot.snapshot := by
        rw [← map_annotated_significantTimedSnapshots]
        simp only [List.map_map, Function.comp_def]
      rw [← snapshotsEq]
      exact aggregate
    uShift_eq := by
      have aggregate :=
        totalUShift_map_annotated_eq_totalTemporalShift
          (valueChangeDeltaVector finalEvents)
          (fun timed => timed.uTemporalCharge finalEvents)
          (significantTimedSnapshots threshold snapshots)
          (by
            intro timed member
            apply history.snapshot_uShift_eq_temporalCharge
            exact
              (List.mem_filter.mp member).1)
      change
        totalUShift
            ((significantAnnotatedSnapshots threshold
              (snapshots.map
                TimedAnnotatedPairShiftSnapshot.annotated)).map
                  AnnotatedPairShiftSnapshot.snapshot) =
          _
      have snapshotsEq :
          (significantTimedSnapshots threshold snapshots).map
              (fun timed => timed.annotated.snapshot) =
            (significantAnnotatedSnapshots threshold
              (snapshots.map
                TimedAnnotatedPairShiftSnapshot.annotated)).map
                  AnnotatedPairShiftSnapshot.snapshot := by
        rw [← map_annotated_significantTimedSnapshots]
        simp only [List.map_map, Function.comp_def]
      rw [← snapshotsEq]
      exact aggregate
    vIncidence := by
      intro event
      simpa [List.map_map, Function.comp_def] using vIncidence event
    uIncidence := by
      intro event
      simpa [List.map_map, Function.comp_def] using uIncidence event }

/--
High-level significant-shift API: concrete column bounds on a timed history
immediately yield the manuscript's two aggregate value-change budgets.
-/
theorem TimedPairShiftHistory.significant_shift_bounds
    {n : ℕ} {params : Parameters}
    {initial final : State n} {initialLabels finalLabels : RootLabels}
    {initialLedger finalLedger : EpisodeLedger n}
    {initialClock finalClock : EpisodeClock n}
    {finalEvents : List (ValueChangeEvent n)}
    {operations : List (Operation n)}
    {snapshots : List (TimedAnnotatedPairShiftSnapshot n)}
    (history :
      TimedPairShiftHistory params initial initialLabels initialLedger
        initialClock [] operations snapshots
        final finalLabels finalLedger finalClock finalEvents)
    (threshold : ℕ)
    (vIncidence :
      ∀ event : Fin finalEvents.length,
        ((significantTimedSnapshots threshold snapshots).map fun timed =>
          |timed.vTemporalCharge finalEvents event|).sum ≤
            (threshold : ℤ))
    (uIncidence :
      ∀ event : Fin finalEvents.length,
        ((significantTimedSnapshots threshold snapshots).map fun timed =>
          |timed.uTemporalCharge finalEvents event|).sum ≤
            ((params.growingLimit * threshold : ℕ) : ℤ)) :
    totalVShift
          (significantPairShiftSnapshots threshold
            (snapshots.map
              TimedAnnotatedPairShiftSnapshot.annotated)) ≤
        ((threshold * totalValueChanges operations : ℕ) : ℤ) ∧
      totalUShift
          (significantPairShiftSnapshots threshold
            (snapshots.map
              TimedAnnotatedPairShiftSnapshot.annotated)) ≤
        ((params.growingLimit * threshold *
          totalValueChanges operations : ℕ) : ℤ) := by
  let incidence :=
    history.significantTemporalIncidence threshold params.growingLimit
      history.final_deltaUnit_of_empty vIncidence uIncidence
  have eventLength :
      finalEvents.length = totalValueChanges operations := by
    have finalEq := history.finalEvents_eq
    simp only [List.nil_append] at finalEq
    rw [finalEq, length_valueChangeEvents]
  constructor
  · simpa [eventLength] using incidence.totalVShift_le
  · simpa [eventLength] using incidence.totalUShift_le

/--
Count-based form of the high-level API.  It is enough to show that each value
change lies in at most `τ` significant winner intervals and at most
`growingLimit * τ` significant creator intervals.
-/
theorem TimedPairShiftHistory.significant_shift_bounds_of_incident_counts
    {n : ℕ} {params : Parameters}
    {initial final : State n} {initialLabels finalLabels : RootLabels}
    {initialLedger finalLedger : EpisodeLedger n}
    {initialClock finalClock : EpisodeClock n}
    {finalEvents : List (ValueChangeEvent n)}
    {operations : List (Operation n)}
    {snapshots : List (TimedAnnotatedPairShiftSnapshot n)}
    (history :
      TimedPairShiftHistory params initial initialLabels initialLedger
        initialClock [] operations snapshots
        final finalLabels finalLedger finalClock finalEvents)
    (threshold : ℕ)
    (vCount :
      ∀ event : Fin finalEvents.length,
        (vIncidentTimedSnapshots finalEvents event
          (significantTimedSnapshots threshold snapshots)).length ≤
            threshold)
    (uCount :
      ∀ event : Fin finalEvents.length,
        (uIncidentTimedSnapshots finalEvents event
          (significantTimedSnapshots threshold snapshots)).length ≤
            params.growingLimit * threshold) :
    totalVShift
          (significantPairShiftSnapshots threshold
            (snapshots.map
              TimedAnnotatedPairShiftSnapshot.annotated)) ≤
        ((threshold * totalValueChanges operations : ℕ) : ℤ) ∧
      totalUShift
          (significantPairShiftSnapshots threshold
            (snapshots.map
              TimedAnnotatedPairShiftSnapshot.annotated)) ≤
        ((params.growingLimit * threshold *
          totalValueChanges operations : ℕ) : ℤ) := by
  apply history.significant_shift_bounds threshold
  · intro event
    rw [sum_abs_vTemporalCharge_eq_incident_length]
    exact_mod_cast vCount event
  · intro event
    rw [sum_abs_uTemporalCharge_eq_incident_length]
    exact_mod_cast uCount event

/--
Structural form used by the model proof: v-columns inject into pass counters,
while u-columns inject into `(root, passCount)` and use at most
`growingLimit` roots.
-/
theorem TimedPairShiftHistory.significant_shift_bounds_of_key_invariants
    {n : ℕ} {params : Parameters}
    {initial final : State n} {initialLabels finalLabels : RootLabels}
    {initialLedger finalLedger : EpisodeLedger n}
    {initialClock finalClock : EpisodeClock n}
    {finalEvents : List (ValueChangeEvent n)}
    {operations : List (Operation n)}
    {snapshots : List (TimedAnnotatedPairShiftSnapshot n)}
    (history :
      TimedPairShiftHistory params initial initialLabels initialLedger
        initialClock [] operations snapshots
        final finalLabels finalLedger finalClock finalEvents)
    (threshold : ℕ)
    (vCountsNodup :
      ∀ event : Fin finalEvents.length,
        ((vIncidentTimedSnapshots finalEvents event
            (significantTimedSnapshots threshold snapshots)).map fun timed =>
          timed.annotated.sourcePassCount).Nodup)
    (uKeysNodup :
      ∀ event : Fin finalEvents.length,
        ((uIncidentTimedSnapshots finalEvents event
            (significantTimedSnapshots threshold snapshots)).map fun timed =>
          (timed.annotated.sourceRoot,
            timed.annotated.sourcePassCount)).Nodup)
    (uRootsBound :
      ∀ event : Fin finalEvents.length,
        ((uIncidentTimedSnapshots finalEvents event
            (significantTimedSnapshots threshold snapshots)).map fun timed =>
          timed.annotated.sourceRoot).toFinset.card ≤
            params.growingLimit) :
    totalVShift
          (significantPairShiftSnapshots threshold
            (snapshots.map
              TimedAnnotatedPairShiftSnapshot.annotated)) ≤
        ((threshold * totalValueChanges operations : ℕ) : ℤ) ∧
      totalUShift
          (significantPairShiftSnapshots threshold
            (snapshots.map
              TimedAnnotatedPairShiftSnapshot.annotated)) ≤
        ((params.growingLimit * threshold *
          totalValueChanges operations : ℕ) : ℤ) := by
  apply history.significant_shift_bounds_of_incident_counts threshold
  · intro event
    exact
      vIncident_length_le_of_passCounts_nodup finalEvents event snapshots
        (vCountsNodup event)
  · intro event
    exact
      uIncident_length_le_of_runKeys_nodup finalEvents event snapshots
        (uKeysNodup event) (uRootsBound event)

end LifetimeHistory

end Splay.Interface
