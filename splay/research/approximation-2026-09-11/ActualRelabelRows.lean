import ActualHistoricalLabelInventory
import ActualTimedErrorBudget
import ActualHistoricalLink

namespace Splay.Research.ActualRelabelRows

open Splay.Interface
open ActualHistoricalLabelInventory
open scoped BigOperators

def winnerRank {n : ℕ} (timed : TimedAnnotatedPairShiftSnapshot n) : ℕ :=
  historicalRank timed.annotated.winnerStart

def oldRank {n : ℕ} (timed : TimedAnnotatedPairShiftSnapshot n) : ℕ :=
  historicalRank timed.annotated.loserStart

def newRank {n : ℕ} (timed : TimedAnnotatedPairShiftSnapshot n) : ℕ :=
  ((timed.annotated.loserStart.join.valueAtJoin : ℤ) +
    ActualTimedErrorBudget.loserDrift timed).toNat - timed.annotated.snapshot.winnerNow

def rowPositive {n : ℕ} (rankLabel : ℕ → ℕ)
    (timed : TimedAnnotatedPairShiftSnapshot n) : ℕ :=
  rankLabel (newRank timed) - rankLabel (oldRank timed)

def rowNegative {n : ℕ} (rankLabel : ℕ → ℕ)
    (timed : TimedAnnotatedPairShiftSnapshot n) : ℕ :=
  rankLabel (oldRank timed) - rankLabel (newRank timed)

def rowPreparation {n : ℕ} (rankLabel : ℕ → ℕ)
    (timed : TimedAnnotatedPairShiftSnapshot n) : ℕ :=
  rankLabel (winnerRank timed) + 1 - rankLabel (oldRank timed)

def RowValid {n : ℕ} (params : Parameters) (timed : TimedAnnotatedPairShiftSnapshot n) : Prop :=
  1 ≤ winnerRank timed ∧ winnerRank timed ≤ params.valueBound ∧
  1 ≤ oldRank timed ∧ oldRank timed ≤ params.valueBound ∧
  1 ≤ newRank timed ∧ newRank timed ≤ params.valueBound ∧
  (newRank timed : ℤ) = (oldRank timed : ℤ) - (winnerRank timed : ℤ) +
    ActualTimedErrorBudget.error timed

theorem newRank_ofLifetimePass {n : ℕ} {params : Parameters}
    {before after : State n} {labels : RootLabels}
    {ledger : EpisodeLedger n} {source : BlockId}
    {matching : List (Pairing n)} {pairing : Pairing n}
    (clock : EpisodeClock n) (events : List (ValueChangeEvent n))
    (exact : EpisodeLedger.ExactAt before labels ledger)
    (sound : EpisodeClock.SoundAt before ledger clock events)
    (step : Step params before (.pass source matching) after)
    (aligned : labels.length = before.blocks.length) (member : pairing ∈ matching) :
    newRank (TimedAnnotatedPairShiftSnapshot.ofLifetimePass clock events
      exact step aligned member) = before.value pairing.loser - before.value pairing.winner := by
  let starts := exact.pass_pairing_starts step aligned member
  have drift := (sound pairing.loser starts.loserStart starts.loserActive).2.1
  change ((starts.loserStart.join.valueAtJoin : ℤ) +
    eventDrift pairing.loser (events.drop (clock pairing.loser))).toNat -
      before.value pairing.winner = _
  rw [← drift]
  simp

theorem valid_ofLifetimePass {n : ℕ} {params : Parameters}
    {before after : State n} {labels : RootLabels}
    {ledger : EpisodeLedger n} {source : BlockId}
    {matching : List (Pairing n)} {pairing : Pairing n}
    (clock : EpisodeClock n) (events : List (ValueChangeEvent n))
    (exact : EpisodeLedger.ExactAt before labels ledger)
    (frozen : EpisodeLedger.FrozenValuesBound params ledger)
    (sound : EpisodeClock.SoundAt before ledger clock events)
    (step : Step params before (.pass source matching) after)
    (aligned : labels.length = before.blocks.length) (member : pairing ∈ matching) :
    RowValid params (TimedAnnotatedPairShiftSnapshot.ofLifetimePass clock events
      exact step aligned member) := by
  let starts := exact.pass_pairing_starts step aligned member
  have wValid := starts.winnerJoinValid
  have lValid := starts.loserJoinValid
  have wBound := (frozen pairing.winner starts.winnerStart starts.winnerActive).1
  have lBound := (frozen pairing.loser starts.loserStart starts.loserActive).1
  have nowBound := (step.1.2.1 pairing.loser).2
  have order : before.value pairing.winner + 1 ≤ before.value pairing.loser := by
    cases step.2.1 with
    | pass found validMatching blocks values =>
        exact (validMatching.2.2.2.1 pairing member).2.1
  unfold RowValid
  rw [newRank_ofLifetimePass clock events exact sound step aligned member]
  change 1 ≤ historicalRank starts.winnerStart ∧
    historicalRank starts.winnerStart ≤ params.valueBound ∧
    1 ≤ historicalRank starts.loserStart ∧
    historicalRank starts.loserStart ≤ params.valueBound ∧
    1 ≤ before.value pairing.loser - before.value pairing.winner ∧
    before.value pairing.loser - before.value pairing.winner ≤ params.valueBound ∧ _
  refine ⟨?_, ?_, ?_, ?_, by omega, by omega, ?_⟩
  · unfold historicalRank; unfold EpisodeStart.JoinValid at wValid; omega
  · unfold historicalRank; omega
  · unfold historicalRank; unfold EpisodeStart.JoinValid at lValid; omega
  · unfold historicalRank; omega
  · have identity := ActualHistoricalLink.pass_identity exact step aligned member
    have drift := (sound pairing.loser starts.loserStart starts.loserActive).2.1
    change (((before.value pairing.loser - before.value pairing.winner : ℕ) : ℤ)) =
      (historicalRank starts.loserStart : ℤ) - (historicalRank starts.winnerStart : ℤ) +
        ((starts.winnerStart.join.valueAtJoin : ℤ) - before.value pairing.winner +
          ((starts.loserStart.creatorValueAtJoin : ℤ) - starts.winnerStart.creatorValueAtJoin) +
            eventDrift pairing.loser (events.drop (clock pairing.loser)))
    change (((before.value pairing.loser - before.value pairing.winner : ℕ) : ℤ)) =
      (historicalRank starts.loserStart : ℤ) - (historicalRank starts.winnerStart : ℤ) +
        ((starts.winnerStart.join.valueAtJoin : ℤ) - before.value pairing.winner) -
        ((starts.loserStart.join.valueAtJoin : ℤ) - before.value pairing.loser) +
        ((starts.loserStart.creatorValueAtJoin : ℤ) - starts.winnerStart.creatorValueAtJoin) at identity
    linarith

theorem nominal_after_loser {n : ℕ} {params : Parameters}
    (rankLabel : ℕ → ℕ) {before after : State n} (labels : RootLabels)
    (ledger : EpisodeLedger n) {source : BlockId}
    {matching : List (Pairing n)} {pairing : Pairing n}
    (step : Step params before (.pass source matching) after)
    (member : pairing ∈ matching) :
    nominal rankLabel (EpisodeLedger.after before labels ledger (.pass source matching))
      pairing.loser = rankLabel (before.value pairing.loser - before.value pairing.winner) := by
  cases step.2.1 with
  | pass found validMatching blocks values =>
      have installed := EpisodeLedger.installPassJoins_apply_of_mem before labels source ledger
        (pairingLosers_nodup validMatching.2.1) member
      obtain ⟨destination, destFound, growing, creatorEq⟩ :=
        (validMatching.2.2.2.1 pairing member).2.2.2
      simp only [EpisodeLedger.after, nominal, installed]
      simp [historicalRank, EpisodeStart.ofJoin, makeJoinOccurrence, destFound, creatorEq]

private theorem sum_support_eq_list {n : ℕ} (keys : List (Element n))
    (distinct : keys.Nodup) (f : Element n → ℕ)
    (support : ∀ element, element ∉ keys → f element = 0) :
    (∑ element, f element) = (keys.map f).sum := by
  have restricted : (∑ element ∈ keys.toFinset, f element) = ∑ element, f element := by
    apply Fintype.sum_subset
    intro element nonzero
    simpa using (by
      by_contra absent
      exact nonzero (support element absent) : element ∈ keys)
  rw [← restricted]
  exact List.sum_toFinset f distinct

/-- The all-key compiler variation is exactly a sum over genuine Pass losers. -/
theorem pass_change_sum {n : ℕ} {params : Parameters}
    (rankLabel : ℕ → ℕ) (delta : ℕ → ℕ → ℕ) (diagonal : ∀ value, delta value value = 0)
    {before after : State n} (labels : RootLabels) (ledger : EpisodeLedger n)
    {source : BlockId} {matching : List (Pairing n)}
    (step : Step params before (.pass source matching) after) :
    (∑ element : Element n,
      delta (nominal rankLabel (EpisodeLedger.after before labels ledger
        (.pass source matching)) element) (nominal rankLabel ledger element)) =
      (matching.map fun pairing =>
        delta (rankLabel (before.value pairing.loser - before.value pairing.winner))
          (nominal rankLabel ledger pairing.loser)).sum := by
  have distinct : (pairingLosers matching).Nodup := by
    cases step.2.1 with
    | pass found validMatching blocks values =>
        exact pairingLosers_nodup validMatching.2.1
  rw [sum_support_eq_list (pairingLosers matching) distinct _ (by
    intro element absent
    have unchanged := EpisodeLedger.installPassJoins_apply_of_not_mem
      before labels source ledger matching element absent
    simp only [EpisodeLedger.after, nominal, unchanged]
    exact diagonal _)]
  simp only [pairingLosers, List.map_map, Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro pairing member
  rw [nominal_after_loser rankLabel labels ledger step member]

theorem pass_rows {n : ℕ} {params : Parameters}
    (rankLabel : ℕ → ℕ) {before after : State n} {labels : RootLabels}
    {ledger : EpisodeLedger n} {source : BlockId} {matching : List (Pairing n)}
    (clock : EpisodeClock n) (events : List (ValueChangeEvent n))
    (exact : EpisodeLedger.ExactAt before labels ledger)
    (sound : EpisodeClock.SoundAt before ledger clock events)
    (step : Step params before (.pass source matching) after)
    (aligned : labels.length = before.blocks.length) :
    ((timedLifetimePassSnapshots clock events exact step aligned).map (rowPositive rankLabel)).sum =
      positive rankLabel before labels ledger (.pass source matching) ∧
    ((timedLifetimePassSnapshots clock events exact step aligned).map (rowNegative rankLabel)).sum =
      negative rankLabel before labels ledger (.pass source matching) := by
  have oldLabel : ∀ pairing : { p // p ∈ matching },
      rankLabel (oldRank (TimedAnnotatedPairShiftSnapshot.ofLifetimePass clock events
        exact step aligned pairing.2)) = nominal rankLabel ledger pairing.1.loser := by
    intro pairing
    let starts := exact.pass_pairing_starts step aligned pairing.2
    change rankLabel (historicalRank starts.loserStart) = _
    simp [nominal, starts.loserActive]
  have mapped : ∀ delta : ℕ → ℕ → ℕ,
      ((timedLifetimePassSnapshots clock events exact step aligned).map fun timed =>
        delta (rankLabel (newRank timed)) (rankLabel (oldRank timed))).sum =
      (matching.map fun pairing => delta
        (rankLabel (before.value pairing.loser - before.value pairing.winner))
        (nominal rankLabel ledger pairing.loser)).sum := by
    intro delta
    unfold timedLifetimePassSnapshots
    simp only [List.map_map, Function.comp_def]
    have mappedEq : (matching.attach.map fun pairing => delta
        (rankLabel (newRank (TimedAnnotatedPairShiftSnapshot.ofLifetimePass clock events
          exact step aligned pairing.2)))
        (rankLabel (oldRank (TimedAnnotatedPairShiftSnapshot.ofLifetimePass clock events
          exact step aligned pairing.2)))) =
      (matching.attach.map fun pairing => delta
        (rankLabel (before.value pairing.1.loser - before.value pairing.1.winner))
        (nominal rankLabel ledger pairing.1.loser)) := by
      apply List.map_congr_left
      intro pairing _
      rw [newRank_ofLifetimePass clock events exact sound step aligned pairing.2,
        oldLabel pairing]
    rw [mappedEq]
    simp
  constructor
  · change _ = ∑ element : Element n, _
    rw [pass_change_sum rankLabel (fun new old => new - old) (by intro; omega)
      labels ledger step]
    exact mapped (fun new old => new - old)
  · change _ = ∑ element : Element n, _
    rw [pass_change_sum rankLabel (fun new old => old - new) (by intro; omega)
      labels ledger step]
    exact mapped (fun new old => old - new)

theorem operation_rows {n : ℕ} {params : Parameters}
    (rankLabel : ℕ → ℕ) (before after : State n) (labels : RootLabels)
    (ledger : EpisodeLedger n) (clock : EpisodeClock n) (events : List (ValueChangeEvent n))
    (operation : Operation n) (exact : EpisodeLedger.ExactAt before labels ledger)
    (sound : EpisodeClock.SoundAt before ledger clock events)
    (step : Step params before operation after) (aligned : labels.length = before.blocks.length) :
    ((operationTimedPairShiftSnapshots before after labels ledger clock events operation
      exact step aligned).map (rowPositive rankLabel)).sum = positive rankLabel before labels ledger operation ∧
    ((operationTimedPairShiftSnapshots before after labels ledger clock events operation
      exact step aligned).map (rowNegative rankLabel)).sum = negative rankLabel before labels ledger operation := by
  cases operation with
  | pass source matching => exact pass_rows rankLabel clock events exact sound step aligned
  | _ => exact ⟨rfl, rfl⟩

theorem operation_valid {n : ℕ} {params : Parameters}
    (before after : State n) (labels : RootLabels) (ledger : EpisodeLedger n)
    (clock : EpisodeClock n) (events : List (ValueChangeEvent n))
    (operation : Operation n) (exact : EpisodeLedger.ExactAt before labels ledger)
    (frozen : EpisodeLedger.FrozenValuesBound params ledger)
    (sound : EpisodeClock.SoundAt before ledger clock events)
    (step : Step params before operation after) (aligned : labels.length = before.blocks.length)
    {timed : TimedAnnotatedPairShiftSnapshot n}
    (member : timed ∈ operationTimedPairShiftSnapshots before after labels ledger clock events
      operation exact step aligned) : RowValid params timed := by
  cases operation with
  | pass source matching =>
      obtain ⟨pairing, pairMember, pairEq⟩ := List.mem_map.mp member
      subst timed
      exact valid_ofLifetimePass clock events exact frozen sound step aligned pairing.2
  | _ => simp [operationTimedPairShiftSnapshots] at member

theorem history_valid {n : ℕ} {params : Parameters}
    {initial final : State n} {initialLabels finalLabels : RootLabels}
    {initialLedger finalLedger : EpisodeLedger n} {initialClock finalClock : EpisodeClock n}
    {initialEvents finalEvents : List (ValueChangeEvent n)} {operations : List (Operation n)}
    {snapshots : List (TimedAnnotatedPairShiftSnapshot n)}
    (history : LifetimeHistory.TimedPairShiftHistory params initial initialLabels initialLedger
      initialClock initialEvents operations snapshots final finalLabels finalLedger finalClock finalEvents)
    (frozen : EpisodeLedger.FrozenValuesBound params initialLedger) :
    ∀ timed ∈ snapshots, RowValid params timed := by
  revert frozen
  induction history with
  | nil valid sound => simp
  | @cons before middle final beforeLabels finalLabels beforeLedger finalLedger
      beforeClock finalClock beforeEvents finalEvents operation operations tailSnapshots
      aligned exact sound head tail ih =>
      intro frozen timed member
      rcases List.mem_append.mp member with headMember | tailMember
      · exact operation_valid before middle beforeLabels beforeLedger beforeClock beforeEvents
          operation exact frozen sound head aligned headMember
      · exact ih (frozen.after_step head) timed tailMember

/-- The rows and the literal inventory ledger are synchronized by induction
on the actual timed history, rather than by an assumed projection witness. -/
theorem history_rows {n : ℕ} {params : Parameters} (rankLabel : ℕ → ℕ)
    {initial final : State n} {initialLabels finalLabels : RootLabels}
    {initialLedger finalLedger : EpisodeLedger n} {initialClock finalClock : EpisodeClock n}
    {initialEvents finalEvents : List (ValueChangeEvent n)} {operations : List (Operation n)}
    {snapshots : List (TimedAnnotatedPairShiftSnapshot n)}
    (history : LifetimeHistory.TimedPairShiftHistory params initial initialLabels initialLedger
      initialClock initialEvents operations snapshots final finalLabels finalLedger finalClock finalEvents) :
    ActualHistoricalLabelInventory.History params rankLabel initial initialLabels initialLedger
      operations (snapshots.map (rowPositive rankLabel)).sum
        (snapshots.map (rowNegative rankLabel)).sum final finalLabels finalLedger := by
  induction history with
  | nil valid sound => exact .nil valid
  | @cons before middle final beforeLabels finalLabels beforeLedger finalLedger
      beforeClock finalClock beforeEvents finalEvents operation operations tailSnapshots
      aligned exact sound head tail ih =>
      have rows := operation_rows rankLabel before middle beforeLabels beforeLedger
        beforeClock beforeEvents operation exact sound head aligned
      simpa only [List.map_append, List.sum_append, rows.1, rows.2] using
        ActualHistoricalLabelInventory.History.cons head ih

end Splay.Research.ActualRelabelRows
