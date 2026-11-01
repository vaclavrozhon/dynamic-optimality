import ActualAbsoluteShiftBudget
import ActualLoserUpwardBudget

namespace Splay.Research.ActualTimedErrorBudget

open Splay.Interface
open ActualLoserUpwardBudget
open scoped BigOperators

def loserDrift {n : ℕ} (timed : TimedAnnotatedPairShiftSnapshot n) : ℤ :=
  eventDrift timed.annotated.loser (timed.eventsBefore.drop timed.loserStartEvent)

def loserUpward {n : ℕ} (timed : TimedAnnotatedPairShiftSnapshot n) : ℕ :=
  (loserDrift timed).toNat

def error {n : ℕ} (timed : TimedAnnotatedPairShiftSnapshot n) : ℤ :=
  timed.annotated.snapshot.vShift + timed.annotated.snapshot.uShift + loserDrift timed

theorem loserUpward_ofLifetimePass {n : ℕ} {params : Parameters}
    {before after : State n} {labels : RootLabels}
    {ledger : EpisodeLedger n} {source : BlockId}
    {matching : List (Pairing n)} {pairing : Pairing n}
    (clock : EpisodeClock n) (events : List (ValueChangeEvent n))
    (exact : EpisodeLedger.ExactAt before labels ledger)
    (sound : EpisodeClock.SoundAt before ledger clock events)
    (step : Step params before (.pass source matching) after)
    (aligned : labels.length = before.blocks.length) (member : pairing ∈ matching) :
    loserUpward (TimedAnnotatedPairShiftSnapshot.ofLifetimePass clock events
      exact step aligned member) = upward (before.value pairing.loser) (ledger pairing.loser) := by
  let starts := exact.pass_pairing_starts step aligned member
  have active := starts.loserActive
  have drift := (sound pairing.loser starts.loserStart active).2.1
  change (eventDrift pairing.loser (events.drop (clock pairing.loser))).toNat = _
  rw [active]
  change (eventDrift pairing.loser (events.drop (clock pairing.loser))).toNat =
    before.value pairing.loser - starts.loserStart.join.valueAtJoin
  omega

theorem operation_sum_eq {n : ℕ} {params : Parameters}
    (before after : State n) (labels : RootLabels) (ledger : EpisodeLedger n)
    (clock : EpisodeClock n) (events : List (ValueChangeEvent n))
    (operation : Operation n) (exact : EpisodeLedger.ExactAt before labels ledger)
    (sound : EpisodeClock.SoundAt before ledger clock events)
    (step : Step params before operation after)
    (aligned : labels.length = before.blocks.length) :
    ((operationTimedPairShiftSnapshots before after labels ledger clock events
      operation exact step aligned).map loserUpward).sum = passUpward before ledger operation := by
  cases operation with
  | pass source matching =>
      change ((timedLifetimePassSnapshots clock events exact step aligned).map loserUpward).sum = _
      unfold timedLifetimePassSnapshots passUpward
      simp only [List.map_map, Function.comp_def]
      have replace :
          (matching.attach.map fun pairing => loserUpward
            (TimedAnnotatedPairShiftSnapshot.ofLifetimePass clock events
              exact step aligned pairing.2)) =
          matching.attach.map fun pairing => upward (before.value pairing.1.loser)
            (ledger pairing.1.loser) := by
        apply List.map_congr_left
        intro pairing _
        exact loserUpward_ofLifetimePass clock events exact sound step aligned pairing.2
      rw [replace]
      simp
  | _ => rfl

theorem history_balance {n : ℕ} {params : Parameters}
    {initial final : State n} {initialLabels finalLabels : RootLabels}
    {initialLedger finalLedger : EpisodeLedger n}
    {initialClock finalClock : EpisodeClock n}
    {initialEvents finalEvents : List (ValueChangeEvent n)}
    {operations : List (Operation n)}
    {snapshots : List (TimedAnnotatedPairShiftSnapshot n)}
    (history : LifetimeHistory.TimedPairShiftHistory params initial initialLabels
      initialLedger initialClock initialEvents operations snapshots
      final finalLabels finalLedger finalClock finalEvents) :
    (snapshots.map loserUpward).sum + inventory final finalLedger ≤
      inventory initial initialLedger + totalValueChanges operations := by
  induction history with
  | nil valid sound => simp [totalValueChanges]
  | @cons before middle final beforeLabels finalLabels beforeLedger finalLedger
      beforeClock finalClock beforeEvents finalEvents operation operations tailSnapshots
      aligned exact sound head tail ih =>
      have budget := step_balance beforeLabels beforeLedger head
      have subbudget := passUpward_le_closed before beforeLabels beforeLedger operation
      have identity := operation_sum_eq before middle beforeLabels beforeLedger
        beforeClock beforeEvents operation exact sound head aligned
      simp only [List.map_append, List.sum_append, totalValueChanges,
        List.map_cons, List.sum_cons] at ih ⊢
      rw [identity]
      omega

theorem history_loser_upward_le {n : ℕ} {params : Parameters}
    {initial final : State n} {finalLabels : RootLabels}
    {finalLedger : EpisodeLedger n} {finalClock : EpisodeClock n}
    {finalEvents : List (ValueChangeEvent n)} {operations : List (Operation n)}
    {snapshots : List (TimedAnnotatedPairShiftSnapshot n)}
    (history : LifetimeHistory.TimedPairShiftHistory params initial []
      (EpisodeLedger.empty : EpisodeLedger n) (fun _ => 0) []
      operations snapshots final finalLabels finalLedger finalClock finalEvents) :
    (snapshots.map loserUpward).sum ≤ totalValueChanges operations := by
  have balance := history_balance history
  have zero : inventory initial (EpisodeLedger.empty : EpisodeLedger n) = 0 := by
    simp [inventory, EpisodeLedger.empty, upward]
  rw [zero, Nat.zero_add] at balance
  omega

/-- The exact integer error needed by historical-rank compression has a
literal original-history early budget, including every loser's upward drift. -/
theorem early_error_le {n : ℕ} {params : Parameters}
    {initial final : State n} {finalLabels : RootLabels}
    {finalLedger : EpisodeLedger n} {finalClock : EpisodeClock n}
    {finalEvents : List (ValueChangeEvent n)} {operations : List (Operation n)}
    {snapshots : List (TimedAnnotatedPairShiftSnapshot n)}
    (history : LifetimeHistory.TimedPairShiftHistory params initial []
      (EpisodeLedger.empty : EpisodeLedger n) (fun _ => 0) []
      operations snapshots final finalLabels finalLedger finalClock finalEvents)
    (initialState : initial.Initial params) (cutoff : ℕ) :
    ((significantTimedSnapshots cutoff snapshots).map fun timed => max (error timed) 0).sum ≤
      ((((1 + params.growingLimit) * cutoff + 1) *
        totalValueChanges operations : ℕ) : ℤ) := by
  have row : ∀ timed : TimedAnnotatedPairShiftSnapshot n,
      max (error timed) 0 ≤ |timed.annotated.snapshot.vShift| +
        |timed.annotated.snapshot.uShift| + (loserUpward timed : ℤ) := by
    intro timed
    have v := le_abs_self timed.annotated.snapshot.vShift
    have u := le_abs_self timed.annotated.snapshot.uShift
    have vn := abs_nonneg timed.annotated.snapshot.vShift
    have un := abs_nonneg timed.annotated.snapshot.uShift
    unfold error loserUpward
    omega
  have aggregate : ∀ rows : List (TimedAnnotatedPairShiftSnapshot n),
      (rows.map fun timed => max (error timed) 0).sum ≤
        (rows.map fun timed => |timed.annotated.snapshot.vShift| +
          |timed.annotated.snapshot.uShift|).sum + (rows.map loserUpward).sum := by
    intro rows
    induction rows with
    | nil => simp
    | cons timed rows ih =>
        have rowBound := row timed
        simp only [List.map_cons, List.sum_cons, Nat.cast_add] at ih ⊢
        omega
  have filtered : ((significantTimedSnapshots cutoff snapshots).map loserUpward).sum ≤
      (snapshots.map loserUpward).sum := by
    clear history initialState
    induction snapshots with
    | nil => simp [significantTimedSnapshots]
    | cons timed snapshots ih =>
        by_cases low : timed.annotated.sourcePassCount < cutoff <;>
          simp [significantTimedSnapshots, AnnotatedPairShiftSnapshot.significantDecision,
            low] at ih ⊢ <;> omega
  have los := filtered.trans (history_loser_upward_le history)
  have vu := ActualAbsoluteShiftBudget.early_absolute_v_u history initialState cutoff
  have all := aggregate (significantTimedSnapshots cutoff snapshots)
  have losInt :
      (((significantTimedSnapshots cutoff snapshots).map loserUpward).sum : ℤ) ≤
        (totalValueChanges operations : ℤ) := by exact_mod_cast los
  apply all.trans
  calc
    _ ≤ (((1 + params.growingLimit) * cutoff * totalValueChanges operations : ℕ) : ℤ) +
        (totalValueChanges operations : ℤ) := add_le_add vu losInt
    _ = _ := by push_cast; ring

end Splay.Research.ActualTimedErrorBudget
