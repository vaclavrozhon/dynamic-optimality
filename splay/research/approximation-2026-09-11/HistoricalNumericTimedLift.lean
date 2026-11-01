import HistoricalNumericHistoryLift
import ActualRelabelRows

/-! The compiler's preparation and nominal-rise charges are exactly the
sums over the original timed Pass rows used by the scalar/error budget.
The resulting trace is constructed from that same literal timed history. -/

namespace Splay.Research.HistoricalNumericTimedLift
open Splay.Interface Splay.Research.ActualHistoricalLabelInventory
open Splay.Research.ActualRelabelRows Splay.Research.HistoricalNumericStepLift
open Splay.Research.HistoricalNumericHistoryLift

theorem pass_preparation {n : ℕ} {params : Parameters} (rankLabel : ℕ → ℕ)
    {before after : State n} {labels : RootLabels} {ledger : EpisodeLedger n}
    {source : BlockId} {matching : List (Pairing n)}
    (clock : EpisodeClock n) (events : List (ValueChangeEvent n))
    (exact : EpisodeLedger.ExactAt before labels ledger)
    (step : Step params before (.pass source matching) after) (aligned : labels.length = before.blocks.length) :
    ((timedLifetimePassSnapshots clock events exact step aligned).map (rowPreparation rankLabel)).sum =
      preparation rankLabel before ledger (.pass source matching) := by
  unfold timedLifetimePassSnapshots
  simp only [List.map_map, Function.comp_def]
  have mapped : (matching.attach.map fun pairing => rowPreparation rankLabel
      (TimedAnnotatedPairShiftSnapshot.ofLifetimePass clock events exact step aligned pairing.2)) =
      (matching.attach.map fun pairing => VirtualLoserPreparation.deficit
        (HistoricalNumericStepLift.state rankLabel before ledger) pairing.1) := by
    apply List.map_congr_left
    intro pairing member
    let starts := exact.pass_pairing_starts step aligned pairing.2
    change rankLabel (historicalRank starts.winnerStart)+1-rankLabel (historicalRank starts.loserStart) =
      nominal rankLabel ledger pairing.1.winner+1-nominal rankLabel ledger pairing.1.loser
    simp only [nominal, starts.winnerActive, starts.loserActive]
  rw [mapped]
  simp [preparation]

theorem operation_preparation {n : ℕ} {params : Parameters} (rankLabel : ℕ → ℕ)
    (before after : State n) (labels : RootLabels) (ledger : EpisodeLedger n)
    (clock : EpisodeClock n) (events : List (ValueChangeEvent n)) (operation : Operation n)
    (exact : EpisodeLedger.ExactAt before labels ledger) (step : Step params before operation after)
    (aligned : labels.length = before.blocks.length) :
    ((operationTimedPairShiftSnapshots before after labels ledger clock events operation exact step aligned).map
      (rowPreparation rankLabel)).sum = preparation rankLabel before ledger operation := by
  cases operation with
  | pass source matching => exact pass_preparation rankLabel clock events exact step aligned
  | _ => rfl

/-- Both scalar charge sums use the exact same original rows and history. -/
theorem recorded {n : ℕ} {params : Parameters} (rankLabel : ℕ → ℕ)
    {initial final : State n} {initialLabels finalLabels : RootLabels}
    {initialLedger finalLedger : EpisodeLedger n} {initialClock finalClock : EpisodeClock n}
    {initialEvents finalEvents : List (ValueChangeEvent n)} {operations : List (Operation n)}
    {snapshots : List (TimedAnnotatedPairShiftSnapshot n)}
    (history : LifetimeHistory.TimedPairShiftHistory params initial initialLabels initialLedger
      initialClock initialEvents operations snapshots final finalLabels finalLedger finalClock finalEvents) :
    PreparationHistory params rankLabel initial initialLabels initialLedger operations
      (snapshots.map (rowPositive rankLabel)).sum (snapshots.map (rowPreparation rankLabel)).sum
      final finalLabels finalLedger := by
  induction history with
  | nil valid sound => exact .nil valid
  | @cons before middle final beforeLabels finalLabels beforeLedger finalLedger
      beforeClock finalClock beforeEvents finalEvents operation operations tailSnapshots
      aligned exact sound head tail ih =>
      have rows := operation_rows rankLabel before middle beforeLabels beforeLedger
        beforeClock beforeEvents operation exact sound head aligned
      have prepares := operation_preparation rankLabel before middle beforeLabels beforeLedger
        beforeClock beforeEvents operation exact head aligned
      simpa only [List.map_append, List.sum_append, rows.1, prepares] using PreparationHistory.cons head ih

/-- Direct numerical compiler on the actual timed original history, with
exact A/I/Q and the original scalar-row budget. -/
theorem realize {n R : ℕ} {oldParams params : Parameters} (rankLabel : ℕ → ℕ)
    {initial final : State n} {initialLabels finalLabels : RootLabels}
    {initialLedger finalLedger : EpisodeLedger n} {initialClock finalClock : EpisodeClock n}
    {initialEvents finalEvents : List (ValueChangeEvent n)} {operations : List (Operation n)}
    {snapshots : List (TimedAnnotatedPairShiftSnapshot n)}
    (history : LifetimeHistory.TimedPairShiftHistory oldParams initial initialLabels initialLedger
      initialClock initialEvents operations snapshots final finalLabels finalLedger finalClock finalEvents)
    (sameShape : params.toShape = oldParams.toShape)
    (positiveLabel : ∀ rank, 1 ≤ rankLabel rank) (boundedLabel : ∀ rank, rankLabel rank ≤ R)
    (cap : R+1 ≤ params.valueBound) :
    ∃ liftedOperations,
      Trace params (HistoricalNumericStepLift.state rankLabel initial initialLedger) liftedOperations
        (HistoricalNumericStepLift.state rankLabel final finalLedger) ∧
      totalActivity liftedOperations = totalActivity operations ∧
      totalBlockGrowth liftedOperations = totalBlockGrowth operations ∧
      totalInserts liftedOperations = totalInserts operations ∧
      totalIncreases liftedOperations ≤ (snapshots.map (rowPreparation rankLabel)).sum +
        (snapshots.map (rowPositive rankLabel)).sum + R*totalInserts operations :=
  (recorded rankLabel history).realize sameShape positiveLabel boundedLabel cap

/-- The empty original residence ledger gives unit initial labels. The
whole compiled trace therefore has at most twice its upward variation,
without a universe-size or initial-cap term. -/
theorem realize_of_initial {n R : ℕ} {oldParams params : Parameters} (rankLabel : ℕ → ℕ)
    {initial final : State n} {finalLabels : RootLabels}
    {finalLedger : EpisodeLedger n} {finalClock : EpisodeClock n}
    {finalEvents : List (ValueChangeEvent n)} {operations : List (Operation n)}
    {snapshots : List (TimedAnnotatedPairShiftSnapshot n)}
    (initialState : initial.Initial oldParams)
    (history : LifetimeHistory.TimedPairShiftHistory oldParams initial []
      (EpisodeLedger.empty : EpisodeLedger n) (fun _ => 0) []
      operations snapshots final finalLabels finalLedger finalClock finalEvents)
    (sameShape : params.toShape = oldParams.toShape)
    (positiveLabel : ∀ rank, 1 ≤ rankLabel rank) (boundedLabel : ∀ rank, rankLabel rank ≤ R)
    (cap : R+1 ≤ params.valueBound) :
    ∃ liftedOperations,
      (HistoricalNumericStepLift.state rankLabel initial EpisodeLedger.empty).Initial params ∧
      Trace params (HistoricalNumericStepLift.state rankLabel initial EpisodeLedger.empty) liftedOperations
        (HistoricalNumericStepLift.state rankLabel final finalLedger) ∧
      totalActivity liftedOperations = totalActivity operations ∧
      totalBlockGrowth liftedOperations = totalBlockGrowth operations ∧
      totalInserts liftedOperations = totalInserts operations ∧
      totalValueChanges liftedOperations ≤ 2*((snapshots.map (rowPreparation rankLabel)).sum +
        (snapshots.map (rowPositive rankLabel)).sum + R*totalInserts operations) := by
  obtain ⟨liftedOperations, trace, activity, growth, inserts, upward⟩ :=
    realize rankLabel history sameShape positiveLabel boundedLabel cap
  have balance := trace.totalValue_balance
  change inventory rankLabel finalLedger+totalDecreases liftedOperations =
    inventory rankLabel (EpisodeLedger.empty : EpisodeLedger n)+totalIncreases liftedOperations at balance
  rw [inventory_empty] at balance
  have lower := inventory_lower rankLabel positiveLabel finalLedger
  have changes := totalValueChanges_eq liftedOperations
  refine ⟨liftedOperations,
    ⟨state_valid rankLabel initial EpisodeLedger.empty initialState.1 sameShape positiveLabel boundedLabel cap,
      initialState.2⟩, trace, activity, growth, inserts, ?_⟩
  omega

/-- Every ordinary initialized original trace constructs its own exact
timed rows and legal compressed trace. No chronological projection or
numeric lifting witness is assumed at this endpoint. -/
theorem from_initial_trace {n R : ℕ} {oldParams params : Parameters} (rankLabel : ℕ → ℕ)
    {initial final : State n} {operations : List (Operation n)}
    (initialState : initial.Initial oldParams) (original : Trace oldParams initial operations final)
    (sameShape : params.toShape = oldParams.toShape)
    (positiveLabel : ∀ rank, 1 ≤ rankLabel rank) (boundedLabel : ∀ rank, rankLabel rank ≤ R)
    (cap : R+1 ≤ params.valueBound) :
    ∃ finalLabels finalLedger finalClock finalEvents snapshots liftedOperations,
      LifetimeHistory.TimedPairShiftHistory oldParams initial []
        (EpisodeLedger.empty : EpisodeLedger n) (fun _ => 0) []
        operations snapshots final finalLabels finalLedger finalClock finalEvents ∧
      (HistoricalNumericStepLift.state rankLabel initial EpisodeLedger.empty).Initial params ∧
      Trace params (HistoricalNumericStepLift.state rankLabel initial EpisodeLedger.empty) liftedOperations
        (HistoricalNumericStepLift.state rankLabel final finalLedger) ∧
      totalActivity liftedOperations = totalActivity operations ∧
      totalBlockGrowth liftedOperations = totalBlockGrowth operations ∧
      totalInserts liftedOperations = totalInserts operations ∧
      totalValueChanges liftedOperations ≤ 2*((snapshots.map (rowPreparation rankLabel)).sum +
        (snapshots.map (rowPositive rankLabel)).sum + R*totalInserts operations) := by
  obtain ⟨finalLabels,finalLedger,joins,leaves,closed,lifetime,aligned,exactLedger,counts⟩ :=
    LifetimeHistory.lift_initial initialState original
  obtain ⟨finalClock,finalEvents,snapshots,timed⟩ :=
    lifetime.lift_timedPairShiftSnapshots (fun _ => 0) [] (by simp [initialState.2])
      (EpisodeLedger.ExactAt.initial initialState) (EpisodeClock.soundAt_empty initial (fun _ => 0) [])
  obtain ⟨liftedOperations, newInitial, trace, activity, growth, inserts, changes⟩ :=
    realize_of_initial rankLabel initialState timed sameShape positiveLabel boundedLabel cap
  exact ⟨finalLabels,finalLedger,finalClock,finalEvents,snapshots,liftedOperations,
    timed,newInitial,trace,activity,growth,inserts,changes⟩

end Splay.Research.HistoricalNumericTimedLift

#print axioms Splay.Research.HistoricalNumericTimedLift.recorded
#print axioms Splay.Research.HistoricalNumericTimedLift.realize
#print axioms Splay.Research.HistoricalNumericTimedLift.from_initial_trace
