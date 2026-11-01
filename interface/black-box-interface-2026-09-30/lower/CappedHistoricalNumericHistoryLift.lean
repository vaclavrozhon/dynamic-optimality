import CappedHistoricalNumericStepLift

/-! Whole literal LifetimeHistory numerical lifting. Both the original
ledger path and exact Pass-preparation totals are retained, alongside one
actual new interface trace with identical A/I/Q. No projected trace or
intermediate numerical witness is an assumption. -/

namespace Splay.Research.CappedHistoricalNumericHistoryLift

open Splay.Interface Splay.Research.ActualHistoricalLabelInventory
open Splay.Research.CappedHistoricalNumericStepLift Splay.Research.VirtualNumericInsertion

/-- Actual original history with its deterministic Pass-rise and loser
preparation sums. Every state and ledger is indexed by the real step. -/
inductive PreparationHistory {n : ℕ} (params : Parameters) (rankLabel : ℕ → ℕ) :
    State n → RootLabels → EpisodeLedger n → List (Operation n) → ℕ → ℕ →
      State n → RootLabels → EpisodeLedger n → Prop
  | nil {state : State n} {labels : RootLabels} {ledger : EpisodeLedger n} (valid : state.Valid params) :
      PreparationHistory params rankLabel state labels ledger [] 0 0 state labels ledger
  | cons {before middle final : State n} {beforeLabels finalLabels : RootLabels}
      {beforeLedger finalLedger : EpisodeLedger n} {operation : Operation n} {operations : List (Operation n)}
      {P J : ℕ} (head : Step params before operation middle)
      (tail : PreparationHistory params rankLabel middle (RootLabels.after beforeLabels operation)
        (EpisodeLedger.after before beforeLabels beforeLedger operation) operations P J final finalLabels finalLedger) :
      PreparationHistory params rankLabel before beforeLabels beforeLedger (operation::operations)
        (positive rankLabel before beforeLabels beforeLedger operation+P)
        (preparation rankLabel before beforeLedger operation+J) final finalLabels finalLedger

theorem PreparationHistory.from_lifetime {n : ℕ} {params : Parameters} (rankLabel : ℕ → ℕ)
    {initial final : State n} {initialLabels finalLabels : RootLabels} {initialLedger finalLedger : EpisodeLedger n}
    {operations : List (Operation n)} {joins : List (JoinOccurrence n)} {leaves : List (LeaveOccurrence n)}
    {closed : List (ClosedEpisode n)}
    (history : LifetimeHistory params initial initialLabels initialLedger operations joins leaves closed final finalLabels finalLedger) :
    ∃ P J, PreparationHistory params rankLabel initial initialLabels initialLedger operations P J final finalLabels finalLedger := by
  induction history with
  | nil valid => exact ⟨0,0,.nil valid⟩
  | cons head tail ih =>
      obtain ⟨P,J,recorded⟩ := ih
      exact ⟨_,_,.cons head recorded⟩

theorem PreparationHistory.inventory_history {n : ℕ} {params : Parameters} {rankLabel : ℕ → ℕ}
    {initial final : State n} {initialLabels finalLabels : RootLabels} {initialLedger finalLedger : EpisodeLedger n}
    {operations : List (Operation n)} {P J : ℕ}
    (history : PreparationHistory params rankLabel initial initialLabels initialLedger operations P J final finalLabels finalLedger) :
    ∃ N, ActualHistoricalLabelInventory.History params rankLabel initial initialLabels initialLedger operations P N
      final finalLabels finalLedger := by
  induction history with
  | nil valid => exact ⟨0,.nil valid⟩
  | cons head tail ih =>
      obtain ⟨N,recorded⟩ := ih
      exact ⟨_,.cons head recorded⟩

/-- One legal new trace follows the complete actual original chronology.
The bill is upward variation; it is not signed/net or absolute variation. -/
theorem PreparationHistory.realize {n R : ℕ} {oldParams params : Parameters} {rankLabel : ℕ → ℕ}
    {initial final : State n} {initialLabels finalLabels : RootLabels} {initialLedger finalLedger : EpisodeLedger n}
    {operations : List (Operation n)} {P J : ℕ}
    (history : PreparationHistory oldParams rankLabel initial initialLabels initialLedger operations P J final finalLabels finalLedger)
    (sameShape : params.toShape = oldParams.toShape)
    (positiveLabel : ∀ rank, 1 ≤ rankLabel rank) (boundedLabel : ∀ rank, rankLabel rank ≤ R)
    (two : 2 ≤ R) (cap : R ≤ params.valueBound) :
    ∃ liftedOperations,
      Trace params (CappedHistoricalNumericStepLift.state rankLabel initial initialLedger) liftedOperations
        (CappedHistoricalNumericStepLift.state rankLabel final finalLedger) ∧
      totalActivity liftedOperations = totalActivity operations ∧
      totalBlockGrowth liftedOperations = totalBlockGrowth operations ∧
      totalInserts liftedOperations = totalInserts operations ∧
      totalIncreases liftedOperations ≤ J+P+R*totalInserts operations := by
  induction history with
  | nil valid =>
      exact ⟨[], .nil (state_valid rankLabel _ _ valid sameShape positiveLabel boundedLabel cap), rfl,rfl,rfl,by simp [totalIncreases,totalInserts]⟩
  | @cons before middle final beforeLabels finalLabels beforeLedger finalLedger operation operations P J head tail ih =>
      obtain ⟨first,firstTrace,firstActivity,firstGrowth,firstInserts,firstCost⟩ :=
        CappedHistoricalNumericStepLift.realize rankLabel head beforeLabels beforeLedger sameShape positiveLabel boundedLabel two cap
      obtain ⟨rest,restTrace,restActivity,restGrowth,restInserts,restCost⟩ := ih
      refine ⟨first++rest, trace_append firstTrace restTrace, ?_, ?_, ?_, ?_⟩
      · rw [totalActivity_append, firstActivity, restActivity]
        rfl
      · rw [totalBlockGrowth_append, firstGrowth, restGrowth]
        rfl
      · rw [totalInserts_append, firstInserts, restInserts]
        rfl
      · rw [totalIncreases_append]
        change _ ≤ _+_+R*(operation.insertCount+totalInserts operations)
        rw [Nat.mul_add]
        unfold charge at firstCost
        omega

/-- Public original-history endpoint. The preparatory tally and the
existing nominal inventory tally share this exact original operation list. -/
theorem from_lifetime {n R : ℕ} {oldParams params : Parameters} (rankLabel : ℕ → ℕ)
    {initial final : State n} {initialLabels finalLabels : RootLabels} {initialLedger finalLedger : EpisodeLedger n}
    {operations : List (Operation n)} {joins : List (JoinOccurrence n)} {leaves : List (LeaveOccurrence n)}
    {closed : List (ClosedEpisode n)}
    (history : LifetimeHistory oldParams initial initialLabels initialLedger operations joins leaves closed final finalLabels finalLedger)
    (sameShape : params.toShape = oldParams.toShape)
    (positiveLabel : ∀ rank, 1 ≤ rankLabel rank) (boundedLabel : ∀ rank, rankLabel rank ≤ R)
    (two : 2 ≤ R) (cap : R ≤ params.valueBound) :
    ∃ P J N liftedOperations,
      PreparationHistory oldParams rankLabel initial initialLabels initialLedger operations P J final finalLabels finalLedger ∧
      ActualHistoricalLabelInventory.History oldParams rankLabel initial initialLabels initialLedger operations P N
        final finalLabels finalLedger ∧
      Trace params (CappedHistoricalNumericStepLift.state rankLabel initial initialLedger) liftedOperations
        (CappedHistoricalNumericStepLift.state rankLabel final finalLedger) ∧
      totalActivity liftedOperations = totalActivity operations ∧
      totalBlockGrowth liftedOperations = totalBlockGrowth operations ∧
      totalInserts liftedOperations = totalInserts operations ∧
      totalIncreases liftedOperations ≤ J+P+R*totalInserts operations := by
  obtain ⟨P,J,recorded⟩ := PreparationHistory.from_lifetime rankLabel history
  obtain ⟨N,inventory⟩ := recorded.inventory_history
  obtain ⟨liftedOperations,trace,activity,growth,inserts,upward⟩ :=
    recorded.realize sameShape positiveLabel boundedLabel two cap
  exact ⟨P,J,N,liftedOperations,recorded,inventory,trace,activity,growth,inserts,upward⟩

/-- From the ordinary original initialized trace itself: the lifetime
ledger and both exact accounting witnesses are constructed automatically.
Unit initial labels make downward changes at most upward changes, without
an additional n times the numeric cap term. -/
theorem from_initial_trace {n R : ℕ} {oldParams params : Parameters} (rankLabel : ℕ → ℕ)
    {initial final : State n} {operations : List (Operation n)}
    (initialState : initial.Initial oldParams) (original : Trace oldParams initial operations final)
    (sameShape : params.toShape = oldParams.toShape)
    (positiveLabel : ∀ rank, 1 ≤ rankLabel rank) (boundedLabel : ∀ rank, rankLabel rank ≤ R)
    (two : 2 ≤ R) (cap : R ≤ params.valueBound) :
    ∃ finalLabels finalLedger P J N liftedOperations,
      PreparationHistory oldParams rankLabel initial [] (EpisodeLedger.empty : EpisodeLedger n)
        operations P J final finalLabels finalLedger ∧
      ActualHistoricalLabelInventory.History oldParams rankLabel initial [] (EpisodeLedger.empty : EpisodeLedger n)
        operations P N final finalLabels finalLedger ∧
      (CappedHistoricalNumericStepLift.state rankLabel initial EpisodeLedger.empty).Initial params ∧
      Trace params (CappedHistoricalNumericStepLift.state rankLabel initial EpisodeLedger.empty) liftedOperations
        (CappedHistoricalNumericStepLift.state rankLabel final finalLedger) ∧
      totalActivity liftedOperations = totalActivity operations ∧
      totalBlockGrowth liftedOperations = totalBlockGrowth operations ∧
      totalInserts liftedOperations = totalInserts operations ∧
      totalIncreases liftedOperations ≤ J+P+R*totalInserts operations ∧
      totalValueChanges liftedOperations ≤ 2*(J+P+R*totalInserts operations) ∧
      N ≤ R*totalInserts operations+P := by
  obtain ⟨finalLabels,finalLedger,joins,leaves,closed,lifetime,aligned,exactLedger,counts⟩ :=
    LifetimeHistory.lift_initial initialState original
  obtain ⟨P,J,N,liftedOperations,recorded,inventoryHistory,trace,activity,growth,inserts,upward⟩ :=
    from_lifetime rankLabel lifetime sameShape positiveLabel boundedLabel two cap
  have balance := trace.totalValue_balance
  change inventory rankLabel finalLedger+totalDecreases liftedOperations =
    inventory rankLabel (EpisodeLedger.empty : EpisodeLedger n)+totalIncreases liftedOperations at balance
  rw [inventory_empty] at balance
  have lower := inventory_lower rankLabel positiveLabel finalLedger
  have changes := totalValueChanges_eq liftedOperations
  refine ⟨finalLabels,finalLedger,P,J,N,liftedOperations,recorded,inventoryHistory,
    ⟨state_valid rankLabel initial EpisodeLedger.empty initialState.1 sameShape positiveLabel boundedLabel cap,
      initialState.2⟩,trace,activity,growth,inserts,upward,?_,
    inventoryHistory.negative_le_insert_add_positive positiveLabel boundedLabel⟩
  omega

end Splay.Research.CappedHistoricalNumericHistoryLift

#print axioms Splay.Research.CappedHistoricalNumericHistoryLift.from_lifetime

#print axioms Splay.Research.CappedHistoricalNumericHistoryLift.from_initial_trace
