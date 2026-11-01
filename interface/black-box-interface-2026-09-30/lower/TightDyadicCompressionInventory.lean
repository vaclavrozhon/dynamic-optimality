import ActualHistoricalLabelInventory

namespace Splay.Research.TightDyadicCompressionInventory
open Splay.Interface Splay.Research.ActualHistoricalLabelInventory

theorem step_balance_tight {n : ℕ} {R : ℕ} (rankLabel : ℕ → ℕ)
    (positiveLabel : ∀ rank, 1 ≤ rankLabel rank)
    (boundedLabel : ∀ rank, rankLabel rank ≤ R)
    (before : State n) (labels : RootLabels) (ledger : EpisodeLedger n)
    (operation : Operation n) :
    negative rankLabel before labels ledger operation +
      inventory rankLabel (EpisodeLedger.after before labels ledger operation) ≤
      inventory rankLabel ledger + positive rankLabel before labels ledger operation +
        (R-1) * operation.insertCount := by
  cases operation with
  | pass source matching =>
      simpa [Operation.insertCount] using (pass_balance rankLabel before labels ledger source matching).le
  | insert destination element =>
      let start := EpisodeStart.ofJoin before
        (makeJoinOccurrence before labels .insert element destination element)
      have update := inventory_update rankLabel ledger element (some start)
      have bound := boundedLabel (historicalRank start)
      have oldPositive := nominal_pos rankLabel positiveLabel ledger element
      have rPositive := (positiveLabel 0).trans (boundedLabel 0)
      simp only [negative, positive, Operation.insertCount, Nat.mul_one,
        Nat.zero_add, Nat.add_zero, EpisodeLedger.after]
      change inventory rankLabel (Function.update ledger element (some start)) ≤ _
      simp only at update
      omega
  | delete source element =>
      have update := inventory_update rankLabel ledger element none
      have oldPositive := nominal_pos rankLabel positiveLabel ledger element
      simp only [negative, positive, Operation.insertCount, Nat.mul_zero,
        Nat.zero_add, Nat.add_zero, EpisodeLedger.after]
      simp only at update
      omega
  | convert source => simp [negative, positive, EpisodeLedger.after, Operation.insertCount]
  | create creator => simp [negative, positive, EpisodeLedger.after, Operation.insertCount]
  | split source length => simp [negative, positive, EpisodeLedger.after, Operation.insertCount]
  | valueChange element delta =>
      simp [negative, positive, EpisodeLedger.after, Operation.insertCount]

theorem history_balance_tight {n : ℕ} {params : Parameters} {rankLabel : ℕ → ℕ} {R : ℕ}
    (positiveLabel : ∀ rank, 1 ≤ rankLabel rank)
    (boundedLabel : ∀ rank, rankLabel rank ≤ R)
    {initial final : State n} {initialLabels finalLabels : RootLabels}
    {initialLedger finalLedger : EpisodeLedger n}
    {operations : List (Operation n)} {P N : ℕ}
    (history : History params rankLabel initial initialLabels initialLedger operations P N
      final finalLabels finalLedger) :
    N + inventory rankLabel finalLedger ≤
      inventory rankLabel initialLedger + P + (R-1) * totalInserts operations := by
  induction history with
  | nil valid => simp [totalInserts]
  | @cons before middle final beforeLabels finalLabels beforeLedger finalLedger
      operation operations P N head tail ih =>
      have localBound := step_balance_tight rankLabel positiveLabel boundedLabel
        before beforeLabels beforeLedger operation
      simp only [totalInserts, List.map_cons, List.sum_cons, Nat.mul_add] at ih ⊢
      omega

theorem negative_le_insert_add_positive_tight {n : ℕ} {params : Parameters}
    {rankLabel : ℕ → ℕ} {R : ℕ}
    (positiveLabel : ∀ rank, 1 ≤ rankLabel rank)
    (boundedLabel : ∀ rank, rankLabel rank ≤ R)
    {initial final : State n} {initialLabels finalLabels : RootLabels}
    {finalLedger : EpisodeLedger n} {operations : List (Operation n)} {P N : ℕ}
    (history : History params rankLabel initial initialLabels
      (EpisodeLedger.empty : EpisodeLedger n) operations P N final finalLabels finalLedger) :
    N ≤ (R-1) * totalInserts operations + P := by
  have balance := history_balance_tight positiveLabel boundedLabel history
  rw [inventory_empty] at balance
  have finalLower := inventory_lower rankLabel positiveLabel finalLedger
  omega

end Splay.Research.TightDyadicCompressionInventory

#print axioms Splay.Research.TightDyadicCompressionInventory.negative_le_insert_add_positive_tight
