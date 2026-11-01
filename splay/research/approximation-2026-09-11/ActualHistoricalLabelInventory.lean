import Splay.Interface.LifetimeHistory
import Splay.Interface.Potential
import Mathlib.Tactic

namespace Splay.Research.ActualHistoricalLabelInventory

open Splay.Interface
open scoped BigOperators

def historicalRank {n : ℕ} (start : EpisodeStart n) : ℕ :=
  start.join.valueAtJoin - start.creatorValueAtJoin

def nominal {n : ℕ} (rankLabel : ℕ → ℕ) (ledger : EpisodeLedger n)
    (element : Element n) : ℕ :=
  match ledger element with
  | none => 1
  | some start => rankLabel (historicalRank start)

def inventory {n : ℕ} (rankLabel : ℕ → ℕ) (ledger : EpisodeLedger n) : ℕ :=
  ∑ element : Element n, nominal rankLabel ledger element

def positive {n : ℕ} (rankLabel : ℕ → ℕ) (before : State n)
    (labels : RootLabels) (ledger : EpisodeLedger n) (operation : Operation n) : ℕ :=
  match operation with
  | .pass _ _ => ∑ element : Element n,
      (nominal rankLabel (EpisodeLedger.after before labels ledger operation) element -
        nominal rankLabel ledger element)
  | _ => 0

def negative {n : ℕ} (rankLabel : ℕ → ℕ) (before : State n)
    (labels : RootLabels) (ledger : EpisodeLedger n) (operation : Operation n) : ℕ :=
  match operation with
  | .pass _ _ => ∑ element : Element n,
      (nominal rankLabel ledger element -
        nominal rankLabel (EpisodeLedger.after before labels ledger operation) element)
  | _ => 0

theorem nominal_pos {n : ℕ} (rankLabel : ℕ → ℕ)
    (positiveLabel : ∀ rank, 1 ≤ rankLabel rank)
    (ledger : EpisodeLedger n) (element : Element n) :
    1 ≤ nominal rankLabel ledger element := by
  cases active : ledger element with
  | none => simp [nominal, active]
  | some start => simpa [nominal, active] using positiveLabel (historicalRank start)

theorem inventory_lower {n : ℕ} (rankLabel : ℕ → ℕ)
    (positiveLabel : ∀ rank, 1 ≤ rankLabel rank) (ledger : EpisodeLedger n) :
    2 * n + 1 ≤ inventory rankLabel ledger := by
  have bound : (∑ _element : Element n, (1 : ℕ)) ≤ inventory rankLabel ledger :=
    Finset.sum_le_sum fun element _ => nominal_pos rankLabel positiveLabel ledger element
  simpa using bound

@[simp] theorem inventory_empty {n : ℕ} (rankLabel : ℕ → ℕ) :
    inventory rankLabel (EpisodeLedger.empty : EpisodeLedger n) = 2 * n + 1 := by
  simp [inventory, nominal, EpisodeLedger.empty]

theorem inventory_update {n : ℕ} (rankLabel : ℕ → ℕ)
    (ledger : EpisodeLedger n) (element : Element n) (start : Option (EpisodeStart n)) :
    inventory rankLabel (Function.update ledger element start) +
        nominal rankLabel ledger element =
      inventory rankLabel ledger +
        (match start with | none => 1 | some item => rankLabel (historicalRank item)) := by
  let newValue := match start with
    | none => 1
    | some item => rankLabel (historicalRank item)
  have pointwise : nominal rankLabel (Function.update ledger element start) =
      Function.update (nominal rankLabel ledger) element newValue := by
    funext candidate
    by_cases same : candidate = element
    · subst candidate; simp [nominal, newValue]
    · simp [nominal, Function.update, same]
  have member : element ∈ (Finset.univ : Finset (Element n)) := Finset.mem_univ _
  have newSum := Finset.sum_update_of_mem member (nominal rankLabel ledger) newValue
  have oldSum := Finset.sum_update_of_mem member (nominal rankLabel ledger)
    (nominal rankLabel ledger element)
  simp only [Function.update_eq_self] at oldSum
  unfold inventory
  rw [pointwise, newSum, oldSum]
  omega

/-- Pointwise positive and negative parts give the exact Pass inventory
balance; this does not assume any numeric ordering of the new labels. -/
theorem pass_balance {n : ℕ} (rankLabel : ℕ → ℕ) (before : State n)
    (labels : RootLabels) (ledger : EpisodeLedger n)
    (source : BlockId) (matching : List (Pairing n)) :
    negative rankLabel before labels ledger (.pass source matching) +
      inventory rankLabel (EpisodeLedger.after before labels ledger (.pass source matching)) =
      inventory rankLabel ledger +
        positive rankLabel before labels ledger (.pass source matching) := by
  unfold negative positive inventory
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro element _
  omega

theorem step_balance {n : ℕ} {R : ℕ} (rankLabel : ℕ → ℕ)
    (positiveLabel : ∀ rank, 1 ≤ rankLabel rank)
    (boundedLabel : ∀ rank, rankLabel rank ≤ R)
    (before : State n) (labels : RootLabels) (ledger : EpisodeLedger n)
    (operation : Operation n) :
    negative rankLabel before labels ledger operation +
      inventory rankLabel (EpisodeLedger.after before labels ledger operation) ≤
      inventory rankLabel ledger + positive rankLabel before labels ledger operation +
        R * operation.insertCount := by
  cases operation with
  | pass source matching =>
      simpa [Operation.insertCount] using (pass_balance rankLabel before labels ledger source matching).le
  | insert destination element =>
      let start := EpisodeStart.ofJoin before
        (makeJoinOccurrence before labels .insert element destination element)
      have update := inventory_update rankLabel ledger element (some start)
      have bound := boundedLabel (historicalRank start)
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

/-- A literal original execution decorated only by its deterministic sums
of positive/negative Pass relabeling. -/
inductive History {n : ℕ} (params : Parameters) (rankLabel : ℕ → ℕ) :
    State n → RootLabels → EpisodeLedger n → List (Operation n) → ℕ → ℕ →
      State n → RootLabels → EpisodeLedger n → Prop
  | nil {state : State n} {labels : RootLabels} {ledger : EpisodeLedger n}
      (valid : state.Valid params) :
      History params rankLabel state labels ledger [] 0 0 state labels ledger
  | cons {before middle final : State n} {beforeLabels finalLabels : RootLabels}
      {beforeLedger finalLedger : EpisodeLedger n}
      {operation : Operation n} {operations : List (Operation n)} {P N : ℕ}
      (head : Step params before operation middle)
      (tail : History params rankLabel middle (RootLabels.after beforeLabels operation)
        (EpisodeLedger.after before beforeLabels beforeLedger operation)
        operations P N final finalLabels finalLedger) :
      History params rankLabel before beforeLabels beforeLedger (operation :: operations)
        (positive rankLabel before beforeLabels beforeLedger operation + P)
        (negative rankLabel before beforeLabels beforeLedger operation + N)
        final finalLabels finalLedger

theorem from_lifetime {n : ℕ} {params : Parameters} (rankLabel : ℕ → ℕ)
    {initial final : State n} {initialLabels finalLabels : RootLabels}
    {initialLedger finalLedger : EpisodeLedger n}
    {operations : List (Operation n)} {joins : List (JoinOccurrence n)}
    {leaves : List (LeaveOccurrence n)} {closed : List (ClosedEpisode n)}
    (history : LifetimeHistory params initial initialLabels initialLedger
      operations joins leaves closed final finalLabels finalLedger) :
    ∃ P N, History params rankLabel initial initialLabels initialLedger operations P N
      final finalLabels finalLedger := by
  induction history with
  | nil valid => exact ⟨0, 0, .nil valid⟩
  | cons head tail ih =>
      obtain ⟨P, N, recorded⟩ := ih
      exact ⟨_, _, .cons head recorded⟩

theorem History.balance {n : ℕ} {params : Parameters} {rankLabel : ℕ → ℕ} {R : ℕ}
    (positiveLabel : ∀ rank, 1 ≤ rankLabel rank)
    (boundedLabel : ∀ rank, rankLabel rank ≤ R)
    {initial final : State n} {initialLabels finalLabels : RootLabels}
    {initialLedger finalLedger : EpisodeLedger n}
    {operations : List (Operation n)} {P N : ℕ}
    (history : History params rankLabel initial initialLabels initialLedger operations P N
      final finalLabels finalLedger) :
    N + inventory rankLabel finalLedger ≤
      inventory rankLabel initialLedger + P + R * totalInserts operations := by
  induction history with
  | nil valid => simp [totalInserts]
  | @cons before middle final beforeLabels finalLabels beforeLedger finalLedger
      operation operations P N head tail ih =>
      have localBound := step_balance rankLabel positiveLabel boundedLabel
        before beforeLabels beforeLedger operation
      simp only [totalInserts, List.map_cons, List.sum_cons, Nat.mul_add] at ih ⊢
      omega

theorem History.negative_le_insert_add_positive {n : ℕ} {params : Parameters}
    {rankLabel : ℕ → ℕ} {R : ℕ}
    (positiveLabel : ∀ rank, 1 ≤ rankLabel rank)
    (boundedLabel : ∀ rank, rankLabel rank ≤ R)
    {initial final : State n} {initialLabels finalLabels : RootLabels}
    {finalLedger : EpisodeLedger n} {operations : List (Operation n)} {P N : ℕ}
    (history : History params rankLabel initial initialLabels
      (EpisodeLedger.empty : EpisodeLedger n) operations P N final finalLabels finalLedger) :
    N ≤ R * totalInserts operations + P := by
  have balance := history.balance positiveLabel boundedLabel
  rw [inventory_empty] at balance
  have finalLower := inventory_lower rankLabel positiveLabel finalLedger
  omega

end Splay.Research.ActualHistoricalLabelInventory
