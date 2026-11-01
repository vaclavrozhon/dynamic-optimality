import Splay.Interface.LifetimeHistory
import Splay.Interface.Potential
import Mathlib.Tactic

namespace Splay.Research.ActualLoserUpwardBudget

open Splay.Interface
open scoped BigOperators

def upward {n : ℕ} (value : ℕ) (start : Option (EpisodeStart n)) : ℕ :=
  match start with
  | none => 0
  | some start => value - start.join.valueAtJoin

def inventory {n : ℕ} (state : State n) (ledger : EpisodeLedger n) : ℕ :=
  ∑ element : Element n, upward (state.value element) (ledger element)

def closedUpward {n : ℕ} (episode : ClosedEpisode n) : ℕ :=
  episode.finish.valueAtLeave - episode.start.join.valueAtJoin

def passUpward {n : ℕ} (before : State n) (ledger : EpisodeLedger n) :
    Operation n → ℕ
  | .pass _ matching =>
      (matching.map fun pairing => upward (before.value pairing.loser)
        (ledger pairing.loser)).sum
  | _ => 0

private theorem sum_update_nat {n : ℕ} (f : Element n → ℕ)
    (element : Element n) (newValue : ℕ) :
    (∑ candidate, Function.update f element newValue candidate) + f element =
      (∑ candidate, f candidate) + newValue := by
  have member : element ∈ (Finset.univ : Finset (Element n)) := Finset.mem_univ _
  have newSum := Finset.sum_update_of_mem member f newValue
  have oldSum := Finset.sum_update_of_mem member f (f element)
  simp only [Function.update_eq_self] at oldSum
  rw [newSum, oldSum]
  omega

theorem inventory_update {n : ℕ} (state : State n)
    (ledger : EpisodeLedger n) (element : Element n)
    (start : Option (EpisodeStart n)) :
    inventory state (Function.update ledger element start) +
        upward (state.value element) (ledger element) =
      inventory state ledger + upward (state.value element) start := by
  have pointwise :
      (fun candidate => upward (state.value candidate)
        (Function.update ledger element start candidate)) =
      Function.update (fun candidate => upward (state.value candidate) (ledger candidate))
        element (upward (state.value element) start) := by
    funext candidate
    by_cases same : candidate = element
    · subst candidate; simp
    · simp [Function.update, same]
  unfold inventory
  rw [pointwise]
  exact sum_update_nat _ _ _

theorem inventory_value_update {n : ℕ} (state : State n)
    (ledger : EpisodeLedger n) (element : Element n) (newValue : ℕ) :
    inventory { state with value := Function.update state.value element newValue } ledger +
        upward (state.value element) (ledger element) =
      inventory state ledger + upward newValue (ledger element) := by
  have pointwise :
      (fun candidate => upward (Function.update state.value element newValue candidate)
        (ledger candidate)) =
      Function.update (fun candidate => upward (state.value candidate) (ledger candidate))
        element (upward newValue (ledger element)) := by
    funext candidate
    by_cases same : candidate = element
    · subst candidate; simp
    · simp [Function.update, same]
  unfold inventory
  rw [pointwise]
  exact sum_update_nat _ _ _

private theorem install_balance {n : ℕ} (before : State n)
    (labels : RootLabels) (source : BlockId) (ledger : EpisodeLedger n)
    (matching : List (Pairing n))
    (distinct : (pairingLosers matching).Nodup) :
    inventory before (EpisodeLedger.installPassJoins before labels source ledger matching) +
      (matching.map fun pairing => upward (before.value pairing.loser)
        (ledger pairing.loser)).sum = inventory before ledger := by
  induction matching generalizing ledger with
  | nil => simp [EpisodeLedger.installPassJoins]
  | cons pairing matching ih =>
      have fresh : pairing.loser ∉ pairingLosers matching := by
        simpa [pairingLosers] using (List.nodup_cons.mp distinct).1
      have tailDistinct : (pairingLosers matching).Nodup := by
        simpa [pairingLosers] using (List.nodup_cons.mp distinct).2
      let newStart := some (EpisodeStart.ofJoin before
        (makeJoinOccurrence before labels (.pass source pairing.winner)
          pairing.loser pairing.destination pairing.winner))
      let next := Function.update ledger pairing.loser newStart
      have nextBalance := ih next tailDistinct
      have chargeEq :
          (matching.map fun other => upward (before.value other.loser)
            (next other.loser)).sum =
          (matching.map fun other => upward (before.value other.loser)
            (ledger other.loser)).sum := by
        congr 1
        apply List.map_congr_left
        intro other member
        have otherNe : other.loser ≠ pairing.loser := by
          intro same
          apply fresh
          simp only [pairingLosers, List.mem_map]
          exact ⟨other, member, same⟩
        simp [next, Function.update, otherNe]
      rw [chargeEq] at nextBalance
      have reset := inventory_update before ledger pairing.loser newStart
      have resetZero : upward (before.value pairing.loser) newStart = 0 := by
        simp [newStart, upward, EpisodeStart.ofJoin, makeJoinOccurrence]
      simp only [resetZero, Nat.add_zero] at reset
      change inventory before
          (EpisodeLedger.installPassJoins before labels source next matching) +
        (upward (before.value pairing.loser) (ledger pairing.loser) +
          (matching.map fun other => upward (before.value other.loser)
            (ledger other.loser)).sum) = _
      change inventory before next +
        upward (before.value pairing.loser) (ledger pairing.loser) = inventory before ledger at reset
      calc
        _ = (inventory before (EpisodeLedger.installPassJoins before labels source next matching) +
            (matching.map fun other => upward (before.value other.loser)
              (ledger other.loser)).sum) +
            upward (before.value pairing.loser) (ledger pairing.loser) := by omega
        _ = inventory before next +
            upward (before.value pairing.loser) (ledger pairing.loser) := by rw [nextBalance]
        _ = inventory before ledger := reset

private theorem closed_sum_eq {n : ℕ} (before : State n)
    (labels : RootLabels) (ledger : EpisodeLedger n) (operation : Operation n) :
    ((operationClosedEpisodes before labels ledger operation).map closedUpward).sum =
      ((operationLeaveOccurrences before labels operation).map fun finish =>
        upward (before.value finish.element) (ledger finish.element)).sum := by
  have general : ∀ (leaves : List (LeaveOccurrence n)),
      (∀ finish ∈ leaves, finish.valueAtLeave = before.value finish.element) →
      ((leaves.filterMap fun finish => (ledger finish.element).map fun start =>
          ({ start := start, finish := finish } : ClosedEpisode n)).map closedUpward).sum =
        (leaves.map fun finish => upward (before.value finish.element)
          (ledger finish.element)).sum := by
    intro leaves correct
    induction leaves with
    | nil => simp
    | cons finish leaves ih =>
        have head := correct finish (by simp)
        have tail := ih (by intro later member; exact correct later (by simp [member]))
        cases active : ledger finish.element <;>
          simp [List.filterMap_cons, active, closedUpward, upward, head, tail]
  exact general _ (by
    intro finish member
    exact valueAtLeave_eq_of_mem_operationLeaveOccurrences member)

theorem passUpward_le_closed {n : ℕ} (before : State n)
    (labels : RootLabels) (ledger : EpisodeLedger n) (operation : Operation n) :
    passUpward before ledger operation ≤
      ((operationClosedEpisodes before labels ledger operation).map closedUpward).sum := by
  cases operation with
  | pass source matching =>
      rw [closed_sum_eq]
      simp [passUpward, operationLeaveOccurrences, makeLeaveOccurrence,
        List.map_map, Function.comp_def]
  | _ => simp [passUpward]

/-- A genuine pass pays every losing upward drift once and resets its entry
snapshot. All other changes cost at most one per original ValueChange. -/
theorem step_balance {n : ℕ} {params : Parameters}
    {before after : State n} {operation : Operation n}
    (labels : RootLabels) (ledger : EpisodeLedger n)
    (step : Step params before operation after) :
    ((operationClosedEpisodes before labels ledger operation).map closedUpward).sum +
      inventory after (EpisodeLedger.after before labels ledger operation) ≤
        inventory before ledger + operation.valueChangeCount := by
  rw [closed_sum_eq]
  cases step.2.1 with
  | convert found growing blocks values =>
      simp [operationLeaveOccurrences, EpisodeLedger.after, inventory,
        values, Operation.valueChangeCount]
  | create room blocks values =>
      simp [operationLeaveOccurrences, EpisodeLedger.after, inventory,
        values, Operation.valueChangeCount]
  | insert found growing unassigned order blocks values =>
      rename_i blockId block element
      have reset := inventory_update before ledger element
        (some (EpisodeStart.ofJoin before
          (makeJoinOccurrence before labels .insert element blockId element)))
      have zero : upward (before.value element)
          (some (EpisodeStart.ofJoin before
            (makeJoinOccurrence before labels .insert element blockId element))) = 0 := by
        simp [upward, EpisodeStart.ofJoin, makeJoinOccurrence]
      simp only [zero, Nat.add_zero] at reset
      simp only [operationLeaveOccurrences, List.map_nil, List.sum_nil,
        Nat.zero_add, Operation.valueChangeCount, Nat.add_zero, EpisodeLedger.after]
      have invEq : ∀ current, inventory after current = inventory before current := by
        intro current; simp [inventory, values]
      rw [invEq]
      omega
  | delete found shrinking present blocks values =>
      rename_i blockId block element
      have reset := inventory_update before ledger element none
      have zero : upward (before.value element) (none : Option (EpisodeStart n)) = 0 := rfl
      simp only [zero, Nat.add_zero] at reset
      simp only [operationLeaveOccurrences, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, Nat.add_zero, Operation.valueChangeCount,
        EpisodeLedger.after, makeLeaveOccurrence]
      have invEq : inventory after (Function.update ledger element none) =
          inventory before (Function.update ledger element none) := by
        simp [inventory, values]
      omega
  | pass found validMatching blocks values =>
      rename_i sourceId source matching
      have balance := install_balance before labels sourceId ledger matching
        (pairingLosers_nodup validMatching.2.1)
      simp only [operationLeaveOccurrences, List.map_map, Function.comp_def,
        makeLeaveOccurrence, Operation.valueChangeCount, Nat.add_zero,
        EpisodeLedger.after]
      have invEq : inventory after
          (EpisodeLedger.installPassJoins before labels sourceId ledger matching) =
          inventory before
          (EpisodeLedger.installPassJoins before labels sourceId ledger matching) := by
        simp [inventory, values]
      rw [invEq]
      omega
  | split found shrinking length blocks values =>
      simp [operationLeaveOccurrences, EpisodeLedger.after, inventory,
        values, Operation.valueChangeCount]
  | decrease possible blocks values =>
      rename_i element
      have change := inventory_value_update before ledger element (before.value element - 1)
      have point : upward (before.value element - 1) (ledger element) ≤
          upward (before.value element) (ledger element) := by
        cases ledger element <;> simp [upward] <;> omega
      have invEq : inventory after ledger =
          inventory { before with value := (Function.update before.value element
            (before.value element - 1)) } ledger := by simp [inventory, values]
      simp only [operationLeaveOccurrences, List.map_nil, List.sum_nil,
        Nat.zero_add, EpisodeLedger.after, Operation.valueChangeCount]
      rw [invEq]
      omega
  | increase possible blocks values =>
      rename_i element
      have change := inventory_value_update before ledger element (before.value element + 1)
      have point : upward (before.value element + 1) (ledger element) ≤
          upward (before.value element) (ledger element) + 1 := by
        cases ledger element <;> simp [upward] <;> omega
      have invEq : inventory after ledger =
          inventory { before with value := (Function.update before.value element
            (before.value element + 1)) } ledger := by simp [inventory, values]
      simp only [operationLeaveOccurrences, List.map_nil, List.sum_nil,
        Nat.zero_add, EpisodeLedger.after, Operation.valueChangeCount]
      rw [invEq]
      omega

theorem lifetime_balance {n : ℕ} {params : Parameters}
    {initial final : State n} {initialLabels finalLabels : RootLabels}
    {initialLedger finalLedger : EpisodeLedger n}
    {operations : List (Operation n)} {joins : List (JoinOccurrence n)}
    {leaves : List (LeaveOccurrence n)} {closed : List (ClosedEpisode n)}
    (history : LifetimeHistory params initial initialLabels initialLedger
      operations joins leaves closed final finalLabels finalLedger) :
    (closed.map closedUpward).sum + inventory final finalLedger ≤
      inventory initial initialLedger + totalValueChanges operations := by
  induction history with
  | nil valid => simp [totalValueChanges]
  | @cons before middle final beforeLabels finalLabels beforeLedger finalLedger
      operation operations tailJoins tailLeaves tailClosed head tail ih =>
      have step := step_balance beforeLabels beforeLedger head
      simp only [List.map_append, List.sum_append, totalValueChanges,
        List.map_cons, List.sum_cons] at ih ⊢
      omega

/-- Unconditional original-lifetime bound; no assumed episode incidence is
left. In particular the pass-loser subfamily costs at most original `V`. -/
theorem closed_upward_le_valueChanges {n : ℕ} {params : Parameters}
    {initial final : State n} {initialLabels finalLabels : RootLabels}
    {finalLedger : EpisodeLedger n}
    {operations : List (Operation n)} {joins : List (JoinOccurrence n)}
    {leaves : List (LeaveOccurrence n)} {closed : List (ClosedEpisode n)}
    (history : LifetimeHistory params initial initialLabels
      (EpisodeLedger.empty : EpisodeLedger n)
      operations joins leaves closed final finalLabels finalLedger) :
    (closed.map closedUpward).sum ≤ totalValueChanges operations := by
  have balance := lifetime_balance history
  have zero : inventory initial (EpisodeLedger.empty : EpisodeLedger n) = 0 := by
    simp [inventory, EpisodeLedger.empty, upward]
  rw [zero, Nat.zero_add] at balance
  omega

#print axioms closed_upward_le_valueChanges

end Splay.Research.ActualLoserUpwardBudget
