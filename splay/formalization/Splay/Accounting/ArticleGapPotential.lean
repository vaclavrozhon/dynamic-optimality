import Splay.Accounting.ArticlePairingLoserRestoration
import Splay.Interface.Potential

namespace Splay.Accounting

open Splay.Lazy

theorem increaseEach_value_congr {n : ℕ} {first second : Lazy.State n}
    (equal : first.value = second.value) (elements : List (Interface.Element n)) :
    (increaseEach first elements).value = (increaseEach second elements).value := by
  induction elements generalizing first second with
  | nil => exact equal
  | cons element elements ih =>
      apply ih
      simp only [State.increaseValue, equal]

/-- A pass preserves values, so restoring its prepared winners recovers the
complete original function before any loser gaps are normalized. -/
theorem articlePassRestoredValue {n : ℕ} (state : Lazy.State n)
    (winners : List (Interface.Element n)) (distinct : winners.Nodup)
    (positive : ∀ element ∈ winners, 1 ≤ state.value element)
    (view : HeapView n) (sourceId : Interface.BlockId) (source : Lazy.Block n)
    (matching : List (Interface.Pairing n)) (intervalGap : ℤ) :
    (increaseEach ((decreaseEach state winners).passAtView view sourceId source matching intervalGap)
      winners).value = state.value :=
  (increaseEach_value_congr
    (first := (decreaseEach state winners).passAtView view sourceId source matching intervalGap)
    (second := decreaseEach state winners) rfl winners).trans
    (increaseEach_decreaseEach_value state winners distinct positive)

/-- A geometric value, independent of temporary interface winner values.
The root contributes one; live elements use their actual interval gap. -/
noncomputable def geometricGapValue {n : ℕ} (state : Lazy.State n)
    (element : Interface.Element n) : ℕ := by
  classical
  exact if member : ∃ block ∈ state.blocks, element ∈ block.elements then
    Analysis.transientContractedGap (state.view.rawGap element)
      (Classical.choose member).intervalGap
  else 1

/-- Gap potential is evaluated at represented, stable macro checkpoints. -/
noncomputable def geometricGapPotential {n : ℕ} (state : Lazy.State n) : ℕ :=
  ∑ element : Interface.Element n, geometricGapValue state element

theorem geometricGapValue_eq {n : ℕ} {state : Lazy.State n}
    (complete : state.Complete) (values : state.ValuesRealizeGaps)
    (element : Interface.Element n) : geometricGapValue state element = state.value element := by
  classical
  unfold geometricGapValue
  split
  next member =>
    exact (values.2 _ (Classical.choose_spec member).1 _
      (Classical.choose_spec member).2).symm
  next absent =>
    have root : element = state.view.root := state.view.parent_eq_none element (by
      by_contra nonroot
      exact absent (State.mem_allElements_iff.mp ((complete element).mpr nonroot)))
    simpa only [root] using values.1.symm

theorem geometricGapPotential_eq {n : ℕ} {state : Lazy.State n}
    (complete : state.Complete) (values : state.ValuesRealizeGaps) :
    geometricGapPotential state = state.toInterface.totalValue := by
  unfold geometricGapPotential Interface.State.totalValue
  exact Finset.sum_congr rfl (fun element _ => geometricGapValue_eq complete values element)

theorem geometricGapPotential_le {n : ℕ} {state : Lazy.State n}
    {params : Interface.Parameters} (stable : state.Stable params) :
    geometricGapPotential state ≤ (2 * n + 1) * params.valueBound := by
  rw [geometricGapPotential_eq stable.2.1 stable.2.2.2.2.2]
  exact Interface.State.totalValue_le stable.valid.toInterface

/-- Free setup and split macros cannot raise the geometric potential when
their stable endpoints are joined by a trace with no increases. -/
theorem geometricGapPotential_le_of_no_increases
    {n : ℕ} {params : Interface.Parameters} {before after : Lazy.State n}
    {events : List (Event n)} (beforeStable : before.Stable params)
    (afterStable : after.Stable params) (trace : Trace params before events after)
    (noIncreases : Interface.totalIncreases (eraseOperations events) = 0) :
    geometricGapPotential after ≤ geometricGapPotential before := by
  rw [geometricGapPotential_eq beforeStable.2.1 beforeStable.2.2.2.2.2,
    geometricGapPotential_eq afterStable.2.1 afterStable.2.2.2.2.2]
  have balance := trace.toInterface.totalValue_balance
  rw [noIncreases] at balance
  omega

/-- Exact value-sum balance for normalizing one element. -/
theorem adjustValue_totalValue {n : ℕ} (state : Lazy.State n)
    (element : Interface.Element n) (target : ℕ) (positive : 1 ≤ target) :
    (state.adjustValue element target).toInterface.totalValue + state.value element =
      state.toInterface.totalValue + target := by
  have changed : (state.adjustValue element target).value =
      Function.update state.value element target := by
    funext other
    by_cases equal : other = element
    · subst other
      simp [State.adjustValue_value_self state element target positive]
    · simp [equal]
  simpa only [Interface.State.totalValue, State.toInterface, changed] using
    state.toInterface.totalValue_update element target

/-- Distinct restored losers pay any nonnegative credits covered by their
actual contracted-gap drops. Credits are frozen before winner preparation. -/
theorem restoreArticlePairingLosers_totalValue
    {n : ℕ} (view : HeapView n) (state : Lazy.State n)
    (matching : List (Interface.Pairing n)) (credit : Interface.Pairing n → ℕ)
    (distinct : (Interface.pairingLosers matching).Nodup)
    (drops : ∀ pairing ∈ matching,
      articlePairingLoserTarget view pairing + credit pairing ≤ state.value pairing.loser) :
    (restoreArticlePairingLosers view state matching).toInterface.totalValue +
        (matching.map credit).sum ≤ state.toInterface.totalValue := by
  induction matching generalizing state with
  | nil => simp [restoreArticlePairingLosers]
  | cons pairing matching ih =>
      have parts : pairing.loser ∉ Interface.pairingLosers matching ∧
          (Interface.pairingLosers matching).Nodup := by
        simpa [Interface.pairingLosers] using distinct
      have headDrop := drops pairing (by simp)
      have balance := adjustValue_totalValue state pairing.loser
        (articlePairingLoserTarget view pairing) (by
          simp [articlePairingLoserTarget, Analysis.contractedGap])
      have rest := ih (state.adjustValue pairing.loser (articlePairingLoserTarget view pairing))
        parts.2 (by
          intro later member
          have different : later.loser ≠ pairing.loser := by
            intro equal
            exact parts.1 (List.mem_map.mpr ⟨later, member, equal⟩)
          rw [State.adjustValue_value_of_ne state different]
          exact drops later (by simp [member]))
      simp only [restoreArticlePairingLosers, List.map_cons, List.sum_cons]
      omega

theorem articleGoodPairings_length_eq_sum {n : ℕ} (state : Lazy.State n)
    (matching : List (Interface.Pairing n)) :
    (articleGoodPairings state matching).length =
      (matching.map fun pairing =>
        if state.value pairing.winner = state.value pairing.loser then 1 else 0).sum := by
  induction matching with
  | nil => rfl
  | cons pairing matching ih =>
      by_cases equal : state.value pairing.winner = state.value pairing.loser
      <;> simp_all [articleGoodPairings, Nat.add_comm]

/-- The restored geometric loss pays every good pairing of a batch, with no
extra charge for the temporary decrease/increase of its winner. -/
theorem restoreArticlePairingLosers_pays_good
    {n : ℕ} (view : HeapView n) (state base : Lazy.State n)
    (matching : List (Interface.Pairing n))
    (valueEq : base.value = state.value)
    (distinct : (Interface.pairingLosers matching).Nodup)
    (drops : ∀ pairing ∈ matching,
      articlePairingLoserTarget view pairing ≤ state.value pairing.loser ∧
      (state.value pairing.winner = state.value pairing.loser →
        articlePairingLoserTarget view pairing + 1 ≤ state.value pairing.loser)) :
    (restoreArticlePairingLosers view base matching).toInterface.totalValue +
        (articleGoodWinners state matching).length ≤ state.toInterface.totalValue := by
  have bound := restoreArticlePairingLosers_totalValue view base matching
    (fun pairing => if state.value pairing.winner = state.value pairing.loser then 1 else 0)
    distinct (by
      intro pairing member
      rw [valueEq]
      split
      next equal => exact (drops pairing member).2 equal
      next => simpa using (drops pairing member).1)
  simpa only [articleGoodWinners, List.length_map, articleGoodPairings_length_eq_sum,
    Interface.State.totalValue, State.toInterface, valueEq] using bound

end Splay.Accounting
