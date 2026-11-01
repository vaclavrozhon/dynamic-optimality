import VirtualOriginalPassLift
import VirtualPrefixInsertion
import ActualHistoricalLabelInventory

/-! One literal original operation lifted to historical-rank labels. The
original ledger determines both endpoints. Original value changes emit
nothing; no structural operation or Insert is introduced. -/

namespace Splay.Research.HistoricalNumericStepLift
open Splay.Interface Splay.Interface.MatchingValid
open Splay.Research.VirtualNumericInsertion Splay.Research.VirtualPrefixInsertion
open Splay.Research.ActualHistoricalLabelInventory
open scoped BigOperators

def state {n : ℕ} (rankLabel : ℕ → ℕ) (physical : State n) (ledger : EpisodeLedger n) : State n :=
  ⟨physical.blocks, nominal rankLabel ledger⟩

theorem nominal_bounds {n R : ℕ} (rankLabel : ℕ → ℕ) (ledger : EpisodeLedger n)
    (positiveLabel : ∀ rank, 1 ≤ rankLabel rank) (boundedLabel : ∀ rank, rankLabel rank ≤ R)
    (element : Element n) : 1 ≤ nominal rankLabel ledger element ∧ nominal rankLabel ledger element ≤ R := by
  have one : 1 ≤ R := (positiveLabel 0).trans (boundedLabel 0)
  unfold nominal
  cases ledger element with
  | none => exact ⟨le_refl 1, one⟩
  | some start => exact ⟨positiveLabel _, boundedLabel _⟩

theorem state_valid {n R : ℕ} {oldParams params : Parameters} (rankLabel : ℕ → ℕ)
    (physical : State n) (ledger : EpisodeLedger n) (valid : physical.Valid oldParams)
    (sameShape : params.toShape = oldParams.toShape)
    (positiveLabel : ∀ rank, 1 ≤ rankLabel rank) (boundedLabel : ∀ rank, rankLabel rank ≤ R)
    (cap : R+1 ≤ params.valueBound) : (state rankLabel physical ledger).Valid params := by
  have growing := congrArg Shape.growingLimit sameShape
  refine ⟨valid.1, ?_, ?_⟩
  · intro element
    have bounds := nominal_bounds rankLabel ledger positiveLabel boundedLabel element
    exact ⟨bounds.1, bounds.2.trans (by omega)⟩
  · intro creator
    simpa only [state, State.growingCount, growing] using valid.2.2 creator

theorem nominal_update {n : ℕ} (rankLabel : ℕ → ℕ) (ledger : EpisodeLedger n)
    (element : Element n) (entry : Option (EpisodeStart n)) :
    nominal rankLabel (Function.update ledger element entry) =
      Function.update (nominal rankLabel ledger) element
        (match entry with | none => 1 | some start => rankLabel (historicalRank start)) := by
  funext queried
  by_cases same : queried = element
  · subst queried
    simp [nominal]
    rfl
  · simp [nominal, same]

noncomputable def preparation {n : ℕ} (rankLabel : ℕ → ℕ) (before : State n)
    (ledger : EpisodeLedger n) : Operation n → ℕ
  | .pass _ matching => (matching.map (VirtualLoserPreparation.deficit (state rankLabel before ledger))).sum
  | _ => 0

noncomputable def charge {n : ℕ} (rankLabel : ℕ → ℕ) (R : ℕ) (before : State n)
    (labels : RootLabels) (ledger : EpisodeLedger n) (operation : Operation n) : ℕ :=
  preparation rankLabel before ledger operation + positive rankLabel before labels ledger operation + R*operation.insertCount

private theorem state_eq {n : ℕ} {a b : State n} (blocks : a.blocks = b.blocks) (values : a.value = b.value) : a=b := by
  cases a; cases b; simp_all

/-- Upward cost, not signed/net variation, is bounded by the literal Pass
preparation/nominal-rise bill and at most R per original Insert. -/
theorem realize {n R : ℕ} {oldParams params : Parameters} (rankLabel : ℕ → ℕ)
    {before next : State n} {operation : Operation n}
    (original : Step oldParams before operation next) (labels : RootLabels) (ledger : EpisodeLedger n)
    (sameShape : params.toShape = oldParams.toShape)
    (positiveLabel : ∀ rank, 1 ≤ rankLabel rank) (boundedLabel : ∀ rank, rankLabel rank ≤ R)
    (cap : R+1 ≤ params.valueBound) :
    ∃ operations,
      Trace params (state rankLabel before ledger) operations
        (state rankLabel next (EpisodeLedger.after before labels ledger operation)) ∧
      totalActivity operations = operation.activity ∧ totalBlockGrowth operations = operation.blockGrowth ∧
      totalInserts operations = operation.insertCount ∧
      totalIncreases operations ≤ charge rankLabel R before labels ledger operation := by
  have beforeValid := state_valid rankLabel before ledger original.1 sameShape positiveLabel boundedLabel cap
  have afterValid := state_valid rankLabel next (EpisodeLedger.after before labels ledger operation)
    original.2.2 sameShape positiveLabel boundedLabel cap
  have growingCap := congrArg Shape.growingLimit sameShape
  cases original.2.1 with
  | @convert _ id source found growing blocks values =>
      have lifted : Step params (state rankLabel before ledger) (.convert id)
          (state rankLabel next (EpisodeLedger.after before labels ledger (.convert id))) :=
        ⟨beforeValid, .convert found growing blocks rfl, afterValid⟩
      exact ⟨[.convert id], .cons lifted (.nil afterValid),
        rfl, rfl, rfl, Nat.zero_le _⟩
  | @create _ creator room blocks values =>
      have room' : (state rankLabel before ledger).growingCount creator < params.growingLimit := by
        simpa only [state, State.growingCount, growingCap] using room
      have lifted : Step params (state rankLabel before ledger) (.create creator)
          (state rankLabel next (EpisodeLedger.after before labels ledger (.create creator))) :=
        ⟨beforeValid, .create room' blocks rfl, afterValid⟩
      exact ⟨[.create creator], .cons lifted (.nil afterValid),
        rfl, rfl, rfl, Nat.zero_le _⟩
  | @split _ id source cut found shrinking within blocks values =>
      have lifted : Step params (state rankLabel before ledger) (.split id cut)
          (state rankLabel next (EpisodeLedger.after before labels ledger (.split id cut))) :=
        ⟨beforeValid, .split found shrinking within blocks rfl, afterValid⟩
      exact ⟨[.split id cut], .cons lifted (.nil afterValid),
        rfl, rfl, rfl, Nat.zero_le _⟩
  | decrease can blocks values =>
      rename_i element
      have endpoint : state rankLabel next (EpisodeLedger.after before labels ledger (.valueChange element .decrease)) =
          state rankLabel before ledger := state_eq blocks rfl
      rw [endpoint]
      exact ⟨[], .nil beforeValid, rfl, rfl, rfl, Nat.zero_le _⟩
  | increase can blocks values =>
      rename_i element
      have endpoint : state rankLabel next (EpisodeLedger.after before labels ledger (.valueChange element .increase)) =
          state rankLabel before ledger := state_eq blocks rfl
      rw [endpoint]
      exact ⟨[], .nil beforeValid, rfl, rfl, rfl, Nat.zero_le _⟩
  | @delete _ id source element found shrinking present blocks values =>
      let deleted := state rankLabel next ledger
      have deletedValid := state_valid rankLabel next ledger original.2.2 sameShape positiveLabel boundedLabel cap
      have deletion : Step params (state rankLabel before ledger) (.delete id element) deleted :=
        ⟨beforeValid, .delete found shrinking present blocks rfl, deletedValid⟩
      let count := nominal rankLabel ledger element-1
      have oldPositive := (nominal_bounds rankLabel ledger positiveLabel boundedLabel element).1
      have lowered := decreases_trace deleted element count deletedValid (by change count+1 ≤ nominal rankLabel ledger element; dsimp [count]; omega)
      have endpoint : setValue deleted element (deleted.value element-count) =
          state rankLabel next (EpisodeLedger.after before labels ledger (.delete id element)) := by
        apply state_eq
        · rfl
        · change Function.update (nominal rankLabel ledger) element (nominal rankLabel ledger element-count) =
            nominal rankLabel (EpisodeLedger.after before labels ledger (.delete id element))
          rw [EpisodeLedger.after, nominal_update]
          congr 1
          dsimp [count]
          omega
      rw [endpoint] at lowered
      refine ⟨.delete id element :: List.replicate count (.valueChange element .decrease), .cons deletion lowered,
        ?_, ?_, ?_, ?_⟩ <;>
        simp [totalActivity, totalBlockGrowth, totalInserts, totalIncreases, Operation.activity,
          Operation.blockGrowth, Operation.insertCount, Operation.increaseCount, charge, preparation, positive]
  | @insert _ id source element found growing fresh order blocks values =>
      let target := nominal rankLabel (EpisodeLedger.after before labels ledger (.insert id element)) element
      have targetBounds := nominal_bounds rankLabel (EpisodeLedger.after before labels ledger (.insert id element))
        positiveLabel boundedLabel element
      have creatorBounds := nominal_bounds rankLabel ledger positiveLabel boundedLabel source.creator
      have oldBounds := nominal_bounds rankLabel ledger positiveLabel boundedLabel element
      have different : source.creator ≠ element := by intro equal; rw [equal] at order; omega
      have insertion := VirtualPrefixInsertion.realize (state rankLabel before ledger) id source element target
        beforeValid found growing fresh different targetBounds.1 (targetBounds.2.trans (by omega))
        (by change nominal rankLabel ledger source.creator+1 ≤ params.valueBound; omega)
      have endpoint : insertState (setValue (state rankLabel before ledger) element target) id element =
          state rankLabel next (EpisodeLedger.after before labels ledger (.insert id element)) := by
        apply state_eq blocks.symm
        change Function.update (nominal rankLabel ledger) element target =
          nominal rankLabel (EpisodeLedger.after before labels ledger (.insert id element))
        rw [EpisodeLedger.after, nominal_update]
        congr 1
        simp [target, EpisodeLedger.after, nominal]
      rw [endpoint] at insertion
      refine ⟨VirtualPrefixInsertion.events (state rankLabel before ledger) id source.creator element target,
        insertion, ?_, VirtualPrefixInsertion.growth_eq_zero _ _ _ _ _,
        VirtualPrefixInsertion.inserts_eq_one _ _ _ _ _, ?_⟩
      · simp [VirtualPrefixInsertion.events, totalActivity, Operation.activity]
      · rw [VirtualPrefixInsertion.increases_eq]
        have peakBound : peak (state rankLabel before ledger) source.creator element target ≤ R+1 := by
          unfold peak
          change max (max target (nominal rankLabel ledger source.creator+1))
            (nominal rankLabel ledger element) ≤ R+1
          apply max_le (max_le _ _) _ <;> omega
        simp only [charge, preparation, positive, Operation.insertCount, Nat.zero_add, Nat.mul_one]
        change peak (state rankLabel before ledger) source.creator element target-nominal rankLabel ledger element ≤ R
        omega
  | @pass _ id source matching found matchingValid blocks values =>
      let oldState := state rankLabel before ledger
      let target := nominal rankLabel (EpisodeLedger.after before labels ledger (.pass id matching))
      obtain ⟨actualSource, actualFound, trace, activity, growth, inserts, increases⟩ :=
        VirtualOriginalPassLift.realize id matching original sameShape (show oldState.blocks=before.blocks from rfl)
          beforeValid (by
            intro pair member
            have bound := (nominal_bounds rankLabel ledger positiveLabel boundedLabel pair.winner).2
            change nominal rankLabel ledger pair.winner+1 ≤ params.valueBound
            omega) target
          (fun element => (nominal_bounds rankLabel _ positiveLabel boundedLabel element).1)
          (fun element => (nominal_bounds rankLabel _ positiveLabel boundedLabel element).2.trans (by omega))
      refine ⟨_, trace, activity, growth, inserts, ?_⟩
      rw [increases]
      simp only [charge, preparation, Operation.insertCount, Nat.mul_zero, Nat.add_zero]
      apply Nat.add_le_add_left
      have boundedRise : ((List.finRange (2*n+1)).map fun element =>
          target element-(VirtualLoserPreparation.lifted oldState matching).value element).sum ≤
          ((List.finRange (2*n+1)).map fun element => target element-oldState.value element).sum := by
        apply List.sum_le_sum
        intro element member
        exact Nat.sub_le_sub_left (VirtualLoserPreparation.lifted_mono oldState matching element) (target element)
      apply boundedRise.trans_eq
      rw [← List.ofFn_eq_map, List.sum_ofFn]
      rfl

end Splay.Research.HistoricalNumericStepLift

#print axioms Splay.Research.HistoricalNumericStepLift.realize
