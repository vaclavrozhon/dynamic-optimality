import MultiSplay.ClassicalSwitchAccountingLinear
import MultiSplay.CommonForestCoefficientBound

/-!
# Interface coefficients for the exact classical switch history

The supplied actual trace retains its chronological event word. Initial
forest domains, capacity, global distinctness, join checks and the single
linear initialization allowance are discharged by the existing reference
lemmas. The exact-word comparator and its budget remain explicit.
-/

namespace MultiSplay.ClassicalSwitch.Accounting

open DynamicOptimality (RawTree BST)
open ChaCha.MTR.Tree (inorder size length_inorder)
open ChaCha.Primary (Key)
open EndpointEncoding CommonForest

/-- One uniform constant bounds the supplied actual splay execution. The
comparator has precisely the same chronological split/join word and initial
component domains; its shapes, final shapes, and paid preparations are free
to differ. The comparator budget is not asserted to be small here. -/
theorem history_splay_bound_of_coefficients :
    ∃ constant : Nat, 0 < constant ∧
      ∀ coefficients : Splay.Interface.ActivityCoefficients,
      Splay.Interface.CoefficientBound Splay.Accounting.articleShape coefficients →
      ∀ {lower upper : Nat} (reference : BST lower upper) (state : State) (addresses : List Key)
        {before after sources targets : List (RawTree Nat)} {cost budget : Nat},
        (∀ address ∈ addresses, referenceAt reference.toRaw address ≠ .empty) →
        domains before = domains (forest state reference.toRaw) →
        domains sources = domains (forest state reference.toRaw) →
        SplayTrace before (historyWord reference.toRaw state addresses) after cost →
        Program sources (historyWord reference.toRaw state addresses) targets budget →
        cost ≤ constant * (2 * reference.size + 1 + budget) *
          Splay.Analysis.coefficientFactor coefficients (Unlocated.normalizedValueCap reference.height) := by
  obtain ⟨constant,positive,bound⟩ := CommonForest.forest_splay_bound_of_coefficients
  refine ⟨constant,positive,?_⟩
  intro coefficients valid lower upper reference state addresses before after sources targets cost budget real actualKeys comparatorKeys actual comparator
  have unique : (inorder reference.toRaw).Nodup :=
    reference.toRaw_ordered.imp (fun less => ne_of_lt less)
  have distinct := history_distinct actual (unique_from_domains actualKeys unique)
  have paid := bound coefficients valid Nat reference.height comparator (capacity_from_domains reference comparatorKeys)
    (history_joinFits reference state addresses real) distinct (actualKeys.trans comparatorKeys.symm)
  rw [initialization_from_domains actualKeys, DynamicOptimality.BST.toRaw_size] at paid
  exact paid

/-- Specialization to arbitrary requests from the actual finite key universe.
Reference addresses are generated from the keys, so no address-validity
premise remains. Empty universes and empty request lists are included. -/
theorem finite_history_splay_bound_of_coefficients :
    ∃ constant : Nat, 0 < constant ∧
      ∀ coefficients : Splay.Interface.ActivityCoefficients,
      Splay.Interface.CoefficientBound Splay.Accounting.articleShape coefficients →
      ∀ {n : Nat} (reference : BST 0 n) (state : State) (requests : List (Fin n))
        {before after sources targets : List (RawTree Nat)} {cost budget : Nat},
        domains before = domains (forest state reference.toRaw) →
        domains sources = domains (forest state reference.toRaw) →
        SplayTrace before
          (historyWord reference.toRaw state (requests.map fun key => nodeAddress reference key.val)) after cost →
        Program sources
          (historyWord reference.toRaw state (requests.map fun key => nodeAddress reference key.val)) targets budget →
        cost ≤ constant * (2 * n + 1 + budget) * Splay.Analysis.coefficientFactor coefficients (Unlocated.normalizedValueCap reference.height) := by
  obtain ⟨constant,positive,bound⟩ := history_splay_bound_of_coefficients
  refine ⟨constant,positive,?_⟩
  intro coefficients valid n reference state requests before after sources targets cost budget actualKeys comparatorKeys actual comparator
  have real : ∀ address ∈ requests.map (fun key => nodeAddress reference key.val),
      referenceAt reference.toRaw address ≠ .empty := by
    intro address member
    obtain ⟨key,_,rfl⟩ := List.mem_map.mp member
    obtain ⟨left,right,found⟩ := referenceAt_nodeAddress reference (Nat.zero_le key.val) key.isLt
    simp [found]
  simpa only [Splay.Tree.BST.size_eq_upper] using
    bound coefficients valid reference state _ real actualKeys comparatorKeys actual comparator

/-- The harmless empty component of the canonical forest does not force an
additive constant at universe size zero: its request word is empty and costs
zero. For all other sizes the exact initialization volume is at most `3*n`. -/
theorem finite_history_splay_bound_linear_of_coefficients :
    ∃ constant : Nat, 0 < constant ∧
      ∀ coefficients : Splay.Interface.ActivityCoefficients,
      Splay.Interface.CoefficientBound Splay.Accounting.articleShape coefficients →
      ∀ {n : Nat} (reference : BST 0 n) (state : State) (requests : List (Fin n))
        {before after sources targets : List (RawTree Nat)} {cost budget : Nat},
        domains before = domains (forest state reference.toRaw) →
        domains sources = domains (forest state reference.toRaw) →
        SplayTrace before
          (historyWord reference.toRaw state (requests.map fun key => nodeAddress reference key.val)) after cost →
        Program sources
          (historyWord reference.toRaw state (requests.map fun key => nodeAddress reference key.val)) targets budget →
        cost ≤ constant * (n + budget) * Splay.Analysis.coefficientFactor coefficients (Unlocated.normalizedValueCap reference.height) := by
  obtain ⟨constant,positive,bound⟩ := finite_history_splay_bound_of_coefficients
  refine ⟨3*constant,Nat.mul_pos (by omega) positive,?_⟩
  intro coefficients valid n reference state requests before after sources targets cost budget actualKeys comparatorKeys actual comparator
  by_cases empty : n = 0
  · subst n
    cases requests with
    | nil =>
        have bare : SplayTrace before [] after cost := by simpa only [List.map_nil, historyWord] using actual
        have zeroCost : cost = 0 := by cases bare.toRun; rfl
        rw [zeroCost]
        exact Nat.zero_le _
    | cons key rest => exact Fin.elim0 key
  · have paid := bound coefficients valid reference state requests actualKeys comparatorKeys actual comparator
    have volume : 2*n+1+budget ≤ 3*(n+budget) := by omega
    calc
      cost ≤ constant * (2*n+1+budget) * Splay.Analysis.coefficientFactor coefficients (Unlocated.normalizedValueCap reference.height) := paid
      _ ≤ constant * (3*(n+budget)) * Splay.Analysis.coefficientFactor coefficients (Unlocated.normalizedValueCap reference.height) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ volume)
      _ = (3*constant) * (n+budget) * Splay.Analysis.coefficientFactor coefficients (Unlocated.normalizedValueCap reference.height) := by ring

end MultiSplay.ClassicalSwitch.Accounting
