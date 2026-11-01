import MultiSplay.ClassicalSwitchAccounting

/-! # One linear initialization term, including the empty universe -/

namespace MultiSplay.ClassicalSwitch.Accounting

open DynamicOptimality (RawTree BST)
open EndpointEncoding CommonForest

/-- The harmless empty component of the canonical forest does not force an
additive constant at universe size zero: its request word is empty and costs
zero. For all other sizes the exact initialization volume is at most `3*n`. -/
theorem finite_history_splay_bound_linear :
    ∃ constant : Nat, 0 < constant ∧
      ∀ {n : Nat} (reference : BST 0 n) (state : State) (requests : List (Fin n))
        {before after sources targets : List (RawTree Nat)} {cost budget : Nat},
        domains before = domains (forest state reference.toRaw) →
        domains sources = domains (forest state reference.toRaw) →
        SplayTrace before
          (historyWord reference.toRaw state (requests.map fun key => nodeAddress reference key.val)) after cost →
        Program sources
          (historyWord reference.toRaw state (requests.map fun key => nodeAddress reference key.val)) targets budget →
        cost ≤ constant * (n + budget) * Splay.Analysis.targetFactor reference.height := by
  obtain ⟨constant,positive,bound⟩ := finite_history_splay_bound
  refine ⟨3*constant,Nat.mul_pos (by omega) positive,?_⟩
  intro n reference state requests before after sources targets cost budget actualKeys comparatorKeys actual comparator
  by_cases empty : n = 0
  · subst n
    cases requests with
    | nil =>
        have bare : SplayTrace before [] after cost := by simpa only [List.map_nil, historyWord] using actual
        have zeroCost : cost = 0 := by cases bare.toRun; rfl
        rw [zeroCost]
        exact Nat.zero_le _
    | cons key rest => exact Fin.elim0 key
  · have paid := bound reference state requests actualKeys comparatorKeys actual comparator
    have volume : 2*n+1+budget ≤ 3*(n+budget) := by omega
    calc
      cost ≤ constant * (2*n+1+budget) * Splay.Analysis.targetFactor reference.height := paid
      _ ≤ constant * (3*(n+budget)) * Splay.Analysis.targetFactor reference.height :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ volume)
      _ = (3*constant) * (n+budget) * Splay.Analysis.targetFactor reference.height := by ring

end MultiSplay.ClassicalSwitch.Accounting
