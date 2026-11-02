import MultiSplay.DenseForestInitial

/-!
# The splay bound for an independently supplied raw normalizer

The input is a bounded comparison trace, with actual rotations and the exact
search/split/join word. The initial splay trees may have arbitrary shapes.
Only their ordered key domains must agree with the comparison forest. Both
the coupled local program and the global accounting history are constructed.
-/

namespace MultiSplay.DenseForest

open DynamicOptimality (RawTree)
open ChaCha.MTR.Tree (inorder size)

variable {α : Type*}

theorem forest_splay_bound :
    ∃ constant : Nat, 0 < constant ∧ ∀ (α : Type*) [Inhabited α] (capacity : Nat)
      {before after actual : List (RawTree α)} {word : List (CommonForest.Event α)} {budget : Nat},
      Trace (Layered.Bounded.height capacity) 20 before word after budget →
      (∀ tree ∈ before, BoundedMacros.Geometry (Layered.Bounded.height capacity) 20 tree) →
      actual.map inorder = before.map inorder →
      ∃ final cost, CommonForest.SplayTrace actual word final cost ∧
        final.map inorder = after.map inorder ∧
        cost ≤ constant * (2 * (actual.map size).sum + actual.length + budget) *
          Splay.Analysis.targetFactor capacity := by
  obtain ⟨constant, positive, bound⟩ := Unlocated.forest_splay_bound
  refine ⟨2*constant, by omega, ?_⟩
  intro α _ capacity before after actual word budget trace geometry same
  obtain ⟨initial, sourceEq, actualEq⟩ := exists_components before actual same
  obtain ⟨last, finalEq, ⟨execution⟩⟩ := compile trace (normalized_cap capacity) initial sourceEq
  have heights : ∀ trees ∈ initial.map Component.trees,
      trees.comparison.height ≤ Layered.Bounded.height capacity := by
    intro trees member
    obtain ⟨component, present, rfl⟩ := List.mem_map.mp member
    exact (component.geometry (geometry component.source (sourceEq ▸ List.mem_map.mpr ⟨component, present, rfl⟩))).1
  have paid := execution.paid.trans (bound capacity execution.program heights)
  have sizes := forest_sizes initial
  rw [actualEq] at sizes
  have lengths : (initial.map Component.trees).length = actual.length := by
    rw [← actualEq]
    simp
  have comparison := execution.comparison
  have volume : 2 * ((initial.map Component.trees).map Unlocated.Trees.size).sum +
      (initial.map Component.trees).length + execution.program.comparisonCost ≤
      2 * (2 * (actual.map size).sum + actual.length + budget) := by
    rw [sizes, lengths]
    omega
  refine ⟨last.map Component.actual, execution.cost, ?_, ?_, ?_⟩
  · simpa only [actualEq] using execution.actual
  · simpa only [finalEq] using forest_domains last
  · calc
      execution.cost ≤ constant * (2 * ((initial.map Component.trees).map Unlocated.Trees.size).sum +
          (initial.map Component.trees).length + execution.program.comparisonCost) *
          Splay.Analysis.targetFactor capacity := paid
      _ ≤ constant * (2 * (2 * (actual.map size).sum + actual.length + budget)) *
          Splay.Analysis.targetFactor capacity :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ volume)
      _ = _ := by ring

end MultiSplay.DenseForest
