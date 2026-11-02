import MultiSplay.PackedPhysicalTrace
import MultiSplay.PackedBoundedPreparation

/-!
# Physical common-forest splay comparison

The two projections of `Program` are actual executions of the existing
`CommonForest` model, with identical search/split/join words. Its splay
projection has exactly `splayCost + boundaries` cost. Its comparator charges
each rotation at depth d by d+1 and each search or structural event by one.
The initial allowance counts physical keys and component handles, including
empty components. No part of this comparison uses a Cha-Cha upper bound.
-/

namespace MultiSplay.PackedSplay

open Splay.Accounting
open ChaCha.MTR.Tree (size)

variable {m : Nat}

theorem physical_size (trees : Trees m) : size trees.physical = trees.size := by
  simp only [Trees.physical, physical, Alphabet.map_size, DynamicOptimality.BST.toRaw_size, Splay.Tree.BST.size_eq_upper]

theorem mass_physical (forest : List (Trees m)) :
    Trees.mass forest = 2 * (forest.map (fun trees => size trees.physical)).sum + forest.length := by
  induction forest with
  | nil => rfl
  | cons head tail ih =>
      simp only [Trees.mass, List.map_cons, List.sum_cons, List.length_cons, physical_size] at ih ⊢
      omega

/-- The constant is independent of capacity, the initial auxiliary shapes,
the number of components, the global universe, and the entire program. -/
theorem physical_forest_splay_bound (slack depth : Nat) :
    ∃ constant : Nat, 0 < constant ∧ ∀ (capacity : Nat) {m : Nat} {before after : List (Trees m)}
      (program : Program (articleParameters (Layered.Bounded.height capacity)) slack depth before after),
      before.Pairwise Trees.Disjoint →
      (∀ trees ∈ before, trees.comparison.height ≤ Layered.Bounded.height capacity) →
      program.splayCost + program.boundaries ≤
        constant * (2 * (before.map (fun trees => size trees.physical)).sum + before.length + program.comparisonCost) *
          Splay.Analysis.targetFactor capacity := by
  obtain ⟨constant, positive, bound⟩ := normalized_splay_bound slack depth
  refine ⟨constant, positive, ?_⟩
  intro capacity m before after program separate bounded
  have volume : program.volume ≤ Trees.mass before + program.comparisonCost := by
    have work := program.volume_le_comparisonCost
    unfold Program.volume
    omega
  rw [mass_physical] at volume
  exact (bound capacity program separate bounded).trans
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left constant volume))

end MultiSplay.PackedSplay
