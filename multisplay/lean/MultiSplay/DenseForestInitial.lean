import MultiSplay.DenseForestCompiler

/-! # Initializing coupled components from physical forests -/

namespace MultiSplay.DenseForest

open DynamicOptimality (RawTree)
open TangoSquared.MTR.Tree (inorder size)

variable {α : Type*}

theorem Component.source_size (component : Component α) : size component.source = component.trees.size := by
  simp only [Component.source, Alphabet.map_size, DynamicOptimality.BST.toRaw_size,
    Splay.Tree.BST.size_eq_upper]

theorem Component.actual_size (component : Component α) : size component.actual = component.trees.size := by
  simp only [Component.actual, Alphabet.map_size, DynamicOptimality.BST.toRaw_size,
    Splay.Tree.BST.size_eq_upper]

theorem exists_components [Inhabited α] (comparison actual : List (RawTree α))
    (same : actual.map inorder = comparison.map inorder) :
    ∃ components : List (Component α), components.map Component.source = comparison ∧
      components.map Component.actual = actual := by
  induction comparison generalizing actual with
  | nil =>
      have empty : actual = [] := List.map_eq_nil_iff.mp same
      subst actual
      exact ⟨[], rfl, rfl⟩
  | cons source sources ih =>
      cases actual with
      | nil => simp at same
      | cons tree trees =>
          obtain ⟨head, tail⟩ := List.cons.inj same
          obtain ⟨component, sourceEq, actualEq⟩ := exists_component source tree head
          obtain ⟨components, sourcesEq, actualsEq⟩ := ih trees tail
          exact ⟨component::components, by simp [sourceEq, sourcesEq], by simp [actualEq, actualsEq]⟩

theorem forest_sizes (components : List (Component α)) :
    ((components.map Component.trees).map Unlocated.Trees.size).sum =
      ((components.map Component.actual).map size).sum := by
  simp only [List.map_map, Function.comp_def, Component.actual_size]

theorem forest_domains (components : List (Component α)) :
    (components.map Component.actual).map inorder = (components.map Component.source).map inorder := by
  simp only [List.map_map, Function.comp_def, Component.inorder_eq]

theorem normalized_cap (capacity : Nat) :
    3 ≤ (Splay.Accounting.articleParameters (Layered.Bounded.height capacity)).valueBound := by
  change 3 ≤ Splay.Analysis.contractedGap (2 * Layered.Bounded.height capacity + 1)
  exact (by decide : 3 ≤ Splay.Analysis.contractedGap 3).trans
    (Splay.Analysis.contractedGap_mono (by dsimp [Layered.Bounded.height]; omega))

end MultiSplay.DenseForest
