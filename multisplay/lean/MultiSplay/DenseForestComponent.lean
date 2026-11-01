import MultiSplay.PairedRootDecomposition
import MultiSplay.ForestRealization

/-! # Coupling sparse physical trees through common local ordinal coordinates -/

namespace MultiSplay.DenseForest

open DynamicOptimality (RawTree)
open Splay.Accounting
open Splay.Tree (BST)
open TangoSquared.MTR.Tree (inorder)

variable {α : Type*}

structure Component (α : Type*) where
  trees : Unlocated.Trees
  alphabet : Nat → α

def Component.source (component : Component α) : RawTree α :=
  Auxiliary.map component.alphabet (DynamicOptimality.BST.toRaw component.trees.comparison)

def Component.actual (component : Component α) : RawTree α :=
  Auxiliary.map component.alphabet (DynamicOptimality.BST.toRaw component.trees.splay)

theorem Component.inorder_eq (component : Component α) : inorder component.actual = inorder component.source :=
  Alphabet.indexed_inorder_eq _ _ _

theorem Component.geometry {height slack : Nat} (component : Component α)
    (geometry : BoundedMacros.Geometry height slack component.source) :
    component.trees.comparison.height ≤ height ∧ OfflineNormalForm.HasBoundedMinorRibs component.trees.comparison slack := by
  obtain ⟨lower, upper, indexed, alphabet, same, bounded, ribs⟩ := geometry
  obtain ⟨heightEq, _, _, ribEq⟩ := Alphabet.geometry_of_map_eq indexed component.trees.comparison alphabet component.alphabet same
  exact ⟨heightEq ▸ bounded, (ribEq slack).mp ribs⟩

theorem exists_component [Inhabited α] (comparison splay : RawTree α) (same : inorder splay = inorder comparison) :
    ∃ component : Component α, component.source = comparison ∧ component.actual = splay := by
  obtain ⟨n, indexed, alphabet, sourceEq, _⟩ := Alphabet.exists_encoding comparison
  obtain ⟨actual, actualEq⟩ := Alphabet.exists_on_same_alphabet indexed alphabet splay (sourceEq ▸ same)
  exact ⟨⟨⟨n, indexed, actual⟩, alphabet⟩, sourceEq, actualEq⟩

def CommonRoot (trees : Unlocated.Trees) : Prop :=
  ∃ key : Nat, trees.comparison.HasRoot key ∧ trees.splay.HasRoot key

theorem request {height slack : Nat} (component : Component α) {left right : RawTree α} {key : α}
    (root : component.source = .node left key right)
    (geometry : BoundedMacros.Geometry height slack component.source) :
    ∃ result : Component α, ∃ rotations : Nat,
      result.source = component.source ∧ Auxiliary.Splay key component.actual result.actual rotations ∧
      CommonRoot result.trees ∧
      ∃ program : Unlocated.Program (articleParameters height) slack 1 [component.trees] [result.trees],
        program.splayCost = rotations+1 ∧ program.requests = 1 ∧ program.rotations = 0 ∧
        program.boundaries = 0 ∧ program.comparisonCost = 1 := by
  obtain ⟨bounded, ribs⟩ := component.geometry geometry
  rcases component with ⟨⟨n, comparison, splay⟩, alphabet⟩
  cases comparison with
  | empty => simp [Component.source, DynamicOptimality.BST.toRaw, Auxiliary.map] at root
  | @node lower pivot upper cl cr =>
      have inside : pivot < n := by have bound := cr.lower_le_upper; omega
      obtain ⟨after, execution⟩ := Splay.Tree.BST.SplayExecution.exists_splay splay (Nat.zero_le _) inside
      have atRoot : (BST.node cl cr).HasRoot pivot := ⟨cl, cr, rfl⟩
      let result : Component α := ⟨⟨_, .node cl cr, after⟩, alphabet⟩
      have actual := (Auxiliary.Splay.of_indexed execution).map alphabet
      have keyEq : alphabet pivot = key := by
        simpa only [Component.source, DynamicOptimality.BST.toRaw, Auxiliary.map,
          TangoSquared.MTR.Tree.node.injEq] using (show alphabet pivot = key from (TangoSquared.MTR.Tree.node.inj root).2.1)
      refine ⟨result, splay.depth pivot, rfl, ?_, ⟨pivot, atRoot, execution.hasRoot_after⟩,
        .next (Unlocated.boundedRequest height slack 1 (.node cl cr) splay after ⟨pivot, inside⟩ [] atRoot execution bounded ribs) (.done _),
        rfl, rfl, rfl, rfl, rfl⟩
      simpa only [keyEq, Component.actual, result] using actual

end MultiSplay.DenseForest
