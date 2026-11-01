import DynamicOptimality.ModelCostEquivalence
import DynamicOptimality.ModelOnline

/-!
# A prescribed initial tree in the equivalent BST models

Changing the initial tree uses at most `6*n` ordinary rotations. This
charge is paid once, before the first root service; the search-and-rotation
conversion still charges the search depth in the supplied initial tree.
The empty request sequence performs no initialization.
-/

namespace DynamicOptimality.ModelInitialization

open TangoSquared.MTR

theorem toRaw_injective {lower upper : Nat} {a b : BST lower upper}
    (same : a.toRaw = b.toRaw) : a = b := by
  induction a with
  | empty =>
    cases b with
    | empty => rfl
    | node => cases same
  | node left right ihLeft ihRight =>
    cases b with
    | empty => cases same
    | node otherLeft otherRight =>
      simp only [BST.toRaw, Tree.node.injEq] at same
      obtain ⟨leftEq, rootEq, rightEq⟩ := same
      cases rootEq
      have hleft := ihLeft leftEq
      have hright := ihRight rightEq
      cases hleft
      cases hright
      rfl

theorem rotations_between {n : Nat} (before after : BST 0 n) :
    ∃ count, Splay.Tree.BST.RotationExecution count before after ∧ count ≤ 6*n := by
  have same := (OnlineModel.indexed_inorder before).trans (OnlineModel.indexed_inorder after).symm
  obtain ⟨count, bound, steps⟩ := Tree.restricted_rotation_linear before.toRaw after.toRaw same
  obtain ⟨target, rotations, targetEq⟩ :=
    SearchRotation.rotations_lift (OnlineModel.restrictedSteps_to_rotations steps) before rfl
  have equal : target = after := toRaw_injective targetEq
  subst target
  refine ⟨count, rotations, ?_⟩
  simp only [BST.toRaw_size, Splay.Tree.BST.size_eq_upper] at bound
  omega

/-- Root service from any supplied initial tree, with one linear startup charge. -/
theorem root_from_initial {n : Nat} (initial : BST 0 n) (requests : List (Fin n)) :
    ∃ (final : BST 0 n) (rotations : Nat),
      OfflineExecution requests initial final rotations ∧
        requests.length + rotations ≤ OPT requests + 6*n := by
  by_cases empty : requests = []
  · subst requests
    exact ⟨initial, 0, .done _, by simp⟩
  · obtain ⟨start, final, count, execution, optimal⟩ := OPT_attained requests
    obtain ⟨setup, initialization, setupBound⟩ := rotations_between initial start
    exact ⟨final, setup + count,
      Splay.Accounting.OfflineOptimum.Execution.prependRotations empty initialization execution,
      by omega⟩

/-- In the user's model the first search is in `initial`, before any rotations. -/
theorem search_from_initial {n : Nat} (initial : BST 0 n) (requests : List (Fin n)) :
    ∃ (final : BST 0 n) (cost : Nat),
      SearchRotation.Execution initial.toRaw (requests.map Fin.val) final.toRaw cost ∧
        cost ≤ 2 * OPT requests + 12*n := by
  obtain ⟨final, rotations, execution, bound⟩ := root_from_initial initial requests
  obtain ⟨cost, search, searchBound⟩ := SearchRotation.ofOffline execution
  exact ⟨final, cost, search, by omega⟩

theorem hull_from_initial {n : Nat} (initial : BST 0 n) (requests : List (Fin n)) :
    ∃ (final : BST 0 n) (cost : Nat),
      AccessExecution initial.toRaw (requests.map Fin.val) final.toRaw cost ∧
        cost ≤ OPT requests + 6*n := by
  obtain ⟨final, rotations, execution, bound⟩ := root_from_initial initial requests
  obtain ⟨last, cost, hull, hullBound⟩ := ModelCosts.hull_of_offline execution
  exact ⟨last, cost, hull, by omega⟩

theorem pointer_from_initial {n : Nat} (initial : BST 0 n) (requests : List (Fin n)) :
    ∃ (final : BST 0 n) (cost : Nat),
      PointerExecution initial.toRaw (requests.map Fin.val) final.toRaw cost ∧
        cost ≤ 37 * OPT requests + 222*n := by
  obtain ⟨final, cost, hull, bound⟩ := hull_from_initial initial requests
  obtain ⟨pointerCost, pointer, pointerBound⟩ := accessExecution_pointer hull initial.toRaw_ordered
  exact ⟨final, pointerCost, pointer, by omega⟩

end DynamicOptimality.ModelInitialization
