import DynamicOptimality.GeometricOnlineSimulation.ComponentCut
import DynamicOptimality.GeometricOnlineSimulation.Interface

/-!
# The concrete split-tree system

This unconditional instance uses exactly the original inorder keys. Setup
stores at most 184 credits per key. Every destructive cut has a finite
ordinary rotation sequence and consumes those credits. All choices are
fixed from the current state and requested key, without future requests.
-/

namespace DynamicOptimality.GeometricOnlineSimulation

open ChaCha.MTR

noncomputable def initialComponent (keys : List Nat) : Component :=
  Classical.choose (Component.exists_initial keys)

theorem initialComponent_keys (keys : List Nat) : (initialComponent keys).tree.inorder = keys :=
  (Classical.choose_spec (Component.exists_initial keys)).1

theorem initialComponent_credit (keys : List Nat) : (initialComponent keys).credit ≤ 184 * keys.length :=
  (Classical.choose_spec (Component.exists_initial keys)).2

noncomputable def componentSplit (component : Component) (key : Nat)
    (member : key ∈ component.tree.inorder) :
    SplitResult Component Component.tree Component.credit component key :=
  Classical.choice (by
    obtain ⟨left, right, count, rotations, bound⟩ := component.cut_exists key member
    exact ⟨⟨left, right, count, rotations, bound⟩⟩)

/-- The fully implemented system consumed by the causal geometry proof. -/
noncomputable def dyadicSplitTrees : SplitTreeSystem where
  State := Component
  tree := Component.tree
  credit := Component.credit
  K := 184
  setup := initialComponent
  setup_keys := initialComponent_keys
  setup_credit := initialComponent_credit
  cut := componentSplit

/-- The one-time setup can start at any supplied ordinary BST; actual
rotations plus all stored future split credit cost at most 190 per key. -/
theorem initialComponent_rotations (tree : RawTree Nat) :
    ∃ count, SearchRotation.Rotations tree (initialComponent tree.inorder).tree count ∧
      count + (initialComponent tree.inorder).credit ≤ 190 * tree.size := by
  have same := initialComponent_keys tree.inorder
  obtain ⟨count, bound, run⟩ := Tree.restricted_rotation_linear
    tree (initialComponent tree.inorder).tree same.symm
  have size : (initialComponent tree.inorder).tree.size = tree.size := by
    simpa only [Tree.length_inorder] using congrArg List.length same
  have stored := initialComponent_credit tree.inorder
  rw [Tree.length_inorder] at stored
  refine ⟨count, OnlineModel.restrictedSteps_to_rotations run, ?_⟩
  omega

end DynamicOptimality.GeometricOnlineSimulation
