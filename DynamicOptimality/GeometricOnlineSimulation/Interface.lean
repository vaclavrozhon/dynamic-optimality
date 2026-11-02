import DynamicOptimality.GeometricOnlineSimulation.Graft

/-!
# The split-tree interface used by the causal geometry conversion

A state represents one class of keys with the same last-touch time.
A cut moves one selected key to the actual physical root and leaves two
valid states. Its ordinary rotations consume stored natural-number credit.
Setup creates at most `K` credits per key, for one fixed constant `K`.

This is an implementation interface, not a final simulation hypothesis:
the concrete split-tree implementation supplies its unconditional instance.
No operation receives a future request sequence.
-/

namespace DynamicOptimality.GeometricOnlineSimulation

open ChaCha.MTR

structure SplitResult (State : Type) (tree : State → RawTree Nat) (credit : State → Nat)
    (state : State) (key : Nat) where
  left : State
  right : State
  count : Nat
  rotations : SearchRotation.Rotations (tree state) (.node (tree left) key (tree right)) count
  credit_bound : count + credit left + credit right ≤ credit state

structure SplitTreeSystem where
  State : Type
  tree : State → RawTree Nat
  credit : State → Nat
  K : Nat
  setup : List Nat → State
  setup_keys : ∀ keys, (tree (setup keys)).inorder = keys
  setup_credit : ∀ keys, credit (setup keys) ≤ K * keys.length
  cut : ∀ state key, key ∈ (tree state).inorder → SplitResult State tree credit state key

namespace SplitTreeSystem

variable (system : SplitTreeSystem)

theorem cut_keys (state : system.State) (key : Nat) (member : key ∈ (system.tree state).inorder) :
    (system.tree state).inorder =
      (system.tree (system.cut state key member).left).inorder ++ [key] ++
        (system.tree (system.cut state key member).right).inorder := by
  have trace := (system.cut state key member).rotations
  have preserved {before after : RawTree Nat} {count : Nat}
      (run : SearchRotation.Rotations before after count) : before.inorder = after.inorder := by
    induction run with
    | refl => rfl
    | step first rest ih => exact (rotation_inorder first).trans ih
  exact preserved trace

theorem setup_size (keys : List Nat) : (system.tree (system.setup keys)).size = keys.length := by
  simpa only [Tree.length_inorder] using congrArg List.length (system.setup_keys keys)

theorem cut_sizes (state : system.State) (key : Nat) (member : key ∈ (system.tree state).inorder) :
    (system.tree (system.cut state key member).left).size +
        (system.tree (system.cut state key member).right).size + 1 = (system.tree state).size := by
  have equal := congrArg List.length (system.cut_keys state key member)
  simp only [List.length_append,List.length_singleton,Tree.length_inorder] at equal
  omega

end SplitTreeSystem
end DynamicOptimality.GeometricOnlineSimulation
