import DynamicOptimality.SearchRotationModel

/-!
# Shared abstract online BST strategies

The state may contain arbitrary mathematical bookkeeping. Each request must
nevertheless transform its one actual tree by a finite rotation sequence,
paying the initial search depth plus one plus those rotations. Choices are
functions of the current state and request. No effectiveness or running-time
claim is part of this interface.

An initial state is supplied separately: this supports both canonical starts
and wrappers that accept an arbitrary initial indexed BST.
-/

namespace DynamicOptimality

structure OnlineBST (n : Nat) where
  State : Type
  tree : State → RawTree Nat
  tree_word : ∀ state, (tree state).inorder = List.range n
  advance : State → Fin n → State
  accessCost : State → Fin n → Nat
  legal : ∀ state request, SearchRotation.Access request.val (tree state)
    (tree (advance state request)) (accessCost state request)

namespace OnlineBST

variable {n : Nat} (strategy : OnlineBST n)

def run (state : strategy.State) : List (Fin n) → strategy.State × Nat
  | [] => (state, 0)
  | request :: requests =>
    let rest := run (strategy.advance state request) requests
    (rest.1, strategy.accessCost state request + rest.2)

theorem run_execution (state : strategy.State) (requests : List (Fin n)) :
    SearchRotation.Execution (strategy.tree state) (requests.map Fin.val)
      (strategy.tree (strategy.run state requests).1) (strategy.run state requests).2 := by
  induction requests generalizing state with
  | nil => exact .nil _
  | cons request requests ih => exact .cons (strategy.legal state request) (ih _)

theorem run_tree_word (state : strategy.State) (requests : List (Fin n)) :
    (strategy.tree (strategy.run state requests).1).inorder = List.range n :=
  strategy.tree_word _

/-- The strategy continues from exactly its chosen prefix state and cost. -/
theorem run_append (state : strategy.State) (first last : List (Fin n)) :
    strategy.run state (first ++ last) =
      let front := strategy.run state first
      let back := strategy.run front.1 last
      (back.1, front.2 + back.2) := by
  induction first generalizing state with
  | nil => simp [run]
  | cons request first ih => simp only [List.cons_append, run, ih, Nat.add_assoc]

end OnlineBST
end DynamicOptimality
