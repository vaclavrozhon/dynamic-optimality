import ChaCha.Paper20261030.OnlineSearchRotation
import ChaCha.Paper20261030.OnlineSearchRotationInitializationCore

set_option autoImplicit false

/-!
The fixed online strategy from an arbitrary supplied initial BST. The
state is either fresh, containing that tree, or active, containing the
canonical maintained state. The first request alone includes a fixed
initialization. An empty word has zero cost and leaves the supplied tree
unchanged. The initial search precedes all initialization rotations.

Classical choice is used only to fix each transition from its current
state and current request, as permitted by the abstract model. No future
request word is an input to that choice.
-/

namespace ChaCha.Paper20261030.OnlineSearchRotationInitialization

open DynamicOptimality
open OnlineSearchRotation (keyCount factor)

theorem indexed_tree_inorder {n : Nat} (tree : BST 0 n) :
    tree.toRaw.inorder = List.range n := by
  apply List.Pairwise.eq_of_mem_iff tree.toRaw_ordered List.pairwise_lt_range
  intro key
  rw [BST.toRaw_mem,List.mem_range]
  omega

noncomputable def initialRotations {h : Nat} (tree : BST 0 (keyCount h)) :
    Initialization tree.toRaw (OnlineSearchRotation.initial h).tree :=
  initialization tree.toRaw (OnlineSearchRotation.initial h).tree
    ((indexed_tree_inorder tree).trans (OnlineSearchRotation.initial h).tree_inorder.symm)

structure FirstTransition {h : Nat} (tree : BST 0 (keyCount h)) (request : Fin (keyCount h)) where
  cost : Nat
  execution : SearchRotation.Access request.val tree.toRaw
    (OnlineSearchRotation.next (OnlineSearchRotation.initial h) request).tree cost
  bound : cost ≤ 19 * keyCount h + (OnlineSearchRotation.step (OnlineSearchRotation.initial h) request).cost

theorem first_transition_exists {h : Nat} (tree : BST 0 (keyCount h)) (request : Fin (keyCount h)) :
    Nonempty (FirstTransition tree request) := by
  obtain ⟨cost, execution, bound⟩ := prepend_initialization tree request (initialRotations tree)
    (OnlineSearchRotation.step (OnlineSearchRotation.initial h) request).execution
  exact ⟨⟨cost, execution, bound⟩⟩

noncomputable def firstStep {h : Nat} (tree : BST 0 (keyCount h)) (request : Fin (keyCount h)) :
    FirstTransition tree request := Classical.choice (first_transition_exists tree request)

/-- The fresh constructor is left permanently on the first request. -/
inductive State (h : Nat) where
  | fresh (tree : BST 0 (keyCount h))
  | active (state : OnlineSearchRotation.State h)

def State.tree {h : Nat} : State h → RawTree Nat
  | .fresh tree => tree.toRaw
  | .active state => state.tree

theorem State.tree_inorder {h : Nat} (state : State h) :
    state.tree.inorder = List.range (keyCount h) := by
  cases state with
  | fresh tree => exact indexed_tree_inorder tree
  | active state => exact state.tree_inorder

theorem State.tree_ordered {h : Nat} (state : State h) : MTR.Tree.Ordered state.tree := by
  unfold MTR.Tree.Ordered
  rw [state.tree_inorder]
  exact List.pairwise_lt_range

noncomputable def next {h : Nat} : State h → Fin (keyCount h) → State h
  | .fresh _, request => .active (OnlineSearchRotation.next (OnlineSearchRotation.initial h) request)
  | .active state, request => .active (OnlineSearchRotation.next state request)

structure Transition {h : Nat} (state : State h) (request : Fin (keyCount h)) where
  cost : Nat
  execution : SearchRotation.Access request.val state.tree (next state request).tree cost

/-- This is one fixed access for each current state and requested key. -/
noncomputable def step {h : Nat} (state : State h) (request : Fin (keyCount h)) : Transition state request :=
  match state with
  | .fresh tree => ⟨(firstStep tree request).cost, (firstStep tree request).execution⟩
  | .active state => ⟨(OnlineSearchRotation.step state request).cost,
      (OnlineSearchRotation.step state request).execution⟩

noncomputable def run {h : Nat} (state : State h) : List (Fin (keyCount h)) → State h × Nat
  | [] => (state, 0)
  | request :: requests =>
      let last := run (next state request) requests
      (last.1, (step state request).cost + last.2)

theorem run_execution {h : Nat} (state : State h) (requests : List (Fin (keyCount h))) :
    SearchRotation.Execution state.tree (requests.map Fin.val)
      (run state requests).1.tree (run state requests).2 := by
  induction requests generalizing state with
  | nil => exact .nil _
  | cons request requests ih => exact .cons (step state request).execution (ih _)

/-- Once active, the entire continuation is exactly the canonical strategy. -/
theorem run_active {h : Nat} (state : OnlineSearchRotation.State h) (requests : List (Fin (keyCount h))) :
    run (.active state) requests =
      (.active (OnlineSearchRotation.run state requests).1, (OnlineSearchRotation.run state requests).2) := by
  induction requests generalizing state with
  | nil => rfl
  | cons request requests ih => simp only [run, next, step, ih, OnlineSearchRotation.run]

theorem run_nil {h : Nat} (tree : BST 0 (keyCount h)) :
    (run (.fresh tree) []).1.tree = tree.toRaw ∧ (run (.fresh tree) []).2 = 0 := ⟨rfl, rfl⟩

theorem run_nonempty_state {h : Nat} (tree : BST 0 (keyCount h))
    (requests : List (Fin (keyCount h))) (nonempty : requests ≠ []) :
    (run (.fresh tree) requests).1 = .active (OnlineSearchRotation.run (OnlineSearchRotation.initial h) requests).1 := by
  cases requests with
  | nil => exact (nonempty rfl).elim
  | cons request requests => simp only [run, next, run_active, OnlineSearchRotation.run]

/-- Every extension continues from the same already chosen prefix state. -/
theorem run_append {h : Nat} (state : State h) (first last : List (Fin (keyCount h))) :
    run state (first ++ last) =
      let front := run state first
      let back := run front.1 last
      (back.1, front.2 + back.2) := by
  induction first generalizing state with
  | nil => simp only [List.nil_append, run, Nat.zero_add]
  | cons request first ih => simp only [List.cons_append, run, ih, Nat.add_assoc]

theorem run_state_append {h : Nat} (state : State h) (first last : List (Fin (keyCount h))) :
    (run state (first ++ last)).1 = (run (run state first).1 last).1 := by rw [run_append]

theorem run_cost_append {h : Nat} (state : State h) (first last : List (Fin (keyCount h))) :
    (run state (first ++ last)).2 = (run state first).2 + (run (run state first).1 last).2 := by
  rw [run_append]

/-- A single linear allowance pays initialization and the first search. -/
theorem initialization_cost_bound {h : Nat} (tree : BST 0 (keyCount h)) (requests : List (Fin (keyCount h))) :
    (run (.fresh tree) requests).2 ≤ 19 * keyCount h + (OnlineSearchRotation.run (OnlineSearchRotation.initial h) requests).2 := by
  cases requests with
  | nil => exact Nat.zero_le _
  | cons request requests =>
    have bound := (firstStep tree request).bound
    simp only [run, next, step, run_active, OnlineSearchRotation.run]
    omega

theorem initialized_bound {h : Nat} (tree : BST 0 (keyCount h)) (requests : List (Fin (keyCount h))) :
    (run (.fresh tree) requests).2 ≤
      19 * keyCount h + 134880000000 * (OPT requests + keyCount h) * factor h :=
  (initialization_cost_bound tree requests).trans
    (Nat.add_le_add_left (OnlineSearchRotation.canonical_bound h requests) _)

theorem initialized_competitor_bound {h : Nat} (tree : BST 0 (keyCount h))
    (requests : List (Fin (keyCount h))) (competitor : BST 0 (keyCount h))
    {final : RawTree Nat} {cost : Nat}
    (execution : SearchRotation.Execution competitor.toRaw (requests.map Fin.val) final cost) :
    (run (.fresh tree) requests).2 ≤
      19 * keyCount h + 269760000000 * (cost + keyCount h) * factor h :=
  (initialization_cost_bound tree requests).trans
    (Nat.add_le_add_left (OnlineSearchRotation.canonical_competitor_bound h requests competitor execution) _)

end ChaCha.Paper20261030.OnlineSearchRotationInitialization
