import DynamicOptimality.OnlineBST
import DynamicOptimality.SearchRotationProjection

/-!
# Projecting an online strategy to an initial interval of keys

The larger tree is free internal state. The actual tree contains only
keys below the cutoff. Every projected access has an actual search and
rotation witness whose cost is no greater than its source access. The
fixed source transition remains a function of the current state and key.
-/

namespace DynamicOptimality.OnlineBST

theorem tree_ordered {n : Nat} (strategy : OnlineBST n) (state : strategy.State) :
    ChaCha.MTR.Tree.Ordered (strategy.tree state) := by
  unfold ChaCha.MTR.Tree.Ordered
  rw [strategy.tree_word]
  exact List.pairwise_lt_range

namespace Projection

variable {n N : Nat}

theorem tree_word (source : OnlineBST N) (included : n ≤ N) (state : source.State) :
    (SearchRotation.Prefix.prune n (source.tree state)).inorder = List.range n := by
  apply List.Pairwise.eq_of_mem_iff
    (SearchRotation.Prefix.ordered n (source.tree_ordered state)) List.pairwise_lt_range
  intro key
  rw [SearchRotation.Prefix.inorder n (source.tree_ordered state),source.tree_word,
    List.mem_filter,List.mem_range,List.mem_range]
  simp only [decide_eq_true_eq]
  omega

structure Transition (source : OnlineBST N) (included : n ≤ N)
    (state : source.State) (request : Fin n) where
  cost : Nat
  execution : SearchRotation.Access request.val
    (SearchRotation.Prefix.prune n (source.tree state))
    (SearchRotation.Prefix.prune n (source.tree (source.advance state (Fin.castLE included request)))) cost
  bound : cost ≤ source.accessCost state (Fin.castLE included request)

theorem transition_exists (source : OnlineBST N) (included : n ≤ N)
    (state : source.State) (request : Fin n) : Nonempty (Transition source included state request) := by
  obtain ⟨cost,execution,bound⟩ := SearchRotation.Prefix.access n
    (source.tree_ordered state) request.isLt (source.legal state (Fin.castLE included request))
  exact ⟨⟨cost,execution,bound⟩⟩

/-- A single access is fixed using only the current state and request. -/
noncomputable def step (source : OnlineBST N) (included : n ≤ N)
    (state : source.State) (request : Fin n) : Transition source included state request :=
  Classical.choice (transition_exists source included state request)

/-- The physical tree has exactly the original `n` keys. The larger source
state is mathematical bookkeeping, and its vertices are never charged as
physical search vertices of the projected strategy. -/
noncomputable def strategy (source : OnlineBST N) (included : n ≤ N) : OnlineBST n where
  State := source.State
  tree := fun state => SearchRotation.Prefix.prune n (source.tree state)
  tree_word := tree_word source included
  advance := fun state request => source.advance state (Fin.castLE included request)
  accessCost := fun state request => (step source included state request).cost
  legal := fun state request => (step source included state request).execution

/-- Projection keeps the exact source states after the embedded requests. -/
theorem run_state (source : OnlineBST N) (included : n ≤ N)
    (state : source.State) (requests : List (Fin n)) :
    ((strategy source included).run state requests).1 =
      (source.run state (requests.map (Fin.castLE included))).1 := by
  induction requests generalizing state with
  | nil => rfl
  | cons request requests ih => exact ih (source.advance state (Fin.castLE included request))

/-- The costs are those of the same fixed projected transitions, not
fresh witnesses chosen after seeing the complete request word. -/
theorem run_cost_le (source : OnlineBST N) (included : n ≤ N)
    (state : source.State) (requests : List (Fin n)) :
    ((strategy source included).run state requests).2 ≤
      (source.run state (requests.map (Fin.castLE included))).2 := by
  induction requests generalizing state with
  | nil => exact le_rfl
  | cons request requests ih =>
    exact Nat.add_le_add (step source included state request).bound
      (ih (source.advance state (Fin.castLE included request)))

/-- The actual output tree is the projection of the exact source output. -/
theorem run_tree (source : OnlineBST N) (included : n ≤ N)
    (state : source.State) (requests : List (Fin n)) :
    (strategy source included).tree ((strategy source included).run state requests).1 =
      SearchRotation.Prefix.prune n (source.tree (source.run state (requests.map (Fin.castLE included))).1) := by
  change SearchRotation.Prefix.prune n (source.tree _) = _
  rw [run_state]

end Projection
end DynamicOptimality.OnlineBST
