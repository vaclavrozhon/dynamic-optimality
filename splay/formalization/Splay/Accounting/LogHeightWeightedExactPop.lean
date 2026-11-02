import Splay.Accounting.LogHeightWeightedMaximum
import Splay.Accounting.RibStackExactPop

namespace Splay.Accounting.OfflineConnectedSupport.LogHeightChocolate

open Splay.Tree

def MinimumStack.empty (capacity boundary : ℕ) : MinimumStack capacity (.last (.empty boundary)) :=
  ⟨.empty boundary, .base (.leaf (.empty boundary)), rfl, Nat.zero_le _⟩

def MaximumStack.empty (capacity boundary : ℕ) : MaximumStack capacity (.last (.empty boundary)) :=
  ⟨capacity, .empty capacity, .base (.leaf (.empty capacity)), .empty boundary,
    .leaf capacity boundary, rfl⟩

theorem MinimumStack.exists_pop_next {capacity lower root upper : ℕ}
    (payload : BST lower root) (rest : SupportFrontier (root + 1) upper)
    (stack : MinimumStack capacity (.next payload rest)) :
    ∃ (result : MinimumStack capacity rest) (cost : ℕ),
      HasSupportedPath stack.tree (.node payload result.tree) cost cost ∧
      cost + result.potential ≤ stack.potential + 16 ∧ cost ≤ stackUnitCost capacity := by
  obtain ⟨key, payload', rest', result, cost, same, path, amortized, worst⟩ :=
    stack.exists_pop (by simp [SupportFrontier.card])
  cases same
  exact ⟨result, cost, path, amortized, worst⟩

theorem MaximumStack.exists_pop_last {capacity lower root upper : ℕ}
    (rest : SupportFrontier lower root) (payload : BST (root + 1) upper)
    (stack : MaximumStack capacity (rest.append (.last payload))) :
    ∃ (result : MaximumStack capacity rest) (cost : ℕ),
      HasSupportedPath stack.tree (.node result.tree payload) cost cost ∧
      cost + result.potential ≤ stack.potential + 16 ∧ cost ≤ stackUnitCost capacity := by
  obtain ⟨key, rest', payload', result, cost, same, path, amortized, worst⟩ :=
    stack.exists_pop (by rw [SupportFrontier.card_append]; simp [SupportFrontier.card])
  obtain ⟨keyEq, restEq, payloadEq⟩ := rest.append_last_injective rest' payload payload' same
  subst keyEq
  cases restEq
  cases payloadEq
  exact ⟨result, cost, path, amortized, worst⟩

end Splay.Accounting.OfflineConnectedSupport.LogHeightChocolate
