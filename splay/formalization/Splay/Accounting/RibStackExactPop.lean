import Splay.Accounting.RibStackFilledMaximum

namespace Splay.Accounting.OfflineConnectedSupport

open Splay.Tree OfflineNormalForm.RibStack

namespace SupportFrontier

/-- The final key separates its literal left frontier and right payload
uniquely, including their dependent interval indices. -/
theorem append_last_injective {lower key otherKey upper : ℕ}
    (a : SupportFrontier lower key) (b : SupportFrontier lower otherKey)
    (payload : BST (key + 1) upper) (other : BST (otherKey + 1) upper)
    (same : a.append (.last payload) = b.append (.last other)) :
    key = otherKey ∧ HEq a b ∧ HEq payload other := by
  induction a generalizing otherKey with
  | last tree =>
      cases b with
      | last tree' =>
          cases same
          exact ⟨rfl, HEq.rfl, HEq.rfl⟩
      | next tree' tail =>
          have count := congrArg SupportFrontier.card same
          simp only [card_append, card] at count
          omega
  | next tree tail ih =>
      cases b with
      | last tree' =>
          have count := congrArg SupportFrontier.card same
          simp only [card_append, card] at count
          omega
      | next tree' tail' =>
          simp only [append] at same
          injection same with lowerEq rootEq upperEq treeEq tailEq
          subst rootEq
          cases treeEq
          obtain ⟨keyEq, tailEq', payloadEq⟩ := ih tail' payload other (eq_of_heq tailEq)
          subst keyEq
          cases tailEq'
          exact ⟨rfl, HEq.rfl, payloadEq⟩

end SupportFrontier

theorem MinimumStack.exists_pop_next {capacity lower root upper : ℕ}
    (payload : BST lower root) (rest : SupportFrontier (root + 1) upper)
    (stack : MinimumStack capacity (.next payload rest)) :
    ∃ result : MinimumStack capacity rest,
      HasSupportedPath stack.tree (.node payload result.tree)
        (16 * Digits.popCost 0 stack.digits) (16 * Digits.popCost 0 stack.digits) ∧
      16 * Digits.popCost 0 stack.digits + result.potential ≤ stack.potential + 112 := by
  obtain ⟨key, payload', rest', result, same, _, path, amortized⟩ :=
    stack.exists_pop (by simp [SupportFrontier.card])
  cases same
  exact ⟨result, path, amortized⟩

theorem MaximumStack.exists_pop_last {capacity lower root upper : ℕ}
    (rest : SupportFrontier lower root) (payload : BST (root + 1) upper)
    (stack : MaximumStack capacity (rest.append (.last payload))) :
    ∃ result : MaximumStack capacity rest,
      HasSupportedPath stack.tree (.node result.tree payload)
        (16 * Digits.popCost 0 stack.digits) (16 * Digits.popCost 0 stack.digits) ∧
      16 * Digits.popCost 0 stack.digits + result.potential ≤ stack.potential + 112 := by
  obtain ⟨key, rest', payload', result, same, _, path, amortized⟩ :=
    stack.exists_pop (by rw [SupportFrontier.card_append]; simp [SupportFrontier.card])
  obtain ⟨keyEq, restEq, payloadEq⟩ := rest.append_last_injective rest' payload payload' same
  subst keyEq
  cases restEq
  cases payloadEq
  exact ⟨result, path, amortized⟩

end Splay.Accounting.OfflineConnectedSupport
