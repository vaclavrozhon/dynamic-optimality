import ChaCha.Recency

/-! Composition of actual successful Move-to-Root executions and their costs. -/

namespace ChaCha.MTR
open Tree
variable {α : Type*} [LinearOrder α]

theorem run_append (t : Tree α) (xs ys : List α) :
    run t (xs ++ ys) = run (run t xs) ys := by simp [run, List.foldl_append]

theorem runCost_append (t : Tree α) (xs ys : List α) :
    runCost t (xs ++ ys) = runCost t xs + runCost (run t xs) ys := by
  induction xs generalizing t with
  | nil => simp [runCost, run]
  | cons x xs ih => simp [runCost, run, ih, Nat.add_assoc]

theorem successful_append (t : Tree α) (xs ys : List α) :
    Successful t (xs ++ ys) ↔ Successful t xs ∧ Successful (run t xs) ys := by
  induction xs generalizing t with
  | nil => simp [Successful, run]
  | cons x xs ih =>
    simp only [List.cons_append, Successful, run, List.foldl_cons]
    rw [ih]
    exact and_assoc.symm

theorem inorder_run (t : Tree α) (xs : List α) : inorder (run t xs) = inorder t := by
  induction xs generalizing t with
  | nil => rfl
  | cons x xs ih =>
    change inorder (run (moveToRoot x t) xs) = inorder t
    rw [ih, inorder_moveToRoot]

theorem ordered_run {t : Tree α} (h : Ordered t) (xs : List α) : Ordered (run t xs) := by
  simpa only [Ordered, inorder_run] using h

theorem length_le_runCost (t : Tree α) (xs : List α) : xs.length ≤ runCost t xs := by
  induction xs generalizing t with
  | nil => rfl
  | cons x xs ih =>
    have hi := ih (moveToRoot x t)
    simp only [List.length_cons, runCost]
    omega

end ChaCha.MTR
