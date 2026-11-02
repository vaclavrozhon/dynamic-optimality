import DynamicOptimality.Funnel.ExactPathCount
import Mathlib.Algebra.BigOperators.Fin

/-! # Chronological accumulation of warm search-path switches -/

namespace DynamicOptimality.Funnel.Warm

variable {α : Type*} [LinearOrder α]

def pathCost (history : List α) (x : α) : Nat :=
  changes ((ancestors x (cartesian history)).map (fun q => decide (q < x)))

def pathRun (history : List α) : List α → Nat
  | [] => 0
  | x :: rest => pathCost history x + pathRun (x :: history) rest

theorem pathRun_eq_sum (history word : List α) :
    pathRun history word = ∑ p : Fin word.length,
      pathCost ((word.take p.val).reverse ++ history) (word.get p) := by
  induction word generalizing history with
  | nil => simp [pathRun]
  | cons x rest ih =>
    rw [pathRun,ih]
    simp [Fin.sum_univ_succ,List.get_eq_getElem,List.reverse_cons,List.append_assoc]

theorem wordCount_eq_pathRun (word : List α) : wordCount word = pathRun [] word := by
  rw [wordCount_eq_sum_path_changes,pathRun_eq_sum]
  simp only [List.append_nil,pathCost]

end DynamicOptimality.Funnel.Warm
