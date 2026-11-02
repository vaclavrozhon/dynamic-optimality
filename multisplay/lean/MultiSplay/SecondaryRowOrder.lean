import MultiSplay.SecondaryVariation
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Reversing query blocks without resetting a secondary row

Each pair contains the ancestor writes and the fixed final-query write block.
The latter may be empty in a row not containing the final query depth. The
entire chronological row word is retained in the estimate.
-/

namespace MultiSplay.Secondary

open ChaCha (changesFrom)

theorem row_order_bound (initial : Bool) (blocks : List (List Bool × List Bool)) (front : List Bool) :
    changesFrom initial (front ++ blocks.flatMap (fun block => block.1.reverse++block.2)) ≤
      changesFrom initial (front ++ blocks.flatMap (fun block => block.1++block.2)) +
        2 * (blocks.map (fun block => if Mixed block.1 then 1 else 0)).sum := by
  induction blocks generalizing front with
  | nil => simp
  | cons block rest ih =>
      have head := contextual_reversal_mixed initial front block.1
        (block.2 ++ rest.flatMap (fun block => block.1.reverse++block.2))
      have tail := ih (front++block.1++block.2)
      simp only [List.flatMap_cons, List.map_cons, List.sum_cons, List.append_assoc] at head tail ⊢
      omega

theorem mixed_reverse (word : List Bool) : Mixed word.reverse ↔ Mixed word := by
  simp only [Mixed, List.mem_reverse]

theorem row_order_reverse_bound (initial : Bool) (blocks : List (List Bool × List Bool)) (front : List Bool) :
    changesFrom initial (front ++ blocks.flatMap (fun block => block.1++block.2)) ≤
      changesFrom initial (front ++ blocks.flatMap (fun block => block.1.reverse++block.2)) +
        2 * (blocks.map (fun block => if Mixed block.1 then 1 else 0)).sum := by
  have bound := row_order_bound initial (blocks.map (fun block => (block.1.reverse,block.2))) front
  simpa only [List.flatMap_map, List.map_map, Function.comp_def, List.reverse_reverse, mixed_reverse] using bound

/-- Sum the physical chronological row estimates. The mixed-query count can
then be bounded by branching in the secondary interval hierarchy. -/
theorem rows_order_bound {Row Query : Type*} (rows : Finset Row) (queries : List Query)
    (initial : Row → Bool) (ancestors final : Row → Query → List Bool) :
    (∑ row ∈ rows, changesFrom (initial row)
      (queries.flatMap (fun query => (ancestors row query).reverse++final row query))) ≤
    (∑ row ∈ rows, changesFrom (initial row)
      (queries.flatMap (fun query => ancestors row query++final row query))) +
      2 * (queries.map (fun query => ∑ row ∈ rows, if Mixed (ancestors row query) then 1 else 0)).sum := by
  have localBounds := Finset.sum_le_sum (s := rows) (fun row _ =>
    row_order_bound (initial row) (queries.map (fun query => (ancestors row query, final row query))) [])
  simp only [List.nil_append, List.flatMap_map, List.map_map, Function.comp_def,
    Finset.sum_add_distrib, ← Finset.mul_sum] at localBounds
  have exchange : (∑ row ∈ rows, (queries.map (fun query => if Mixed (ancestors row query) then 1 else 0)).sum) =
      (queries.map (fun query => ∑ row ∈ rows, if Mixed (ancestors row query) then 1 else 0)).sum := by
    clear localBounds
    induction queries with
    | nil => simp
    | cons query rest ih => simp [Finset.sum_add_distrib, ih]
  simpa only [exchange] using localBounds

end MultiSplay.Secondary
