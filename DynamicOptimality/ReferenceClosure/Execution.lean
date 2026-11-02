import DynamicOptimality.ReferenceClosure.TimeInterval

/-!
# Reference-closed executions in the shared geometric model

Every execution admits rowwise NCA closure at at most twice its original
touch cost. Requests and row times stay fixed, including repeated requests.
The initialization row remains the shared uncharged complete baseline.
-/

namespace DynamicOptimality.Geometry.ReferenceClosure

open Splay.Tree

theorem rowAt_union (a b : Finset Point) (time : Int) :
    rowAt (a ∪ b) time = rowAt a time ∪ rowAt b time := by
  ext key
  simp only [mem_rowAt, Finset.mem_union]

theorem rowAt_horizontal (keys : Finset Nat) (time query : Int) :
    rowAt (keys.image fun key => (key,time)) query = if query = time then keys else ∅ := by
  ext key
  rw [mem_rowAt]
  by_cases equal : query = time
  · simp [equal]
  · simp [equal, Ne.symm equal]

theorem rowAt_points_before (rows : List (Finset Nat)) {time query : Int} (before : query < time) :
    rowAt (points time rows) query = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro key member
  have := points_lower (mem_rowAt.mp member)
  omega

theorem rowAt_points_cons (head : Finset Nat) (tail : List (Finset Nat)) (time query : Int) :
    rowAt (points time (head :: tail)) query =
      if query = time then head else rowAt (points (time+1) tail) query := by
  rw [points, rowAt_union, rowAt_horizontal]
  by_cases equal : query = time
  · subst query
    rw [if_pos rfl, rowAt_points_before tail (by omega), Finset.union_empty]
    simp
  · simp only [if_neg equal, Finset.empty_union]

theorem rowAt_points_map (f : Finset Nat → Finset Nat) (empty : f ∅ = ∅)
    (rows : List (Finset Nat)) (time query : Int) :
    rowAt (points time (rows.map f)) query = f (rowAt (points time rows) query) := by
  induction rows generalizing time with
  | nil => simp [points, rowAt, empty]
  | cons head tail ih =>
    rw [List.map_cons, rowAt_points_cons, rowAt_points_cons]
    by_cases equal : query = time
    · simp only [if_pos equal]
    · simp only [if_neg equal, ih]

theorem row_empty {lo hi : Nat} (tree : BST lo hi) : row tree ∅ = ∅ := by
  apply (row_eq_empty_iff tree ∅).mpr
  simp [selected]

theorem points_map_row {lo hi : Nat} (tree : BST lo hi) (rows : List (Finset Nat)) (time : Int)
    (bounded : ∀ p ∈ points time rows, lo ≤ p.1 ∧ p.1 < hi) :
    points time (rows.map (row tree)) = closePoints tree (points time rows) := by
  ext ⟨key, query⟩
  rw [← mem_rowAt, rowAt_points_map (row tree) (row_empty tree)]
  exact (closePoints_mem_bounded tree bounded (key,query)).symm

theorem rowsServe_map_row {n : Nat} (tree : BST 0 n) {requests : List Nat}
    {rows : List (Finset Nat)} (serve : RowsServe n requests rows) :
    RowsServe n requests (rows.map (row tree)) := by
  induction serve with
  | nil => exact .nil
  | @cons request original requests rows head tail ih =>
    refine .cons ⟨?_, ?_⟩ ih
    · exact selected_subset_row tree original ((mem_selected tree original).mpr
        ⟨head.1, Nat.zero_le _, head.2 request head.1⟩)
    · exact fun key member => (row_bounded tree original key member).2

/-- The concrete row transformation yields an execution of the same word,
with doubled cost and NCA-closed rows and closed-interval unions. -/
theorem execution_referenceClosure {n : Nat} (tree : BST 0 n) {requests : List Nat} {cost : Nat}
    (execution : Execution n requests cost) :
    ∃ rows, ArboralExecution n (baseline n) 1 requests rows (rowCost rows) ∧
      rowCost rows ≤ 2 * cost ∧
      (∀ time, row tree (rowAt (points 1 rows) time) = rowAt (points 1 rows) time) ∧
      (∀ start finish, row tree (intervalKeys (points 1 rows) start finish) =
        intervalKeys (points 1 rows) start finish) := by
  obtain ⟨rows, serve, charge, satisfied⟩ := execution_iff_points.mp execution
  have bounded : ∀ p ∈ points 1 rows, 0 ≤ p.1 ∧ p.1 < n :=
    fun p member => ⟨Nat.zero_le _, serve.points_bounded 1 p member⟩
  have mapped := points_map_row tree rows 1 bounded
  have served := rowsServe_map_row tree serve
  have closedSatisfied : ArborallySatisfied (points 1 (rows.map (row tree))) := by
    rw [mapped]
    exact closePoints_satisfied tree satisfied
  refine ⟨rows.map (row tree), ?_, ?_, ?_, ?_⟩
  · apply arboralExecution_of_final served
    · intro p member
      obtain ⟨key, _, rfl⟩ := Finset.mem_image.mp member
      change (0 : Int) < 1
      decide
    · apply (baseline_union_iff (served.points_bounded 1) ?_).mpr closedSatisfied
      intro p member
      have := points_lower member
      omega
  · rw [← points_card 1, mapped]
    have bound := closePoints_card_le tree bounded
    simpa [charge] using bound
  · intro time
    rw [mapped]
    exact closed_rows tree bounded time
  · intro start finish
    rw [mapped]
    exact closePoints_interval_closed tree satisfied bounded start finish

end DynamicOptimality.Geometry.ReferenceClosure
