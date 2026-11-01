import DynamicOptimality.GeometricModel
import Greedy.Algorithm

/-!
# The existing Greedy algorithm in the shared geometric model

The algorithm keeps its actual negative-depth initialization. Its chosen
rows are unchanged. Clamping last-touch times below zero to zero preserves
rectangle feasibility and commutes with every positive-time update; this
identifies those exact rows with a feasible execution of the standard
positive-time point-set model. No assertion that the two initializations
produce the same *least* rows is needed or made.
-/

namespace DynamicOptimality.Geometry

open GreedyMerge.Geometry GreedyMerge.Surface

theorem rowSatisfies_monotone {n : Nat} {height : Nat → Int} {row : Finset Nat}
    (satisfied : RowSatisfies height n row) (f : Int → Int) (monotone : Monotone f) :
    RowSatisfies (fun key => f (height key)) n row := by
  refine ⟨satisfied.1, ?_⟩
  intro start member old bound different
  rcases satisfied.2 start member old bound different with touched | blocked | between
  · exact .inl touched
  · obtain ⟨key, inside, notOld, high⟩ := blocked
    exact .inr (.inl ⟨key, inside, notOld, monotone high⟩)
  · exact .inr (.inr between)

def clampSurface (height : Nat → Int) (key : Nat) : Int := max 0 (height key)

theorem clamp_update (height : Nat → Int) (time : Int) (row : Finset Nat)
    (nonnegative : 0 ≤ time) :
    clampSurface (update height time row) = update (clampSurface height) time row := by
  funext key
  by_cases member : key ∈ row
  · simp only [clampSurface, update, if_pos member, max_eq_right nonnegative]
  · simp only [clampSurface, update, if_neg member]

theorem SurfaceExecution.clamp {n : Nat} {height : Nat → Int} {time : Int}
    {requests : List Nat} {rows : List (Finset Nat)} {cost : Nat}
    (execution : SurfaceExecution n height time requests rows cost) (nonnegative : 0 ≤ time) :
    SurfaceExecution n (clampSurface height) time requests rows cost := by
  induction execution with
  | nil => exact .nil _ _
  | @cons height time requests rows cost request row satisfied requested rest ih =>
    have valid := rowSatisfies_monotone satisfied (fun value => max 0 value)
      (fun _ _ inequality => max_le_max_left 0 inequality)
    have next := ih (by omega)
    rw [clamp_update height time row nonnegative] at next
    exact .cons valid requested next

noncomputable def greedyRows {n : Nat} (height : Nat → Int) (time : Int) :
    List (Fin n) → List (Finset Nat)
  | [] => []
  | request :: requests =>
      GreedyRow height n request.val ::
        greedyRows (RaiseSurface height n request.val time) (time+1) requests

theorem update_greedyRow (height : Nat → Int) (time : Int) (n request : Nat) :
    update height time (GreedyRow height n request) = RaiseSurface height n request time := by
  funext key
  by_cases visible : Neighborhood height n key request
  · have member : key ∈ GreedyRow height n request := mem_greedyRow.mpr visible
    simp only [update, RaiseSurface, if_pos member, if_pos visible]
  · have absent : key ∉ GreedyRow height n request := fun member => visible (mem_greedyRow.mp member)
    simp only [update, RaiseSurface, if_neg absent, if_neg visible]

theorem greedy_surface {n : Nat} (height : Nat → Int) (time : Int) (requests : List (Fin n)) :
    SurfaceExecution n height time (requests.map Fin.val) (greedyRows height time requests)
      (Greedy.costFrom height time requests) := by
  induction requests generalizing height time with
  | nil => exact .nil _ _
  | cons request requests ih =>
    have tail : SurfaceExecution n (update height time (GreedyRow height n request.val)) (time+1)
        (requests.map Fin.val) (greedyRows (RaiseSurface height n request.val time) (time+1) requests)
        (Greedy.costFrom (RaiseSurface height n request.val time) (time+1) requests) := by
      rw [update_greedyRow]
      exact ih _ _
    exact .cons (greedyRow_satisfies height) (access_mem_greedyRow height request.isLt) tail

/-- Exact feasibility of the already-defined Greedy cost, starting from
its already-defined negative-depth surface for the supplied initial BST. -/
theorem greedy_cost_geometric {n : Nat} (initial : BST 0 n) (requests : List (Fin n)) :
    Execution n (requests.map Fin.val) (Greedy.cost initial requests) := by
  apply execution_iff_surface.mpr
  have result := (greedy_surface (Greedy.initialSurface initial) 1 requests).clamp (by omega)
  have zero : clampSurface (Greedy.initialSurface initial) = fun _ => 0 := by
    funext key
    simp only [clampSurface, Greedy.initialSurface]
    omega
  rw [zero] at result
  exact ⟨greedyRows (Greedy.initialSurface initial) 1 requests, result⟩

/-- These are the actual Greedy rows, with their exact finite-point cost. -/
theorem greedy_points {n : Nat} (initial : BST 0 n) (requests : List (Fin n)) :
    let rows := greedyRows (Greedy.initialSurface initial) 1 requests
    RowsServe n (requests.map Fin.val) rows ∧
      (points 1 rows).card = Greedy.cost initial requests ∧
      ArborallySatisfied (points 1 rows) := by
  dsimp only
  have result := (greedy_surface (Greedy.initialSurface initial) 1 requests).clamp (by omega)
  have zero : clampSurface (Greedy.initialSurface initial) = fun _ => 0 := by
    funext key
    simp only [clampSurface, Greedy.initialSurface]
    omega
  rw [zero] at result
  have arboral := result.toArboral (baseline_surface n) (by intros; omega) (baseline_satisfied n)
  obtain ⟨serve, charge, satisfied⟩ := arboral.spec (baseline_satisfied n)
  refine ⟨serve, (points_card 1 _).trans charge, ?_⟩
  apply (baseline_union_iff (serve.points_bounded 1) ?_).mp satisfied
  intro point member
  have := points_lower member
  omega

end DynamicOptimality.Geometry
