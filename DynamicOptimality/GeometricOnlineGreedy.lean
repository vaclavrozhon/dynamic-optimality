import DynamicOptimality.GeometricGreedy
import DynamicOptimality.GeometricOnline

/-!
# The actual Greedy algorithm as one fixed online geometric strategy

The state retains the algorithm's real surface, including its negative
initial depths. The public geometric surface is its nonnegative clamp;
this changes neither chosen rows nor charges. Every transition depends
only on the present state and request.
-/

namespace DynamicOptimality.Geometry.OnlineGreedy

open GreedyMerge.Geometry GreedyMerge.Surface

structure State (n : Nat) where
  actual : Nat → Int
  time : Int
  positive : 0 < time
  fresh : ∀ key, key < n → actual key < time

noncomputable def advance {n : Nat} (state : State n) (request : Fin n) : State n where
  actual := RaiseSurface state.actual n request.val state.time
  time := state.time + 1
  positive := by have := state.positive; omega
  fresh := by
    rw [← update_greedyRow]
    exact update_below_next state.fresh

noncomputable def strategy (n : Nat) : OnlineStrategy n where
  State := State n
  height state := clampSurface state.actual
  time state := state.time
  row state request := GreedyRow state.actual n request.val
  advance := advance
  fresh state key bound := max_lt state.positive (state.fresh key bound)
  valid state request := rowSatisfies_monotone (greedyRow_satisfies state.actual)
    (fun value => max 0 value) (fun _ _ inequality => max_le_max_left 0 inequality)
  requested state request := access_mem_greedyRow state.actual request.isLt
  height_next state request := by
    change clampSurface (RaiseSurface state.actual n request.val state.time) = _
    rw [← update_greedyRow]
    exact clamp_update _ _ _ state.positive.le
  time_next _ _ := rfl

def initial {n : Nat} (tree : BST 0 n) : State n where
  actual := Greedy.initialSurface tree
  time := 1
  positive := by omega
  fresh key _ := Greedy.initialSurface_lt_one tree key

theorem initial_height {n : Nat} (tree : BST 0 n) :
    (strategy n).height (initial tree) = fun _ => 0 := by
  funext key
  change max 0 (-(tree.depth key : Int)) = 0
  omega

theorem run_cost {n : Nat} (state : State n) (requests : List (Fin n)) :
    ((strategy n).run state requests).2 = Greedy.costFrom state.actual state.time requests := by
  induction requests generalizing state with
  | nil => rfl
  | cons request requests ih =>
    change (GreedyRow state.actual n request.val).card +
      ((strategy n).run (advance state request) requests).2 = _
    rw [ih]
    rfl

theorem run_rows {n : Nat} (state : State n) (requests : List (Fin n)) :
    (strategy n).rows state requests = greedyRows state.actual state.time requests := by
  induction requests generalizing state with
  | nil => rfl
  | cons request requests ih =>
    change GreedyRow state.actual n request.val ::
      (strategy n).rows (advance state request) requests = _
    rw [ih]
    rfl

/-- The strategy realizes exactly the existing algorithm's cost from every
supplied initial BST; it is fixed before any future request is supplied. -/
theorem initialized_cost {n : Nat} (tree : BST 0 n) (requests : List (Fin n)) :
    ((strategy n).run (initial tree) requests).2 = Greedy.cost tree requests :=
  run_cost _ _

theorem execution {n : Nat} (tree : BST 0 n) (requests : List (Fin n)) :
    Execution n (requests.map Fin.val) ((strategy n).run (initial tree) requests).2 :=
  (strategy n).run_execution (initial tree) (initial_height tree) rfl requests

end DynamicOptimality.Geometry.OnlineGreedy
