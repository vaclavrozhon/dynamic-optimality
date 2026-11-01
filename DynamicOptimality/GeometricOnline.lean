import DynamicOptimality.GeometricFromBST
import DynamicOptimality.ModelOnlineNormalization

/-!
# Online geometric strategies and the BST-to-geometry simulation

The geometric interface stores only a last-touch surface, its next time,
and arbitrary internal state. Every chosen row contains the request and
satisfies the geometric rectangle condition. Its cost is its cardinality.
No tree or physical-execution witness occurs in this interface.

A rooted-hull strategy induces one fixed online geometric strategy, with
exactly the same total cost. Together with online rotation postponement,
this converts every shared `OnlineBST` into an online geometric strategy
with at most twice its cost on every finite prefix. These are forward
simulations; no online geometric-to-BST converse is claimed here.
-/

namespace DynamicOptimality.Geometry

open GreedyMerge.Geometry
open TangoSquared.MTR TangoSquared.MTR.Tree.PriorityHull

/-- Pure online geometry. The freshness condition makes each new row later
than every previous touch represented by the stored surface. -/
structure OnlineStrategy (n : Nat) where
  State : Type
  height : State → Nat → Int
  time : State → Int
  row : State → Fin n → Finset Nat
  advance : State → Fin n → State
  fresh : ∀ state key, key < n → height state key < time state
  valid : ∀ state request, RowSatisfies (height state) n (row state request)
  requested : ∀ state request, request.val ∈ row state request
  height_next : ∀ state request,
    height (advance state request) = update (height state) (time state) (row state request)
  time_next : ∀ state request, time (advance state request) = time state + 1

namespace OnlineStrategy

variable {n : Nat}

def run (strategy : OnlineStrategy n) (state : strategy.State) :
    List (Fin n) → strategy.State × Nat
  | [] => (state, 0)
  | request :: requests =>
    let rest := strategy.run (strategy.advance state request) requests
    (rest.1, (strategy.row state request).card + rest.2)

def rows (strategy : OnlineStrategy n) (state : strategy.State) :
    List (Fin n) → List (Finset Nat)
  | [] => []
  | request :: requests =>
    strategy.row state request :: strategy.rows (strategy.advance state request) requests

theorem run_append (strategy : OnlineStrategy n) (state : strategy.State)
    (first last : List (Fin n)) :
    strategy.run state (first ++ last) =
      let front := strategy.run state first
      let back := strategy.run front.1 last
      (back.1, front.2 + back.2) := by
  induction first generalizing state with
  | nil => simp [run]
  | cons request first ih => simp only [List.cons_append, run, ih, Nat.add_assoc]

theorem rows_append (strategy : OnlineStrategy n) (state : strategy.State)
    (first last : List (Fin n)) :
    strategy.rows state (first ++ last) = strategy.rows state first ++
      strategy.rows (strategy.run state first).1 last := by
  induction first generalizing state with
  | nil => rfl
  | cons request first ih => simp only [List.cons_append, rows, run, ih]

/-- The rows are those fixed by this strategy's transitions, not witnesses
selected after the complete request sequence is supplied. -/
theorem run_surface (strategy : OnlineStrategy n) (state : strategy.State)
    (requests : List (Fin n)) :
    SurfaceExecution n (strategy.height state) (strategy.time state)
      (requests.map Fin.val) (strategy.rows state requests) (strategy.run state requests).2 := by
  induction requests generalizing state with
  | nil => exact .nil _ _
  | cons request requests ih =>
    have rest := ih (strategy.advance state request)
    rw [strategy.height_next, strategy.time_next] at rest
    exact .cons (strategy.valid state request) (strategy.requested state request) rest

theorem run_arboral (strategy : OnlineStrategy n) (state : strategy.State)
    (requests : List (Fin n)) {history : Finset Point}
    (surface : HasSurface history (strategy.height state) n)
    (satisfied : ArborallySatisfied history) :
    ArboralExecution n history (strategy.time state) (requests.map Fin.val)
      (strategy.rows state requests) (strategy.run state requests).2 :=
  (strategy.run_surface state requests).toArboral surface (strategy.fresh state) satisfied

/-- Starting from the standard uncharged horizontal row gives the same
geometric execution relation used in the five-model cost comparison. -/
theorem run_execution (strategy : OnlineStrategy n) (state : strategy.State)
    (initialHeight : strategy.height state = fun _ => 0)
    (initialTime : strategy.time state = 1) (requests : List (Fin n)) :
    Execution n (requests.map Fin.val) (strategy.run state requests).2 := by
  apply execution_iff_surface.mpr
  refine ⟨strategy.rows state requests, ?_⟩
  simpa only [initialHeight, initialTime] using strategy.run_surface state requests

theorem run_points (strategy : OnlineStrategy n) (state : strategy.State)
    (initialHeight : strategy.height state = fun _ => 0)
    (initialTime : strategy.time state = 1) (requests : List (Fin n)) :
    RowsServe n (requests.map Fin.val) (strategy.rows state requests) ∧
      (points 1 (strategy.rows state requests)).card = (strategy.run state requests).2 ∧
      ArborallySatisfied (points 1 (strategy.rows state requests)) := by
  have surface : HasSurface (baseline n) (strategy.height state) n := by
    rw [initialHeight]
    exact baseline_surface n
  have result := strategy.run_arboral state requests surface (baseline_satisfied n)
  rw [initialTime] at result
  obtain ⟨serve, charge, satisfied⟩ := result.spec (baseline_satisfied n)
  refine ⟨serve, (points_card 1 _).trans charge, ?_⟩
  apply (baseline_union_iff (serve.points_bounded 1) ?_).mp satisfied
  intro point member
  have := points_lower member
  omega

end OnlineStrategy

namespace OnlineHull

variable {n : Nat}

/-- The particular hull witness is fixed per source state and request. -/
noncomputable def access (source : OnlineHullBST n) (state : source.State) (request : Fin n) :
    HullAccess request.val (source.tree state).toRaw
      (source.tree (source.advance state request)).toRaw :=
  Classical.choose (source.legal state request)

theorem access_cost (source : OnlineHullBST n) (state : source.State) (request : Fin n) :
    (access source state request).cost = source.accessCost state request :=
  (Classical.choose_spec (source.legal state request)).symm

theorem keys (source : OnlineHullBST n) (state : source.State) (key : Nat) :
    key ∈ (source.tree state).toRaw.inorder ↔ key < n := by
  rw [BST.toRaw_mem]
  omega

structure State (source : OnlineHullBST n) where
  physical : source.State
  height : Nat → Int
  time : Int
  heap : Heap height (source.tree physical).toRaw
  fresh : ∀ key, key < n → height key < time

noncomputable def advance (source : OnlineHullBST n) (state : State source) (request : Fin n) :
    State source where
  physical := source.advance state.physical request
  height := update state.height state.time (hullRow (access source state.physical request))
  time := state.time + 1
  heap := hull_row_heap (access source state.physical request) (source.tree _).toRaw_ordered
    (keys source state.physical) state.height state.time state.heap state.fresh
  fresh := update_below_next state.fresh

noncomputable def strategy (source : OnlineHullBST n) : OnlineStrategy n where
  State := State source
  height state := state.height
  time state := state.time
  row state request := hullRow (access source state.physical request)
  advance := advance source
  fresh state := state.fresh
  valid state request := hull_row_satisfies (access source state.physical request)
    (source.tree _).toRaw_ordered (keys source state.physical) state.height state.heap
  requested state request := by
    simpa only [hullRow, List.mem_toFinset] using (access source state.physical request).requested
  height_next _ _ := rfl
  time_next _ _ := rfl

def initial (source : OnlineHullBST n) (state : source.State) : State source where
  physical := state
  height := fun _ => 0
  time := 1
  heap := heap_uniform _ _ 0 (by intros; rfl)
  fresh := by intros; omega

/-- The geometric strategy retains the exact current physical source state. -/
theorem run_state (source : OnlineHullBST n) (state : State source)
    (requests : List (Fin n)) :
    ((strategy source).run state requests).1.physical =
      (source.run state.physical requests).1 := by
  induction requests generalizing state with
  | nil => rfl
  | cons request requests ih => exact ih _

theorem run_cost (source : OnlineHullBST n) (state : State source)
    (requests : List (Fin n)) :
    ((strategy source).run state requests).2 = (source.run state.physical requests).2 := by
  induction requests generalizing state with
  | nil => rfl
  | cons request requests ih =>
    change (hullRow (access source state.physical request)).card +
        ((strategy source).run (advance source state request) requests).2 = _
    rw [ih, hull_row_card _ (source.tree _).toRaw_ordered, access_cost]
    rfl

theorem initial_height (source : OnlineHullBST n) (state : source.State) :
    (strategy source).height (initial source state) = fun _ => 0 := rfl

theorem initial_time (source : OnlineHullBST n) (state : source.State) :
    (strategy source).time (initial source state) = 1 := rfl

theorem execution (source : OnlineHullBST n) (state : source.State)
    (requests : List (Fin n)) :
    Execution n (requests.map Fin.val) (source.run state requests).2 := by
  have result := (strategy source).run_execution (initial source state) rfl rfl requests
  rw [run_cost] at result
  exact result

end OnlineHull

namespace OnlineSearch

variable {n : Nat}

noncomputable def strategy (source : OnlineBST n) : OnlineStrategy n :=
  OnlineHull.strategy (OnlineModel.Normalization.hullStrategy source)

noncomputable def initial (source : OnlineBST n) (state : source.State) :
    (strategy source).State :=
  OnlineHull.initial _ (OnlineModel.Normalization.initialFromState source state)

theorem run_cost_le (source : OnlineBST n) (state : source.State) (requests : List (Fin n)) :
    ((strategy source).run (initial source state) requests).2 ≤
      2 * (source.run state requests).2 := by
  change ((OnlineHull.strategy _).run _ requests).2 ≤ _
  rw [OnlineHull.run_cost]
  exact OnlineModel.Normalization.hull_cost_le_from_state source state requests

theorem execution (source : OnlineBST n) (state : source.State) (requests : List (Fin n)) :
    Execution n (requests.map Fin.val)
      ((strategy source).run (initial source state) requests).2 :=
  (strategy source).run_execution (initial source state) rfl rfl requests

theorem initial_height (source : OnlineBST n) (state : source.State) :
    (strategy source).height (initial source state) = fun _ => 0 := rfl

theorem initial_time (source : OnlineBST n) (state : source.State) :
    (strategy source).time (initial source state) = 1 := rfl

end OnlineSearch
end DynamicOptimality.Geometry
