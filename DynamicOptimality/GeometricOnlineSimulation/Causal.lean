import DynamicOptimality.GeometricOnlineSimulation.RowsRebuild
import DynamicOptimality.GeometricOnlineSimulation.ClassInitial
import DynamicOptimality.GeometricOnline

/-! # One fixed causal BST strategy for an online geometric strategy

A state contains the geometric strategy's current state and a physical
class tree realizing its last-touch heights. Choices are made once from
that state and the current request. The potential is twice the stored
split-tree credit, so the telescoping estimate holds for every prefix.
-/

namespace DynamicOptimality.GeometricOnlineSimulation

open ChaCha.MTR SearchRotation

structure CausalState {n : Nat} (system : SplitTreeSystem)
    (source : Geometry.OnlineStrategy n) where
  geometric : source.State
  physical : ClassTree system
  valid : physical.Realizes (source.height geometric) 0 n

namespace CausalState

variable {n : Nat} {system : SplitTreeSystem} {source : Geometry.OnlineStrategy n}

structure Step (state : CausalState system source) (request : Fin n) where
  next : CausalState system source
  cost : Nat
  source_next : next.geometric = source.advance state.geometric request
  legal : Access request.val state.physical.tree next.physical.tree cost
  budget : cost + 2*next.physical.credit ≤ 2*state.physical.credit +
    (2*system.K+13)*(source.row state.geometric request).card

theorem step_exists (state : CausalState system source) (request : Fin n) :
    Nonempty (Step state request) := by
  obtain ⟨after, cost, valid, legal, budget⟩ := state.valid.row_access
    (source.fresh state.geometric) (source.valid state.geometric request)
    (source.requested state.geometric request)
  have nextValid : after.Realizes (source.height (source.advance state.geometric request)) 0 n := by
    rw [source.height_next]
    exact valid
  exact ⟨⟨⟨source.advance state.geometric request, after, nextValid⟩,
    cost, rfl, legal, budget⟩⟩

noncomputable def step (state : CausalState system source) (request : Fin n) :
    Step state request := Classical.choice (step_exists state request)

end CausalState

/-- The abstract online strategy uses actual initial-depth-plus-rotations
accesses. Its bookkeeping contains no future request sequence. -/
noncomputable def causalStrategy {n : Nat} (system : SplitTreeSystem)
    (source : Geometry.OnlineStrategy n) : OnlineBST n where
  State := CausalState system source
  tree state := state.physical.tree
  tree_word state := state.valid.full_inorder
  advance state request := (state.step request).next
  accessCost state request := (state.step request).cost
  legal state request := (state.step request).legal

theorem causal_run_source {n : Nat} (system : SplitTreeSystem)
    (source : Geometry.OnlineStrategy n) (state : CausalState system source)
    (requests : List (Fin n)) :
    ((causalStrategy system source).run state requests).1.geometric =
      (source.run state.geometric requests).1 := by
  induction requests generalizing state with
  | nil => rfl
  | cons request rest ih =>
      change ((causalStrategy system source).run (state.step request).next rest).1.geometric = _
      rw [ih, (state.step request).source_next]
      rfl

/-- The same fixed strategy satisfies the amortized estimate on every
finite prefix, with the current geometric state used on both sides. -/
theorem causal_run_budget {n : Nat} (system : SplitTreeSystem)
    (source : Geometry.OnlineStrategy n) (state : CausalState system source)
    (requests : List (Fin n)) :
    ((causalStrategy system source).run state requests).2 +
      2*((causalStrategy system source).run state requests).1.physical.credit ≤
      2*state.physical.credit + (2*system.K+13)*(source.run state.geometric requests).2 := by
  induction requests generalizing state with
  | nil => simp [OnlineBST.run, Geometry.OnlineStrategy.run]
  | cons request rest ih =>
      have first := (state.step request).budget
      have remaining := ih (state.step request).next
      rw [(state.step request).source_next] at remaining
      change (state.step request).cost +
        ((causalStrategy system source).run (state.step request).next rest).2 +
        2*((causalStrategy system source).run (state.step request).next rest).1.physical.credit ≤
        2*state.physical.credit + (2*system.K+13)*
          ((source.row state.geometric request).card +
            (source.run (source.advance state.geometric request) rest).2)
      nlinarith

theorem causal_initial_exists {n : Nat} (system : SplitTreeSystem)
    (source : Geometry.OnlineStrategy n) (initial : source.State)
    (baseline : source.height initial = fun _ => 0) :
    ∃ state : CausalState system source,
      state.geometric = initial ∧ state.physical.credit ≤ system.K*n := by
  obtain ⟨physical, valid, bound⟩ := exists_initial_class system n 0
  refine ⟨⟨initial, physical, ?_⟩, rfl, bound⟩
  simpa only [baseline] using valid

noncomputable def causalInitial {n : Nat} (system : SplitTreeSystem)
    (source : Geometry.OnlineStrategy n) (initial : source.State)
    (baseline : source.height initial = fun _ => 0) : CausalState system source :=
  Classical.choose (causal_initial_exists system source initial baseline)

theorem causalInitial_source {n : Nat} (system : SplitTreeSystem)
    (source : Geometry.OnlineStrategy n) (initial : source.State)
    (baseline : source.height initial = fun _ => 0) :
    (causalInitial system source initial baseline).geometric = initial :=
  (Classical.choose_spec (causal_initial_exists system source initial baseline)).1

theorem causalInitial_credit {n : Nat} (system : SplitTreeSystem)
    (source : Geometry.OnlineStrategy n) (initial : source.State)
    (baseline : source.height initial = fun _ => 0) :
    (causalInitial system source initial baseline).physical.credit ≤ system.K*n :=
  (Classical.choose_spec (causal_initial_exists system source initial baseline)).2

theorem causal_initial_run_cost {n : Nat} (system : SplitTreeSystem)
    (source : Geometry.OnlineStrategy n) (initial : source.State)
    (baseline : source.height initial = fun _ => 0) (requests : List (Fin n)) :
    ((causalStrategy system source).run (causalInitial system source initial baseline) requests).2 ≤
      2*system.K*n + (2*system.K+13)*(source.run initial requests).2 := by
  have budget := causal_run_budget system source
    (causalInitial system source initial baseline) requests
  rw [causalInitial_source] at budget
  have stored := causalInitial_credit system source initial baseline
  nlinarith

end DynamicOptimality.GeometricOnlineSimulation
