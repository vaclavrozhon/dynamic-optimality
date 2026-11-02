import DynamicOptimality.GeometricOnlineSimulation.Causal
import DynamicOptimality.GeometricOnlineSimulation.SplitTree
import DynamicOptimality.OnlineBSTInitialization

/-! # Online geometric-to-BST conversion from an arbitrary supplied tree

The source is any online geometric strategy starting at its zero-time
baseline. One fixed target strategy is chosen before the requests. It
starts at the supplied ordinary BST, pays initialization at most once,
and satisfies its cost estimate simultaneously for every finite prefix.
-/

namespace DynamicOptimality.GeometricOnlineSimulation

/-- Generic initialized simulation, parametrized only by an implemented
split-tree system. The concrete theorem below removes that parameter. -/
theorem exists_initialized_causal_simulation {n : Nat} (system : SplitTreeSystem)
    (source : Geometry.OnlineStrategy n) (initial : source.State)
    (baseline : source.height initial = fun _ => 0) :
    ∃ target : OnlineBST n, ∃ start : BST 0 n → target.State,
      (∀ before, target.tree (start before) = before.toRaw) ∧
      ∀ before requests, (target.run (start before) requests).2 ≤
        (19+2*system.K)*n + (2*system.K+13)*(source.run initial requests).2 := by
  let active := causalStrategy system source
  let canonical := causalInitial system source initial baseline
  let target := OnlineBST.Initialization.strategy active canonical
  refine ⟨target, fun before => Sum.inl before, ?_, ?_⟩
  · intro before
    rfl
  · intro before requests
    have setupBound := OnlineBST.Initialization.run_cost_le active canonical before requests
    have sourceBound := causal_initial_run_cost system source initial baseline requests
    change (target.run (Sum.inl before) requests).2 ≤ _ at setupBound
    change (active.run canonical requests).2 ≤ _ at sourceBound
    nlinarith

end DynamicOptimality.GeometricOnlineSimulation

namespace DynamicOptimality.Geometry.OnlineStrategy

/-- Every online geometric strategy from the complete free baseline has
one causal simulation in the shared ordinary BST model. Actual searches
and rotations are charged, the key universe is unchanged, and the supplied
initial tree contributes only a one-time additive allowance. -/
theorem exists_onlineBST {n : Nat} (source : OnlineStrategy n) (initial : source.State)
    (baseline : source.height initial = fun _ => 0) :
    ∃ target : OnlineBST n, ∃ start : BST 0 n → target.State,
      (∀ before, target.tree (start before) = before.toRaw) ∧
      ∀ before requests, (target.run (start before) requests).2 ≤
        387*n + 381*(source.run initial requests).2 := by
  simpa only [GeometricOnlineSimulation.dyadicSplitTrees] using
    GeometricOnlineSimulation.exists_initialized_causal_simulation
      GeometricOnlineSimulation.dyadicSplitTrees source initial baseline

end DynamicOptimality.Geometry.OnlineStrategy
