import DynamicOptimality.GeometricOnlineSimulation.CausalInitialized
import DynamicOptimality.GeometricOnlineGreedy

/-! # An actual online BST realization of the existing Greedy algorithm

This specializes the general causal simulator to the already defined
Greedy rows and their unchanged negative-depth initialization. It adds no
competitive hypothesis and no replacement definition of Greedy's cost.
-/

namespace DynamicOptimality.Geometry.OnlineGreedy

/-- Fix Greedy's reference initialization before all request words. One
online ordinary BST strategy simulates those rows within constant factor,
from any supplied physical initial BST on the same keys. -/
theorem exists_onlineBST {n : Nat} (reference : BST 0 n) :
    ∃ target : OnlineBST n, ∃ start : BST 0 n → target.State,
      (∀ before, target.tree (start before) = before.toRaw) ∧
      ∀ before requests, (target.run (start before) requests).2 ≤
        387*n + 381*Greedy.cost reference requests := by
  obtain ⟨target, start, initialTree, bound⟩ :=
    (strategy n).exists_onlineBST (initial reference) (initial_height reference)
  refine ⟨target, start, initialTree, ?_⟩
  intro before requests
  simpa only [initialized_cost] using bound before requests

end DynamicOptimality.Geometry.OnlineGreedy
