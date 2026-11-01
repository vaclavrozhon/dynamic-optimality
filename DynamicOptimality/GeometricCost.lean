import DynamicOptimality.GeometricFromBST
import DynamicOptimality.GeometricToBST
import DynamicOptimality.ModelCostEquivalence

/-!
# The geometric cost relation and the shared optimum

The cost counts touched keys in the actual request rows. The geometric
definition consists only of finite points, requests, and the closed-rectangle
condition; it does not assume a tree execution or a comparison algorithm.
-/

namespace DynamicOptimality.ModelCosts

def geometry : CostRelation := fun {n} requests cost =>
  Geometry.Execution n (requests.map Fin.val) cost

theorem geometry_of_hull {n cost : Nat} {requests : List (Fin n)}
    (run : hull requests cost) : geometry requests cost := by
  obtain ⟨initial, final, execution⟩ := run
  apply Geometry.of_hullExecution execution initial.toRaw_ordered
  intro key
  rw [BST.toRaw_mem]
  omega

/-- The same shared optimum supplies a satisfying point set with no
increase in cost and no charged artificial initialization row. -/
theorem geometry_upper {n : Nat} (requests : List (Fin n)) :
    ∃ cost, geometry requests cost ∧ cost ≤ OPT requests := by
  obtain ⟨cost, execution, bound⟩ := hullComparison.upper requests
  exact ⟨cost, geometry_of_hull execution, by simpa [hullComparison] using bound⟩

/-- Exact equality of the attainable costs in the freely initialized
rooted-hull and geometric models. The converse reconstruction is offline. -/
theorem geometry_iff_hull {n cost : Nat} {requests : List (Fin n)} :
    geometry requests cost ↔ hull requests cost := by
  constructor
  · intro execution
    exact Geometry.to_hullExecution execution
  · exact geometry_of_hull

def geometryComparison : CostComparison geometry where
  lowerFactor := 13
  upperFactor := 1
  lower_pos := by decide
  upper_pos := by decide
  lower {n} requests {cost} run :=
    hullComparison.lower requests (geometry_iff_hull.mp run)
  upper {n} requests := by
    obtain ⟨cost, execution, bound⟩ := geometry_upper requests
    exact ⟨cost, execution, by simpa using bound⟩

end DynamicOptimality.ModelCosts
