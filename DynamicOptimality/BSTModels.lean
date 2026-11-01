import DynamicOptimality.GeometricCost
import DynamicOptimality.ModelInitialization
import DynamicOptimality.ModelOnlineNormalization
import DynamicOptimality.GeometricOnlineGreedy

/-!
# Five equivalent models of binary search trees

The finite-execution theorem `transfer` compares any pair of the five
models with uniform constants and the same original key universe. All
competitiveness statements use the existing `OPT`; no new optimum is
introduced. Geometric feasibility is the ordinary arborally satisfied
point-set condition, as established by `Geometry.execution_iff_points`.

Online conversions between the four tree models are also imported, as
are the online conversion from BSTs to geometry and the exact online
geometric Greedy strategy. The offline geometric reconstruction does not
by itself assert the reverse online simulation.
-/

namespace DynamicOptimality

inductive BSTModel where
  | root
  | search
  | pointer
  | hull
  | geometry
  deriving DecidableEq, Repr

namespace BSTModel

def costs : BSTModel → CostRelation
  | .root => ModelCosts.root
  | .search => ModelCosts.search
  | .pointer => ModelCosts.pointer
  | .hull => ModelCosts.hull
  | .geometry => ModelCosts.geometry

def comparison : (model : BSTModel) → CostComparison model.costs
  | .root => ModelCosts.rootComparison
  | .search => ModelCosts.searchComparison
  | .pointer => ModelCosts.pointerComparison
  | .hull => ModelCosts.hullComparison
  | .geometry => ModelCosts.geometryComparison

/-- Each model bounds the same shared optimum from below. -/
theorem OPT_le (model : BSTModel) {n cost : Nat} (requests : List (Fin n))
    (run : model.costs requests cost) :
    OPT requests ≤ model.comparison.lowerFactor * cost :=
  model.comparison.lower requests run

/-- Each model admits an actual witness within a constant of the shared OPT. -/
theorem exists_cost_le (model : BSTModel) {n : Nat} (requests : List (Fin n)) :
    ∃ cost, model.costs requests cost ∧
      cost ≤ model.comparison.upperFactor * OPT requests :=
  model.comparison.upper requests

/-- All ordered pairs of the five models admit finite-execution conversions.
Initial trees are freely chosen; neither online choices nor identical
final trees are claimed by this cost-comparison theorem. -/
theorem transfer (source target : BSTModel) {n cost : Nat}
    {requests : List (Fin n)} (run : source.costs requests cost) :
    ∃ targetCost, target.costs requests targetCost ∧
      targetCost ≤ (target.comparison.upperFactor * source.comparison.lowerFactor) * cost :=
  source.comparison.transfer target.comparison run

/-- A single numerical constant works simultaneously for all 25 ordered
model pairs, all finite universes, and all request sequences. -/
theorem all_five_equivalent (source target : BSTModel) {n cost : Nat}
    {requests : List (Fin n)} (run : source.costs requests cost) :
    ∃ targetCost, target.costs requests targetCost ∧ targetCost ≤ 481 * cost := by
  obtain ⟨targetCost, actual, bound⟩ := source.transfer target run
  have lower : source.comparison.lowerFactor ≤ 13 := by cases source <;> decide
  have upper : target.comparison.upperFactor ≤ 37 := by cases target <;> decide
  have product : target.comparison.upperFactor * source.comparison.lowerFactor ≤ 481 :=
    (Nat.mul_le_mul upper lower).trans (by decide)
  exact ⟨targetCost, actual, bound.trans (Nat.mul_le_mul_right cost product)⟩

/-- Competitive bounds are independent of which of these five models is
used for the competitor. The algorithm cost itself remains unchanged. -/
theorem competitive_iff (model : BSTModel) (cost : AlgorithmCost) (factor : Nat → Nat) :
    Competitive cost factor ↔
      ∃ C : Nat, 0 < C ∧ ∀ n : Nat, 0 < n →
        ∀ initial : BST 0 n, ∀ requests : List (Fin n),
          ∀ competitorCost, model.costs requests competitorCost →
            cost initial requests ≤ C * (competitorCost + n) * factor n :=
  model.comparison.competitive_iff cost factor

end BSTModel
end DynamicOptimality
