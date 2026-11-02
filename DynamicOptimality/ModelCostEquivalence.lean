import DynamicOptimality.ModelEquivalence
import DynamicOptimality.SearchRotationEquivalence

/-!
# Cost comparisons for the four tree models

A `CostRelation` records actual execution costs, with a freely chosen
initial tree on exactly the original keys. It is not a new optimum.
`CostComparison` compares these witnesses with the existing shared `OPT`.
Its constants are uniform over all universes and request sequences,
including the empty universe and empty sequence.

These are comparisons of finite executions. Online simulations are
separate statements; in particular, a normalization may postpone rotations
and need not preserve the final tree of an arbitrary-rotation execution.
-/

namespace DynamicOptimality

open ChaCha ChaCha.MTR

abbrev CostRelation := {n : Nat} → List (Fin n) → Nat → Prop

/-- Two uniform directions of comparison with the same attained `OPT`. -/
structure CostComparison (model : CostRelation) where
  lowerFactor : Nat
  upperFactor : Nat
  lower_pos : 0 < lowerFactor
  upper_pos : 0 < upperFactor
  lower : ∀ {n} (requests : List (Fin n)) {cost},
    model requests cost → OPT requests ≤ lowerFactor * cost
  upper : ∀ {n} (requests : List (Fin n)),
    ∃ cost, model requests cost ∧ cost ≤ upperFactor * OPT requests

namespace CostComparison

/-- Every execution in the first model has a constant-cost witness in the
second model. No common final-tree or online claim is implicit here. -/
theorem transfer {first second : CostRelation}
    (a : CostComparison first) (b : CostComparison second)
    {n cost : Nat} {requests : List (Fin n)} (run : first requests cost) :
    ∃ targetCost, second requests targetCost ∧
      targetCost ≤ (b.upperFactor * a.lowerFactor) * cost := by
  obtain ⟨targetCost, target, bound⟩ := b.upper requests
  refine ⟨targetCost, target, bound.trans ?_⟩
  simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left b.upperFactor (a.lower requests run)

/-- The competitor quantifier can use any of the equivalent models,
without changing the algorithm cost or the shared definition of competitiveness. -/
theorem competitive_iff {model : CostRelation} (comparison : CostComparison model)
    (cost : AlgorithmCost) (factor : Nat → Nat) :
    Competitive cost factor ↔
      ∃ C : Nat, 0 < C ∧ ∀ n : Nat, 0 < n →
        ∀ initial : BST 0 n, ∀ requests : List (Fin n),
          ∀ competitorCost, model requests competitorCost →
            cost initial requests ≤ C * (competitorCost + n) * factor n := by
  constructor
  · rintro ⟨C, positive, bound⟩
    refine ⟨C * comparison.lowerFactor, Nat.mul_pos positive comparison.lower_pos, ?_⟩
    intro n hn initial requests competitorCost run
    have lo := comparison.lower requests run
    have one : 1 ≤ comparison.lowerFactor := comparison.lower_pos
    have startup : n ≤ comparison.lowerFactor * n := by
      simpa using Nat.mul_le_mul_right n one
    calc
      cost initial requests ≤ C * (OPT requests + n) * factor n := bound n hn initial requests
      _ ≤ C * (comparison.lowerFactor * (competitorCost + n)) * factor n := by
        apply Nat.mul_le_mul_right
        apply Nat.mul_le_mul_left
        rw [Nat.mul_add]
        omega
      _ = (C * comparison.lowerFactor) * (competitorCost + n) * factor n := by
        simp only [Nat.mul_assoc]
  · rintro ⟨C, positive, bound⟩
    refine ⟨C * comparison.upperFactor, Nat.mul_pos positive comparison.upper_pos, ?_⟩
    intro n hn initial requests
    obtain ⟨competitorCost, run, hi⟩ := comparison.upper requests
    have one : 1 ≤ comparison.upperFactor := comparison.upper_pos
    have startup : n ≤ comparison.upperFactor * n := by
      simpa using Nat.mul_le_mul_right n one
    calc
      cost initial requests ≤ C * (competitorCost + n) * factor n :=
        bound n hn initial requests competitorCost run
      _ ≤ C * (comparison.upperFactor * (OPT requests + n)) * factor n := by
        apply Nat.mul_le_mul_right
        apply Nat.mul_le_mul_left
        rw [Nat.mul_add]
        omega
      _ = (C * comparison.upperFactor) * (OPT requests + n) * factor n := by
        simp only [Nat.mul_assoc]

end CostComparison

namespace ModelCosts

def root : CostRelation := fun {n} requests cost =>
  ∃ (initial final : BST 0 n) (rotations : Nat),
    OfflineExecution requests initial final rotations ∧ cost = requests.length + rotations

def search : CostRelation := fun {n} requests cost =>
  ∃ (initial : BST 0 n) (final : RawTree Nat),
    SearchRotation.Execution initial.toRaw (requests.map Fin.val) final cost

def pointer : CostRelation := fun {n} requests cost =>
  ∃ (initial : BST 0 n) (final : RawTree Nat),
    PointerExecution initial.toRaw (requests.map Fin.val) final cost

def hull : CostRelation := fun {n} requests cost =>
  ∃ (initial : BST 0 n) (final : RawTree Nat),
    AccessExecution initial.toRaw (requests.map Fin.val) final cost

def rootComparison : CostComparison root where
  lowerFactor := 1
  upperFactor := 1
  lower_pos := by decide
  upper_pos := by decide
  lower {n} requests {cost} run := by
    obtain ⟨initial, final, rotations, execution, rfl⟩ := run
    simpa using OPT_le_execution execution
  upper {n} requests := by
    obtain ⟨initial, final, rotations, execution, optimal⟩ := OPT_attained requests
    exact ⟨OPT requests, ⟨initial, final, rotations, execution, optimal⟩, by omega⟩

def searchComparison : CostComparison search where
  lowerFactor := 2
  upperFactor := 2
  lower_pos := by decide
  upper_pos := by decide
  lower {n} requests {cost} run := by
    obtain ⟨initial, final, execution⟩ := run
    exact SearchRotation.OPT_le_cost initial requests execution
  upper {n} requests := by
    obtain ⟨initial, final, cost, execution, bound⟩ := SearchRotation.exists_cost_le_OPT requests
    exact ⟨cost, ⟨initial, final.toRaw, execution⟩, bound⟩

def pointerComparison : CostComparison pointer where
  lowerFactor := 13
  upperFactor := 37
  lower_pos := by decide
  upper_pos := by decide
  lower {n} requests {cost} run := by
    obtain ⟨initial, final, execution⟩ := run
    exact OPT_le_pointer_cost initial requests execution
  upper {n} requests := by
    obtain ⟨initial, final, cost, execution, bound⟩ := exists_pointer_of_OPT requests
    exact ⟨cost, ⟨initial, final, execution⟩, bound⟩

/-- A hull execution already supplies a root-serving execution, with at
most twelve rotations per touched key and one unit per request. -/
theorem OPT_le_hull_cost {n cost : Nat} (initial : BST 0 n)
    {final : RawTree Nat} (requests : List (Fin n))
    (execution : AccessExecution initial.toRaw (requests.map Fin.val) final cost) :
    OPT requests ≤ 13 * cost := by
  obtain ⟨rotations, bound, trace⟩ := execution.marked_trace initial.toRaw_ordered
  obtain ⟨last, kept, offline, keptBound⟩ := marked_to_offline trace initial rfl requests rfl
  have minimum := OPT_le_execution offline
  have length := execution.length_le_cost
  simp only [List.length_map] at length
  omega

/-- Normalization preserves the initial tree and spends at most one
touched node per retained rotation or request. -/
theorem hull_of_offline {n rotations : Nat} {requests : List (Fin n)}
    {initial final : BST 0 n} (execution : OfflineExecution requests initial final rotations) :
    ∃ (last : BST 0 n) (cost : Nat),
      AccessExecution initial.toRaw (requests.map Fin.val) last.toRaw cost ∧
        cost ≤ requests.length + rotations := by
  obtain ⟨last, kept, support, connected, keptBound, supportBound⟩ :=
    Splay.Accounting.OfflineConnectedSupport.exists_connectedReordered execution
  exact ⟨last, support, connected_hull connected, by omega⟩

def hullComparison : CostComparison hull where
  lowerFactor := 13
  upperFactor := 1
  lower_pos := by decide
  upper_pos := by decide
  lower {n} requests {cost} run := by
    obtain ⟨initial, final, execution⟩ := run
    exact OPT_le_hull_cost initial requests execution
  upper {n} requests := by
    obtain ⟨initial, final, rotations, execution, optimal⟩ := OPT_attained requests
    obtain ⟨last, cost, hull, bound⟩ := hull_of_offline execution
    exact ⟨cost, ⟨initial, last.toRaw, hull⟩, by omega⟩

end ModelCosts
end DynamicOptimality
