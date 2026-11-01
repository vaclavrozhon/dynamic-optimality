import Splay.Interface.Potential

namespace Splay.Interface

/--
The abstract activity hypothesis plus the verified value potential expresses
activity using only inserts, increases, and the corrected initial potential.
-/
theorem activity_le_inserts_and_increases
    {n : ℕ} {params : Parameters}
    (activityBound : ActivityBound params.toShape)
    {initial final : State n} {operations : List (Operation n)}
    (initialState : initial.Initial params)
    (trace : Trace params initial operations final) :
    ∃ insertConstant valueChangeConstant : ℕ,
      0 < insertConstant ∧
        0 < valueChangeConstant ∧
        totalActivity operations ≤
          insertConstant * params.valueBound * totalInserts operations +
            valueChangeConstant * Nat.clog 2 params.valueBound *
              (2 * totalIncreases operations +
                (2 * n + 1) * params.valueBound) := by
  obtain
    ⟨insertConstant, valueChangeConstant, hInsertConstant,
      hValueConstant, hActivity⟩ := activityBound
  refine
    ⟨insertConstant, valueChangeConstant, hInsertConstant,
      hValueConstant, ?_⟩
  calc
    totalActivity operations ≤
        insertConstant * params.valueBound * totalInserts operations +
            valueChangeConstant * Nat.clog 2 params.valueBound *
              totalValueChanges operations :=
      hActivity params rfl initialState trace
    _ ≤ insertConstant * params.valueBound * totalInserts operations +
          valueChangeConstant * Nat.clog 2 params.valueBound *
            (2 * totalIncreases operations +
              (2 * n + 1) * params.valueBound) := by
      exact Nat.add_le_add_left
        (Nat.mul_le_mul_left _
          (trace.totalValueChanges_le initialState.1)) _

end Splay.Interface
