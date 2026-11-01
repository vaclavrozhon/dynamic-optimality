import Splay.Interface.Model
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Lean.Elab.Tactic.Omega

namespace Splay.Interface

namespace State

/-- Sum of all element values, including elements not currently in a block. -/
def totalValue {n : ℕ} (state : State n) : ℕ :=
  ∑ element : Element n, state.value element

/-- Replacing one value preserves the sum after adding back the old value. -/
theorem totalValue_update {n : ℕ} (state : State n)
    (element : Element n) (newValue : ℕ) :
    (∑ candidate : Element n,
        Function.update state.value element newValue candidate) +
        state.value element =
      state.totalValue + newValue := by
  have hMember : element ∈ (Finset.univ : Finset (Element n)) :=
    Finset.mem_univ element
  have hNew :=
    Finset.sum_update_of_mem hMember state.value newValue
  have hOld :=
    Finset.sum_update_of_mem hMember state.value (state.value element)
  simp only [Function.update_eq_self] at hOld
  unfold totalValue
  rw [hNew, hOld]
  omega

/-- A valid state's total value is bounded by the corrected `2n+1` count. -/
theorem totalValue_le {n : ℕ} {state : State n} {params : Parameters}
    (valid : state.Valid params) :
    state.totalValue ≤ (2 * n + 1) * params.valueBound := by
  unfold totalValue
  calc
    (∑ element : Element n, state.value element) ≤
        ∑ _element : Element n, params.valueBound := by
      apply Finset.sum_le_sum
      intro element _
      exact (valid.2.1 element).2
    _ = (2 * n + 1) * params.valueBound := by
      simp [Fintype.card_fin]

end State

namespace Operation

/-- Indicator for an increasing `ValueChange`. -/
def increaseCount {n : ℕ} : Operation n → ℕ
  | .valueChange _ .increase => 1
  | _ => 0

/-- Indicator for a decreasing `ValueChange`. -/
def decreaseCount {n : ℕ} : Operation n → ℕ
  | .valueChange _ .decrease => 1
  | _ => 0

end Operation

/-- Number of increasing unit value changes in an operation sequence. -/
def totalIncreases {n : ℕ} (operations : List (Operation n)) : ℕ :=
  (operations.map Operation.increaseCount).sum

/-- Number of decreasing unit value changes in an operation sequence. -/
def totalDecreases {n : ℕ} (operations : List (Operation n)) : ℕ :=
  (operations.map Operation.decreaseCount).sum

/-- Every value change is exactly one increase or one decrease. -/
theorem totalValueChanges_eq {n : ℕ} (operations : List (Operation n)) :
    totalValueChanges operations =
      totalIncreases operations + totalDecreases operations := by
  induction operations with
  | nil =>
      simp [totalValueChanges, totalIncreases, totalDecreases]
  | cons operation operations ih =>
      simp only [totalValueChanges, totalIncreases, totalDecreases,
        List.map_cons, List.sum_cons] at ih ⊢
      cases operation with
      | convert =>
          simpa [Operation.valueChangeCount, Operation.increaseCount,
            Operation.decreaseCount] using ih
      | create =>
          simpa [Operation.valueChangeCount, Operation.increaseCount,
            Operation.decreaseCount] using ih
      | insert =>
          simpa [Operation.valueChangeCount, Operation.increaseCount,
            Operation.decreaseCount] using ih
      | delete =>
          simpa [Operation.valueChangeCount, Operation.increaseCount,
            Operation.decreaseCount] using ih
      | pass =>
          simpa [Operation.valueChangeCount, Operation.increaseCount,
            Operation.decreaseCount] using ih
      | split =>
          simpa [Operation.valueChangeCount, Operation.increaseCount,
            Operation.decreaseCount] using ih
      | valueChange element delta =>
          cases delta <;>
            simp only [Operation.valueChangeCount, Operation.increaseCount,
              Operation.decreaseCount] <;>
            omega

/-- One exact operation preserves the value-sum balance. -/
theorem Effect.totalValue_balance {n : ℕ} {params : Parameters}
    {before after : State n} {operation : Operation n}
    (effect : Effect params before operation after) :
    after.totalValue + operation.decreaseCount =
      before.totalValue + operation.increaseCount := by
  cases effect with
  | convert found growing blocks_eq values_eq =>
      simp [State.totalValue, Operation.decreaseCount,
        Operation.increaseCount, values_eq]
  | create room blocks_eq values_eq =>
      simp [State.totalValue, Operation.decreaseCount,
        Operation.increaseCount, values_eq]
  | insert found growing unassigned value_order blocks_eq values_eq =>
      simp [State.totalValue, Operation.decreaseCount,
        Operation.increaseCount, values_eq]
  | delete found shrinking present blocks_eq values_eq =>
      simp [State.totalValue, Operation.decreaseCount,
        Operation.increaseCount, values_eq]
  | pass found valid_matching blocks_eq values_eq =>
      simp [State.totalValue, Operation.decreaseCount,
        Operation.increaseCount, values_eq]
  | split found shrinking prefix_le blocks_eq values_eq =>
      simp [State.totalValue, Operation.decreaseCount,
        Operation.increaseCount, values_eq]
  | decrease can_decrease blocks_eq values_eq =>
      rename_i element
      have hUpdate :=
        State.totalValue_update before element (before.value element - 1)
      unfold State.totalValue at hUpdate ⊢
      rw [values_eq]
      simp only [Operation.decreaseCount, Operation.increaseCount, add_zero]
      omega
  | increase can_increase blocks_eq values_eq =>
      rename_i element
      have hUpdate :=
        State.totalValue_update before element (before.value element + 1)
      unfold State.totalValue at hUpdate ⊢
      rw [values_eq]
      simp only [Operation.decreaseCount, Operation.increaseCount, add_zero]
      omega

/-- The value-sum balance telescopes over a complete trace. -/
theorem Trace.totalValue_balance {n : ℕ} {params : Parameters}
    {initial final : State n} {operations : List (Operation n)}
    (trace : Trace params initial operations final) :
    final.totalValue + totalDecreases operations =
      initial.totalValue + totalIncreases operations := by
  induction trace with
  | nil valid =>
      simp [totalDecreases, totalIncreases]
  | @cons before middle final operation operations head tail ih =>
      have hHead := head.2.1.totalValue_balance
      simp only [totalDecreases, totalIncreases] at ih
      simp only [totalDecreases, totalIncreases, List.map_cons, List.sum_cons]
      calc
        final.totalValue +
            (operation.decreaseCount +
              (List.map Operation.decreaseCount operations).sum) =
            (final.totalValue +
              (List.map Operation.decreaseCount operations).sum) +
                operation.decreaseCount := by omega
        _ = (middle.totalValue +
              (List.map Operation.increaseCount operations).sum) +
                operation.decreaseCount := by rw [ih]
        _ = (middle.totalValue + operation.decreaseCount) +
              (List.map Operation.increaseCount operations).sum := by omega
        _ = (before.totalValue + operation.increaseCount) +
              (List.map Operation.increaseCount operations).sum := by
            rw [hHead]
        _ = before.totalValue +
            (operation.increaseCount +
              (List.map Operation.increaseCount operations).sum) := by omega

/--
Exact `lemma:bounding-decreases`, with the initial `2n+1` external elements
instead of the manuscript's erroneous `n`.
-/
theorem Trace.totalDecreases_le {n : ℕ} {params : Parameters}
    {initial final : State n} {operations : List (Operation n)}
    (initialValid : initial.Valid params)
    (trace : Trace params initial operations final) :
    totalDecreases operations ≤
      totalIncreases operations + (2 * n + 1) * params.valueBound := by
  have hBalance := trace.totalValue_balance
  have hInitial := State.totalValue_le initialValid
  omega

/-- Total value changes are controlled by increases and initial potential. -/
theorem Trace.totalValueChanges_le {n : ℕ} {params : Parameters}
    {initial final : State n} {operations : List (Operation n)}
    (initialValid : initial.Valid params)
    (trace : Trace params initial operations final) :
    totalValueChanges operations ≤
      2 * totalIncreases operations +
        (2 * n + 1) * params.valueBound := by
  rw [totalValueChanges_eq]
  have hDecreases := trace.totalDecreases_le initialValid
  omega

end Splay.Interface
