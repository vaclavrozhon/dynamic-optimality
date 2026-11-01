import Splay.Interface.ActivityCoefficients
import Splay.Interface.LayerCompression
import BinaryMemorylessPotential

namespace Splay.Interface.LayerCoefficients

open Splay.Research LayerCompression

/-- Unlike the older dyadic cutoff, this cutoff does not depend on the cap. -/
def cutoff (b : ℕ) : ℕ := Nat.clog 2 (24 * b + 1)

def insertionCoefficient (a b R : ℕ) : ℕ := 2 * a + 2 * b * (4 * R - 2) + 1

def variationCoefficient (shape : Shape) (b : ℕ) : ℕ :=
  24 * b * shapeConstant shape * (cutoff b + 2)

theorem numerical_transfer (shape : Shape) (a b R A I U K newU : ℕ)
    (activity : A ≤ a * I + b * newU)
    (compression : newU ≤ (4 * R - 2) * I + 6 * K)
    (layers : 2 ^ cutoff b * K ≤
      2 ^ cutoff b * (2 * shapeConstant shape * (cutoff b + 2) * U) + 2 * (A + I)) :
    A ≤ insertionCoefficient a b R * I + variationCoefficient shape b * U := by
  have power : 24 * b ≤ 2 ^ cutoff b := by
    have := Nat.le_pow_clog (by decide : 1 < 2) (24 * b + 1)
    unfold cutoff
    omega
  have positive : 0 < 2 ^ cutoff b := by positivity
  have first := Nat.mul_le_mul_left (2 ^ cutoff b) activity
  have second := Nat.mul_le_mul_left (2 ^ cutoff b * b) compression
  have third := Nat.mul_le_mul_left (6 * b) layers
  have absorbA := Nat.mul_le_mul_right A power
  have absorbI := Nat.mul_le_mul_right I power
  have scaled : 2 ^ cutoff b * A ≤ 2 ^ cutoff b *
      (insertionCoefficient a b R * I + variationCoefficient shape b * U) := by
    unfold insertionCoefficient variationCoefficient
    nlinarith only [first, second, third, absorbA, absorbI]
  exact Nat.le_of_mul_le_mul_left scaled positive

/-- Transfer a valid bound from the smaller cap using a literal compiled
execution and the cap-independent logarithmic-error account. -/
theorem transfer_at (shape : Shape) (G a b : ℕ)
    (inner : ∀ params : Parameters, params.toShape = shape → params.valueBound = cap G →
      ∀ {n : ℕ} {initial final : State n} {operations : List (Operation n)},
        initial.Initial params → Trace params initial operations final →
        totalActivity operations ≤ a * totalInserts operations + b * totalValueChanges operations) :
    ∀ params : Parameters, params.toShape = shape → params.valueBound = G →
      ∀ {n : ℕ} {initial final : State n} {operations : List (Operation n)},
        initial.Initial params → Trace params initial operations final →
        totalActivity operations ≤ insertionCoefficient a b (cap G) * totalInserts operations +
          variationCoefficient shape b * totalValueChanges operations := by
  intro params sameShape sameCap n initial final operations initialized original
  let reduced := SharperDyadicCompressionRealization.parameters params
  obtain ⟨finalLabels, finalLedger, finalClock, finalEvents, rows, liftedOperations,
      history, newInitial, lifted, activity, growth, inserts, variation⟩ :=
    CappedHistoricalNumericTimedLift.from_initial_trace (label params.valueBound)
      initialized original (params := reduced) rfl
      (SharperDyadicCompressionRowBudget.label_positive params.valueBound)
      (SharperDyadicCompressionRowBudget.label_bounded params.valueBound)
      (SharperDyadicCompressionRowBudget.cap_ge_two params.valueBound) (le_refl _)
  have newCap : reduced.valueBound = cap G := by
    simp only [reduced, SharperDyadicCompressionRealization.parameters, sameCap]
  have paid := inner reduced sameShape newCap newInitial lifted
  rw [activity, inserts] at paid
  have compiler := compiler_charge_bound history
  have compression : totalValueChanges liftedOperations ≤
      (4 * cap params.valueBound - 2) * totalInserts operations + 6 * totalCharge rows := by
    nlinarith only [variation, compiler]
  have layers := totalCharge_bound history initialized (cutoff b)
  rw [sameCap] at compression
  rw [sameShape] at layers
  exact numerical_transfer shape a b (cap G) _ _ _ _ _ paid compression layers

/-- Finite explicit recursion with an arbitrary-initialization binary seed.
Only this provider changes when the interface analysis improves again. -/
def coefficients (shape : Shape) (G : ℕ) : ℕ × ℕ :=
  if _small : G ≤ 2 then (4, 5)
  else
    let inner := coefficients shape (cap G)
    (insertionCoefficient inner.1 inner.2 (cap G), variationCoefficient shape inner.2)
termination_by G
decreasing_by exact SharperDyadicCompressionRowBudget.cap_lt_of_two_lt (by omega)

theorem coefficients_of_large (shape : Shape) (G : ℕ) (large : 2 < G) :
    coefficients shape G =
      (insertionCoefficient (coefficients shape (cap G)).1 (coefficients shape (cap G)).2 (cap G),
        variationCoefficient shape (coefficients shape (cap G)).2) := by
  rw [coefficients]
  simp only [show ¬G ≤ 2 by omega, dite_false]

/-- The improved recurrence is valid for actual initialized interface traces.
There are no history-budget or compression-realizability assumptions. -/
theorem valid (shape : Shape)
    (exempt : shape.exemptPasses = 2)
    (numerator : shape.matchingNumerator = 1)
    (denominator : shape.matchingDenominator = 8) :
    CoefficientBound shape (coefficients shape) := by
  have atCap : ∀ G, ∀ params : Parameters, params.toShape = shape → params.valueBound = G →
      ∀ {n : ℕ} {initial final : State n} {operations : List (Operation n)},
        initial.Initial params → Trace params initial operations final →
        totalActivity operations ≤ (coefficients shape G).1 * totalInserts operations +
          (coefficients shape G).2 * totalValueChanges operations := by
    intro G
    induction G using Nat.strong_induction_on with
    | h G ih =>
      by_cases small : G ≤ 2
      · intro params sameShape sameCap n initial final operations initialized original
        have binary : params.valueBound = 2 := by have := params.valueBound_ge_two; omega
        have sameExempt : params.exemptPasses = 2 := by
          have := congrArg Shape.exemptPasses sameShape; omega
        have sameNumerator : params.matchingNumerator = 1 := by
          have := congrArg Shape.matchingNumerator sameShape; omega
        have sameDenominator : params.matchingDenominator = 8 := by
          have := congrArg Shape.matchingDenominator sameShape; omega
        have bound := BinaryMemorylessPotential.from_initial_trace
          (price := 5) (by omega) (by omega) binary sameExempt sameNumerator
          sameDenominator initialized original
        simpa [coefficients, small] using bound
      · have smaller := SharperDyadicCompressionRowBudget.cap_lt_of_two_lt (by omega : 2 < G)
        have transferred := transfer_at shape G
          (coefficients shape (cap G)).1 (coefficients shape (cap G)).2 (ih (cap G) smaller)
        rw [coefficients_of_large shape G (by omega)]
        exact transferred
  intro params sameShape n initial final operations initialized trace
  exact atCap params.valueBound params sameShape rfl initialized trace

end Splay.Interface.LayerCoefficients
