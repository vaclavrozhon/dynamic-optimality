import BinaryMemorylessPotential
import SharperDyadicCompressionRecursion

/-! Fully explicit finite dyadic recursion. Every compressed trace starts
with all global values one, so its terminal cap-two coefficient pair is
(0,5), not the arbitrary-initialization pair (4,5). -/

namespace Splay.Research.BinarySeededCompressionRecursion
open Splay.Interface
open SharperDyadicCompressionRecursion

/-- A coefficient assertion at one specified cap. -/
def BoundAt (shape : Shape) (G : ℕ) (pair : ℕ × ℕ) : Prop :=
  ∀ (params : Parameters), params.toShape = shape → params.valueBound = G →
    ∀ {n : ℕ} {initial final : State n} {operations : List (Operation n)},
      initial.Initial params → Trace params initial operations final →
      totalActivity operations ≤ pair.1 * totalInserts operations +
        pair.2 * totalValueChanges operations

/-- The initialized subclass produced by every historical numeric compiler. -/
def AllOnesBoundAt (shape : Shape) (G : ℕ) (pair : ℕ × ℕ) : Prop :=
  ∀ (params : Parameters), params.toShape = shape → params.valueBound = G →
    ∀ {n : ℕ} {initial final : State n} {operations : List (Operation n)},
      initial.Initial params → (∀ x, initial.value x = 1) →
      Trace params initial operations final →
      totalActivity operations ≤ pair.1 * totalInserts operations +
        pair.2 * totalValueChanges operations

/-- One strict cap-decreasing transfer needs only an all-ones inner bound. -/
theorem transfer_at (shape : Shape) (G a b : ℕ)
    (inner : AllOnesBoundAt shape (SharperDyadicCompressionRowBudget.cap G) (a,b)) :
    BoundAt shape G
      (insertionCoefficient a b (SharperDyadicCompressionRowBudget.cap G),
       variationCoefficient shape b (SharperDyadicCompressionRowBudget.cap G)) := by
  intro params sameShape sameCap n initial final operations initialState original
  apply numerical_transfer shape a b (SharperDyadicCompressionRowBudget.cap G)
    (totalActivity operations) (totalInserts operations) (totalValueChanges operations)
  intro k
  let cutoffValue := ArbitrarySourceTail.threshold params k
  obtain ⟨finalLabels,finalLedger,finalClock,finalEvents,snapshots,liftedOperations,
      timed,newInitial,lifted,activity,growth,inserts,variation⟩ :=
    SharperDyadicCompressionRealization.from_initial_trace initialState original cutoffValue
  refine ⟨totalValueChanges liftedOperations,
    ActualCompressionRowBudget.lateCount cutoffValue snapshots, ?_, ?_, ?_⟩
  · have newShape : (SharperDyadicCompressionRealization.parameters params).toShape = shape :=
      sameShape
    have newCap : (SharperDyadicCompressionRealization.parameters params).valueBound =
        SharperDyadicCompressionRowBudget.cap G := by
      simp only [SharperDyadicCompressionRealization.parameters, sameCap]
    have allOnes : ∀ x,
        (CappedHistoricalNumericStepLift.state
          (SharperDyadicCompressionRowBudget.label params.valueBound)
          initial EpisodeLedger.empty).value x = 1 := by
      intro x
      rfl
    have bound := inner _ newShape newCap newInitial allOnes lifted
    rw [activity,inserts] at bound
    exact bound
  · have originalShape : params.growingLimit = shape.growingLimit ∧
        params.exemptPasses = shape.exemptPasses ∧
        params.matchingDenominator = shape.matchingDenominator := by
      exact ⟨congrArg Shape.growingLimit sameShape,
        congrArg Shape.exemptPasses sameShape,
        congrArg Shape.matchingDenominator sameShape⟩
    dsimp [cutoffValue, ArbitrarySourceTail.threshold] at variation
    rw [originalShape.1,originalShape.2.1,originalShape.2.2,sameCap] at variation
    simpa [cutoffValue, ArbitrarySourceTail.threshold, originalShape.2.1,
      originalShape.2.2, DyadicCompressionRowBudget.lateCount,
      ActualCompressionRowBudget.lateCount] using variation
  · exact HistoricalCompressionTail.timed_tail_bound initialState timed k

/-- Finite, entirely numerical recurrence terminating at exact binary cap. -/
def coefficients (shape : Shape) (G : ℕ) : ℕ × ℕ :=
  if _small : G ≤ 2 then (0,5)
  else
    let R := SharperDyadicCompressionRowBudget.cap G
    let inner := coefficients shape R
    (insertionCoefficient inner.1 inner.2 R,
      variationCoefficient shape inner.2 R)
termination_by G
decreasing_by
  exact SharperDyadicCompressionRowBudget.cap_lt_of_two_lt (by omega)

theorem coefficients_of_large (shape : Shape) (G : ℕ) (large : 2 < G) :
    coefficients shape G =
      (insertionCoefficient (coefficients shape (SharperDyadicCompressionRowBudget.cap G)).1
        (coefficients shape (SharperDyadicCompressionRowBudget.cap G)).2
        (SharperDyadicCompressionRowBudget.cap G),
       variationCoefficient shape (coefficients shape (SharperDyadicCompressionRowBudget.cap G)).2
        (SharperDyadicCompressionRowBudget.cap G)) := by
  rw [coefficients]
  simp only [show ¬G ≤ 2 by omega, dite_false]

/-- Every cap uses the exact all-ones binary seed after finitely many lifts. -/
theorem coefficients_all_ones (shape : Shape)
    (exempt : shape.exemptPasses = 2)
    (numerator : shape.matchingNumerator = 1)
    (denominator : shape.matchingDenominator = 8) :
    ∀ G, AllOnesBoundAt shape G (coefficients shape G) := by
  intro G
  induction G using Nat.strong_induction_on with
  | h G ih =>
    by_cases small : G ≤ 2
    · intro params sameShape sameCap n initial final operations initialState allOnes original
      have binary : params.valueBound = 2 := by
        have lower := params.valueBound_ge_two
        omega
      have sameExempt : params.exemptPasses = 2 := by
        have equality := congrArg Shape.exemptPasses sameShape
        omega
      have sameNumerator : params.matchingNumerator = 1 := by
        have equality := congrArg Shape.matchingNumerator sameShape
        omega
      have sameDenominator : params.matchingDenominator = 8 := by
        have equality := congrArg Shape.matchingDenominator sameShape
        omega
      have binaryBound := BinaryMemorylessPotential.all_ones_bound binary
        sameExempt sameNumerator sameDenominator initialState allOnes original
      simpa [coefficients, small] using binaryBound
    · have smaller : SharperDyadicCompressionRowBudget.cap G < G :=
        SharperDyadicCompressionRowBudget.cap_lt_of_two_lt (by omega)
      have inner := ih (SharperDyadicCompressionRowBudget.cap G) smaller
      have transferred := transfer_at shape G
        (coefficients shape (SharperDyadicCompressionRowBudget.cap G)).1
        (coefficients shape (SharperDyadicCompressionRowBudget.cap G)).2 inner
      intro params sameShape sameCap n initial final operations initialState allOnes original
      rw [coefficients_of_large shape G (by omega)]
      exact transferred params sameShape sameCap initialState original

/-- Original arbitrary initialization needs its own cap-two insertion term. -/
def originalCoefficients (shape : Shape) (G : ℕ) : ℕ × ℕ :=
  if G ≤ 2 then (4,5) else coefficients shape G

/-- Fully explicit native bounds for arbitrary initialized traces. No coarse
existential constants remain in the recurrence or its binary seed. -/
theorem original_coefficients_valid (shape : Shape)
    (exempt : shape.exemptPasses = 2)
    (numerator : shape.matchingNumerator = 1)
    (denominator : shape.matchingDenominator = 8) :
    HistoricalCompressionRecursion.CoefficientBound shape (originalCoefficients shape) := by
  intro params sameShape n initial final operations initialState original
  by_cases small : params.valueBound ≤ 2
  · have binary : params.valueBound = 2 := by
      have lower := params.valueBound_ge_two
      omega
    have sameExempt : params.exemptPasses = 2 := by
      have equality := congrArg Shape.exemptPasses sameShape
      omega
    have sameNumerator : params.matchingNumerator = 1 := by
      have equality := congrArg Shape.matchingNumerator sameShape
      omega
    have sameDenominator : params.matchingDenominator = 8 := by
      have equality := congrArg Shape.matchingDenominator sameShape
      omega
    have binaryBound := BinaryMemorylessPotential.from_initial_trace
      (price := 5) (by omega) (by omega) binary sameExempt sameNumerator
      sameDenominator initialState original
    simpa [originalCoefficients, small] using binaryBound
  · have inner := coefficients_all_ones shape exempt numerator denominator
      (SharperDyadicCompressionRowBudget.cap params.valueBound)
    have transferred := transfer_at shape params.valueBound
      (coefficients shape (SharperDyadicCompressionRowBudget.cap params.valueBound)).1
      (coefficients shape (SharperDyadicCompressionRowBudget.cap params.valueBound)).2 inner
    simp only [originalCoefficients, if_neg small]
    rw [coefficients_of_large shape params.valueBound (by omega)]
    exact transferred params sameShape rfl initialState original

#print axioms transfer_at
#print axioms coefficients_all_ones
#print axioms original_coefficients_valid
end Splay.Research.BinarySeededCompressionRecursion
