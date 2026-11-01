import Splay.Interface.Model

namespace Splay.Interface

/-- The insertion and unit-variation coefficients, as functions of the value cap.
Both directions of a unit value change contribute to `totalValueChanges`. -/
abbrev ActivityCoefficients := ℕ → ℕ × ℕ

/-- A reusable numerical interface for every initialized execution of a fixed
shape. The coefficients depend on the cap, but not on the population or trace. -/
def CoefficientBound (shape : Shape) (coefficients : ActivityCoefficients) : Prop :=
  ∀ (params : Parameters), params.toShape = shape →
    ∀ {n : ℕ} {initial final : State n} {operations : List (Operation n)},
      initial.Initial params → Trace params initial operations final →
      totalActivity operations ≤
        (coefficients params.valueBound).1 * totalInserts operations +
        (coefficients params.valueBound).2 * totalValueChanges operations

theorem CoefficientBound.mono {shape : Shape} {first second : ActivityCoefficients}
    (bound : CoefficientBound shape first)
    (inserts : ∀ G, (first G).1 ≤ (second G).1)
    (variation : ∀ G, (first G).2 ≤ (second G).2) :
    CoefficientBound shape second := by
  intro params sameShape n initial final operations initialized trace
  exact (bound params sameShape initialized trace).trans
    (Nat.add_le_add (Nat.mul_le_mul_right _ (inserts _))
      (Nat.mul_le_mul_right _ (variation _)))

/-- Select a valid coefficient pair at each cap. The selection is shared by
both coefficients: taking their separate minima is not justified. -/
theorem CoefficientBound.select {ι : Type*} {shape : Shape}
    (coefficients : ι → ActivityCoefficients)
    (bounds : ∀ i, CoefficientBound shape (coefficients i)) (select : ℕ → ι) :
    CoefficientBound shape (fun G => coefficients (select G) G) := by
  intro params sameShape n initial final operations initialized trace
  exact bounds (select params.valueBound) params sameShape initialized trace

end Splay.Interface
