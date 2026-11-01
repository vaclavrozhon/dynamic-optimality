import Splay.Statement
import Mathlib.Tactic

namespace Splay

/--
The numerical information exported by a nearly optimal comparison-tree trace.
Its construction and structural invariants live in the normal-form layer; the
global accounting argument consumes only its cost and maximum height.
-/
structure ComparisonProfile where
  cost : {n : ℕ} → List (Fin n) → ℕ
  maxHeight : {n : ℕ} → List (Fin n) → ℕ

/--
Exact finite replacement for the statement that the normal-form comparison
tree costs only a constant factor more than the optimum.
-/
def HasNormalFormBound (model : CostModel)
    (comparison : ComparisonProfile) : Prop :=
  ∃ constant : ℕ, 0 < constant ∧
    ∀ (n : ℕ), 0 < n → ∀ accesses : List (Fin n),
      comparison.cost accesses ≤
        constant * (model.optCost accesses + n)

/--
The conditional output of the heavy-path, lazy-interval, and pairing
accounting layers, still parameterized by the comparison tree's height.
-/
def HasCoreAnalysisBound (model : CostModel)
    (comparison : ComparisonProfile) : Prop :=
  ∃ constant : ℕ, 0 < constant ∧
    ∀ (n : ℕ), 0 < n →
      ∀ (initial : model.Initial n) (accesses : List (Fin n)),
        model.splayCost initial accesses ≤
          constant * (comparison.cost accesses + n) *
            Analysis.heightFactor (comparison.maxHeight accesses)

/--
The arithmetic bridge from a logarithmic comparison-tree height to the
stabilized iterated-log factor used by `TargetBound`.

This is separate because the manuscript currently states the logarithmic
height and all `O(log log n)` conversions only asymptotically.
-/
def HasHeightFactorBound (comparison : ComparisonProfile) : Prop :=
  ∃ constant : ℕ, 0 < constant ∧
    ∀ (n : ℕ), 0 < n → ∀ accesses : List (Fin n),
      Analysis.heightFactor (comparison.maxHeight accesses) ≤
        constant * Analysis.targetFactor n

/--
The three independently auditable layers compose to the exact target
competitiveness statement.

No combinatorial claim is hidden in this theorem: its proof is only
natural-number monotonicity and reassociation of the three constants.
-/
theorem targetBound_of_conditional_layers
    (model : CostModel) (comparison : ComparisonProfile)
    (hNormalForm : HasNormalFormBound model comparison)
    (hCore : HasCoreAnalysisBound model comparison)
    (hHeight : HasHeightFactorBound comparison) :
    TargetBound model := by
  obtain ⟨normalConstant, hNormalConstant, hNormalForm⟩ := hNormalForm
  obtain ⟨coreConstant, hCoreConstant, hCore⟩ := hCore
  obtain ⟨heightConstant, hHeightConstant, hHeight⟩ := hHeight
  refine
    ⟨coreConstant * (normalConstant + 1) * heightConstant, by positivity, ?_⟩
  intro n hN initial accesses
  have hComparison :=
    hNormalForm n hN accesses
  have hComparisonWithInitial :
      comparison.cost accesses + n ≤
        (normalConstant + 1) * (model.optCost accesses + n) := by
    calc
      comparison.cost accesses + n ≤
          normalConstant * (model.optCost accesses + n) + n :=
        Nat.add_le_add_right hComparison n
      _ ≤ normalConstant * (model.optCost accesses + n) +
          (model.optCost accesses + n) := by omega
      _ = (normalConstant + 1) * (model.optCost accesses + n) := by
        rw [Nat.add_mul, one_mul]
  calc
    model.splayCost initial accesses ≤
        coreConstant * (comparison.cost accesses + n) *
          Analysis.heightFactor (comparison.maxHeight accesses) :=
      hCore n hN initial accesses
    _ ≤ coreConstant *
          ((normalConstant + 1) * (model.optCost accesses + n)) *
          Analysis.heightFactor (comparison.maxHeight accesses) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hComparisonWithInitial)
    _ ≤ coreConstant *
          ((normalConstant + 1) * (model.optCost accesses + n)) *
          (heightConstant * Analysis.targetFactor n) :=
      Nat.mul_le_mul_left _ (hHeight n hN accesses)
    _ = (coreConstant * (normalConstant + 1) * heightConstant) *
          (model.optCost accesses + n) * Analysis.targetFactor n := by
      ring

end Splay
