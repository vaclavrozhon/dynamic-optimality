import Splay.Analysis.HeightFactor
import Splay.Assumptions.NormalForm
import Splay.Conditional

namespace Splay.Assumptions.NormalForm

/--
A choice of the universal normal-form constants and one certified trace for
every nonempty instance.
-/
structure Realization (model : CostModel) where
  bounds : Bounds
  trace :
    ∀ (n : ℕ), 0 < n →
      ∀ accesses : List (Fin n), ComparisonTrace n accesses
  isNormal :
    ∀ (n : ℕ), ∀ hN : 0 < n, ∀ accesses : List (Fin n),
      IsNormal bounds (trace n hN accesses)
  cost_le :
    ∀ (n : ℕ), ∀ hN : 0 < n, ∀ accesses : List (Fin n),
      (trace n hN accesses).cost ≤
        bounds.costMultiplier * model.optCost accesses

/-- Choice turns the existential normal-form hypothesis into reusable data. -/
noncomputable def Hypothesis.realize {model : CostModel}
    (hypothesis : Hypothesis model) : Realization model := by
  classical
  let bounds := Classical.choose hypothesis
  have hBounds := Classical.choose_spec hypothesis
  exact
    { bounds
      trace := fun n hN accesses =>
        Classical.choose (hBounds n hN accesses)
      isNormal := fun n hN accesses =>
        (Classical.choose_spec (hBounds n hN accesses)).1
      cost_le := fun n hN accesses =>
        (Classical.choose_spec (hBounds n hN accesses)).2 }

/--
The numerical profile exported by a realized normal-form trace.

For `n = 0` its cost is set to zero; all competitiveness statements quantify
over `0 < n`. The height component is the certified uniform upper bound.
-/
def Realization.comparisonProfile {model : CostModel}
    (realization : Realization model) : ComparisonProfile where
  cost := fun {n} accesses =>
    if hN : 0 < n then
      (realization.trace n hN accesses).cost
    else
      0
  maxHeight := fun {n} _ =>
    realization.bounds.heightMultiplier * Analysis.stabilizedLog n

/-- The chosen trace cost satisfies the numerical normal-form layer. -/
theorem Realization.hasNormalFormBound {model : CostModel}
    (realization : Realization model) :
    HasNormalFormBound model realization.comparisonProfile := by
  refine
    ⟨realization.bounds.costMultiplier,
      realization.bounds.costMultiplier_pos, ?_⟩
  intro n hN accesses
  simp only [Realization.comparisonProfile, dif_pos hN]
  calc
    (realization.trace n hN accesses).cost ≤
        realization.bounds.costMultiplier * model.optCost accesses :=
      realization.cost_le n hN accesses
    _ ≤ realization.bounds.costMultiplier *
          (model.optCost accesses + n) :=
      Nat.mul_le_mul_left _ (Nat.le_add_right _ _)

/-- Every chosen state has height below the profile's exported bound. -/
theorem Realization.trace_height_le_profile {model : CostModel}
    (realization : Realization model)
    {n : ℕ} (hN : 0 < n) (accesses : List (Fin n))
    (time : Fin ((realization.trace n hN accesses).rotationCount + 1)) :
    ((realization.trace n hN accesses).state time).height ≤
      realization.comparisonProfile.maxHeight accesses := by
  exact (realization.isNormal n hN accesses).height_le time

/--
The exact height-factor theorem discharges the third conditional layer for
every normal-form realization.
-/
theorem Realization.hasHeightFactorBound {model : CostModel}
    (realization : Realization model) :
    HasHeightFactorBound realization.comparisonProfile := by
  refine
    ⟨Analysis.heightFactorConstant realization.bounds.heightMultiplier,
      ?_, ?_⟩
  · unfold Analysis.heightFactorConstant
    positivity
  · intro n _ accesses
    exact Analysis.heightFactor_le_targetFactor
      realization.bounds.heightMultiplier n
      (realization.bounds.heightMultiplier * Analysis.stabilizedLog n)
      le_rfl

/--
Consequently, after assuming normal form, only the core combinatorial bound
remains to prove in order to obtain the exact main theorem.
-/
theorem targetBound_of_normalForm_and_core
    (model : CostModel) (realization : Realization model)
    (hCore :
      HasCoreAnalysisBound model realization.comparisonProfile) :
    TargetBound model :=
  targetBound_of_conditional_layers model realization.comparisonProfile
    realization.hasNormalFormBound hCore realization.hasHeightFactorBound

end Splay.Assumptions.NormalForm
