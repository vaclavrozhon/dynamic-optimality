import Splay.Analysis.PolylogHeightFactor
import Splay.Conditional

namespace Splay

theorem ComparisonProfile.hasHeightFactorBound_of_polylog
    (comparison : ComparisonProfile) (multiplier exponent : ℕ)
    (height : ∀ (n : ℕ), 0 < n → ∀ accesses : List (Fin n),
      comparison.maxHeight accesses ≤ multiplier * (Analysis.stabilizedLog n) ^ exponent) :
    HasHeightFactorBound comparison := by
  refine ⟨Analysis.polylogHeightFactorConstant multiplier exponent, ?_, ?_⟩
  · unfold Analysis.polylogHeightFactorConstant
    positivity
  · intro n positive accesses
    exact Analysis.heightFactor_le_targetFactor_of_polylog multiplier exponent n _ (height n positive accesses)

/-- The exact original target follows from any fixed polylogarithmic
comparison height. Only the final universal constant changes. -/
theorem targetBound_of_polylog_comparison
    (model : CostModel) (comparison : ComparisonProfile) (multiplier exponent : ℕ)
    (normal : HasNormalFormBound model comparison) (core : HasCoreAnalysisBound model comparison)
    (height : ∀ (n : ℕ), 0 < n → ∀ accesses : List (Fin n),
      comparison.maxHeight accesses ≤ multiplier * (Analysis.stabilizedLog n) ^ exponent) :
    TargetBound model :=
  targetBound_of_conditional_layers model comparison normal core
    (comparison.hasHeightFactorBound_of_polylog multiplier exponent height)

end Splay
