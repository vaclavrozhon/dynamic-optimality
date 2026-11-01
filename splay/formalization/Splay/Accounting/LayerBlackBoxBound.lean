import Splay.Accounting.ConcreteBlackBoxBound
import Splay.Analysis.CoefficientEnvelope
import Splay.Analysis.LayerEnvelope

namespace Splay

/-- Unconditional splay bound with the stronger, cap-independent recurrence.
The provider can be replaced without changing the splay transfer theorem. -/
theorem concreteLayerBlackBoxBound :
    FactorBound Accounting.OfflineOptimum.concreteOfflineCostModel
      (fun n => Analysis.coefficientFactor (Interface.LayerCoefficients.coefficients Accounting.articleShape)
        (Accounting.ConstructedPolylogNormalForm.interfaceGapCap n)) :=
  concreteBound_of_activityCoefficients _
    (Interface.LayerCoefficients.valid Accounting.articleShape rfl rfl rfl)

/-- The improved `G log G E(G)` bound for standard splay and the attained
offline optimum. The gap cap is logarithmic in the polylogarithmic comparison
height; `E_le_iterated_log_exponential` controls the remaining loss. -/
theorem concreteEGBound :
    FactorBound Accounting.OfflineOptimum.concreteOfflineCostModel
      (fun n =>
        let G := Accounting.ConstructedPolylogNormalForm.interfaceGapCap n
        G * (Nat.clog 2 G + 1) * Analysis.LayerEnvelope.E G) := by
  obtain ⟨constant, positive, bound⟩ := concreteLayerBlackBoxBound
  refine ⟨16 * constant, by positivity, ?_⟩
  intro n nPositive tree accesses
  let G := Accounting.ConstructedPolylogNormalForm.interfaceGapCap n
  have gapPositive : 0 < G :=
    lt_of_lt_of_le (by decide : 0 < 2)
      (Accounting.ConstructedPolylogNormalForm.interfaceGapCap_ge_two n)
  have coefficients := Analysis.LayerEnvelope.coefficients_le Accounting.articleShape (by decide) G
  have factor := Analysis.coefficientFactor_le_envelope
    (Interface.LayerCoefficients.coefficients Accounting.articleShape) G
    (Analysis.LayerEnvelope.envelope (Analysis.LayerEnvelope.depth G)) gapPositive
    (Analysis.LayerEnvelope.envelope_pos _) coefficients.1 coefficients.2
  have paid := bound n nPositive tree accesses
  change Accounting.concreteSplayCost tree accesses ≤
    constant * (Accounting.OfflineOptimum.offlineOptCost accesses + n) *
      Analysis.coefficientFactor (Interface.LayerCoefficients.coefficients Accounting.articleShape) G at paid
  calc
    _ ≤ _ := paid
    _ ≤ constant * (Accounting.OfflineOptimum.offlineOptCost accesses + n) *
        (16 * G * Analysis.LayerEnvelope.envelope (Analysis.LayerEnvelope.depth G) ^ 2 *
          (Nat.clog 2 G + 1)) := Nat.mul_le_mul_left _ factor
    _ = _ := by
      change _ = (16 * constant) *
        (Accounting.OfflineOptimum.offlineOptCost accesses + n) *
        (G * (Nat.clog 2 G + 1) * Analysis.LayerEnvelope.E G)
      unfold Analysis.LayerEnvelope.E
      ring

end Splay
