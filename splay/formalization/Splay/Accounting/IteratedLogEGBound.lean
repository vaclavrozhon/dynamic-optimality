import Splay.Accounting.LayerBlackBoxBound

namespace Splay.Analysis

/-- The improved factor in the universe size. The stabilized iterated logs
remain positive at small sizes. The factor `24` covers comparison height. -/
def egTargetFactor (n : ℕ) : ℕ :=
  iteratedLog 2 n * iteratedLog 3 n * LayerEnvelope.E (24 * iteratedLog 2 n)

end Splay.Analysis

namespace Splay.Accounting.ConstructedPolylogNormalForm

theorem interfaceGapCap_le_iteratedLog (n : ℕ) :
    interfaceGapCap n ≤ 24 * Analysis.iteratedLog 2 n := by
  let L := Analysis.iteratedLog 2 n
  have positive : 0 < L := Analysis.stabilizedLog_pos _
  have base : Analysis.stabilizedLog n ≤ 2 ^ L :=
    (le_max_right 2 _).trans (Nat.le_pow_clog (by decide) _)
  have cube := Nat.pow_le_pow_left base 3
  have powerPositive : 1 ≤ (2 ^ L) ^ 3 := by
    have : 0 < (2 ^ L : ℕ) ^ 3 := by positivity
    omega
  have capped : 108000 * Analysis.stabilizedLog n ^ 3 + 2 ≤ 2 ^ (17 + 3 * L) := by
    rw [pow_add, show 3 * L = L * 3 by omega, pow_mul]
    norm_num
    nlinarith only [cube, powerPositive]
  have logarithm := Nat.clog_le_of_le_pow capped
  change 1 + Nat.clog 2 (2 * (54000 * Analysis.stabilizedLog n ^ 3) + 1 + 1) ≤ 24 * L
  have argument : 2 * (54000 * Analysis.stabilizedLog n ^ 3) + 1 + 1 =
      108000 * Analysis.stabilizedLog n ^ 3 + 2 := by ring
  rw [argument]
  omega

theorem gapFactor_le_egTargetFactor (n : ℕ) :
    interfaceGapCap n * (Nat.clog 2 (interfaceGapCap n) + 1) *
      Analysis.LayerEnvelope.E (interfaceGapCap n) ≤ 168 * Analysis.egTargetFactor n := by
  let L := Analysis.iteratedLog 2 n
  let T := Analysis.iteratedLog 3 n
  have Tpositive : 0 < T := Analysis.stabilizedLog_pos _
  have gap := interfaceGapCap_le_iteratedLog n
  have base : L ≤ 2 ^ T :=
    (le_max_right 2 _).trans (Nat.le_pow_clog (by decide) _)
  have power : interfaceGapCap n ≤ 2 ^ (5 + T) := by
    rw [pow_add]
    calc
      _ ≤ 24 * L := gap
      _ ≤ 32 * 2 ^ T := Nat.mul_le_mul (by decide) base
      _ = _ := by norm_num
  have logarithm := Nat.clog_le_of_le_pow power
  have logBound : Nat.clog 2 (interfaceGapCap n) + 1 ≤ 7 * T := by omega
  have loss := Analysis.LayerEnvelope.E_mono gap
  calc
    _ ≤ (24 * L) * (7 * T) * Analysis.LayerEnvelope.E (24 * L) :=
      Nat.mul_le_mul (Nat.mul_le_mul gap logBound) loss
    _ = _ := by unfold Analysis.egTargetFactor; change _ = 168 * (L * T * Analysis.LayerEnvelope.E (24 * L)); ring

end Splay.Accounting.ConstructedPolylogNormalForm

namespace Splay

/-- The improved competitiveness theorem expressed using iterated logs of
the universe size, with no interface or execution hypotheses. -/
theorem concreteIteratedLogEGBound :
    FactorBound Accounting.OfflineOptimum.concreteOfflineCostModel Analysis.egTargetFactor := by
  obtain ⟨C, positive, bound⟩ := concreteEGBound
  refine ⟨168 * C, by positivity, ?_⟩
  intro n nPositive tree accesses
  have factor := Accounting.ConstructedPolylogNormalForm.gapFactor_le_egTargetFactor n
  calc
    _ ≤ _ := bound n nPositive tree accesses
    _ ≤ C * (Accounting.OfflineOptimum.offlineOptCost accesses + n) *
        (168 * Analysis.egTargetFactor n) := Nat.mul_le_mul_left _ factor
    _ = _ := by
      change _ = (168 * C) * (Accounting.OfflineOptimum.offlineOptCost accesses + n) *
        Analysis.egTargetFactor n
      ring

end Splay
