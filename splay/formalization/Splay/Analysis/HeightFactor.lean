import Splay.Analysis.IteratedLog
import Mathlib.Tactic

namespace Splay.Analysis

/--
An explicit constant for converting a comparison-tree height bounded by
`heightMultiplier * stabilizedLog n` into the theorem's iterated-log factor.
-/
def heightFactorConstant (heightMultiplier : ℕ) : ℕ :=
  let firstScale := Nat.clog 2 (heightMultiplier + 2) + 2
  let secondScale := Nat.clog 2 firstScale + 1
  firstScale * secondScale ^ 2

/--
The exact small-input-safe conversion omitted by the asymptotic manuscript:
a logarithmic comparison-tree height yields the target
`log log n * (log log log n)^2` factor, up to a constant depending only on
the height multiplier.
-/
theorem heightFactor_le_targetFactor
    (heightMultiplier n height : ℕ)
    (hHeight : height ≤ heightMultiplier * stabilizedLog n) :
    heightFactor height ≤
      heightFactorConstant heightMultiplier * targetFactor n := by
  let firstLog := stabilizedLog n
  let secondLog := stabilizedLog firstLog
  let thirdLog := stabilizedLog secondLog
  let multiplierLog := Nat.clog 2 (heightMultiplier + 2)
  let firstScale := multiplierLog + 2
  let secondScale := Nat.clog 2 firstScale + 1

  have hFirstLogPos : 0 < firstLog := stabilizedLog_pos n
  have hSecondLogPos : 0 < secondLog := stabilizedLog_pos firstLog
  have hThirdLogPos : 0 < thirdLog := stabilizedLog_pos secondLog

  have hMultiplierPow :
      heightMultiplier + 2 ≤ 2 ^ multiplierLog := by
    dsimp [multiplierLog]
    exact Nat.le_pow_clog (by omega) _
  have hFirstLogPow :
      max 2 firstLog ≤ 2 ^ secondLog := by
    dsimp [secondLog, stabilizedLog]
    exact Nat.le_pow_clog (by omega) _
  have hHeightArgument :
      height + 2 ≤ (heightMultiplier + 2) * max 2 firstLog := by
    calc
      height + 2 ≤ heightMultiplier * firstLog + 2 :=
        Nat.add_le_add_right hHeight 2
      _ ≤ heightMultiplier * max 2 firstLog + 2 * max 2 firstLog := by
        apply Nat.add_le_add
        · exact Nat.mul_le_mul_left _ (Nat.le_max_right _ _)
        · nlinarith [Nat.le_max_left 2 firstLog]
      _ = (heightMultiplier + 2) * max 2 firstLog := by ring
  have hHeightPow :
      height + 2 ≤ 2 ^ (multiplierLog + secondLog) := by
    calc
      height + 2 ≤ (heightMultiplier + 2) * max 2 firstLog :=
        hHeightArgument
      _ ≤ 2 ^ multiplierLog * 2 ^ secondLog :=
        Nat.mul_le_mul hMultiplierPow hFirstLogPow
      _ = 2 ^ (multiplierLog + secondLog) := by
        rw [Nat.pow_add]
  have hHeightClog :
      Nat.clog 2 (height + 2) ≤ multiplierLog + secondLog :=
    Nat.clog_le_of_le_pow hHeightPow

  have hContracted :
      contractedGap (height + 1) ≤ firstScale * secondLog := by
    unfold contractedGap gapBucket
    have hArgument : height + 1 + 1 = height + 2 := by omega
    rw [hArgument]
    dsimp [firstScale]
    nlinarith

  have hFirstScaleTwo : 2 ≤ firstScale := by
    dsimp [firstScale]
    omega
  have hFirstScalePow :
      firstScale ≤ 2 ^ Nat.clog 2 firstScale :=
    Nat.le_pow_clog (by omega) _
  have hSecondLogPow :
      max 2 secondLog ≤ 2 ^ thirdLog := by
    dsimp [thirdLog, stabilizedLog]
    exact Nat.le_pow_clog (by omega) _
  have hContractedMax :
      max 2 (contractedGap (height + 1)) ≤
        firstScale * max 2 secondLog := by
    apply max_le
    · nlinarith [Nat.le_max_left 2 secondLog]
    · exact hContracted.trans
        (Nat.mul_le_mul_left _ (Nat.le_max_right _ _))
  have hContractedPow :
      max 2 (contractedGap (height + 1)) ≤
        2 ^ (Nat.clog 2 firstScale + thirdLog) := by
    calc
      max 2 (contractedGap (height + 1)) ≤
          firstScale * max 2 secondLog :=
        hContractedMax
      _ ≤ 2 ^ Nat.clog 2 firstScale * 2 ^ thirdLog :=
        Nat.mul_le_mul hFirstScalePow hSecondLogPow
      _ = 2 ^ (Nat.clog 2 firstScale + thirdLog) := by
        rw [Nat.pow_add]
  have hContractedLogRaw :
      Nat.clog 2 (max 2 (contractedGap (height + 1))) ≤
        Nat.clog 2 firstScale + thirdLog :=
    Nat.clog_le_of_le_pow hContractedPow
  have hContractedLog :
      stabilizedLog (contractedGap (height + 1)) ≤
        secondScale * thirdLog := by
    unfold stabilizedLog
    dsimp [secondScale]
    nlinarith

  calc
    heightFactor height =
        contractedGap (height + 1) *
          stabilizedLog (contractedGap (height + 1)) ^ 2 := rfl
    _ ≤ (firstScale * secondLog) * (secondScale * thirdLog) ^ 2 :=
      Nat.mul_le_mul hContracted (Nat.pow_le_pow_left hContractedLog 2)
    _ = (firstScale * secondScale ^ 2) *
          (secondLog * thirdLog ^ 2) := by ring
    _ = heightFactorConstant heightMultiplier * targetFactor n := by
      simp only [heightFactorConstant, targetFactor, iteratedLog]
      simp only [firstScale, secondScale, multiplierLog, firstLog, secondLog,
        thirdLog]

end Splay.Analysis
