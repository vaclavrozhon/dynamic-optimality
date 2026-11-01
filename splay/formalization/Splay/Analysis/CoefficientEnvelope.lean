import Splay.Analysis.CoefficientFactor
import Mathlib.Tactic

namespace Splay.Analysis

/-- A coefficient envelope with insertion cost `B (log G + 1)` and unit
variation cost `B` yields a splay factor `O(G (log G + 1) B²)`.
Squaring the envelope absorbs its own logarithm without a separate growth
assumption; this preserves the iterated-log exponential class. -/
theorem coefficientFactor_le_envelope (coefficients : Interface.ActivityCoefficients)
    (G B : ℕ) (gapPositive : 0 < G) (envelopePositive : 0 < B)
    (inserts : (coefficients G).1 ≤ B * (Nat.clog 2 G + 1))
    (variation : (coefficients G).2 ≤ B) :
    coefficientFactor coefficients G ≤ 16 * G * B ^ 2 * (Nat.clog 2 G + 1) := by
  have logGap : Nat.clog 2 G ≤ G :=
    Nat.clog_le_of_le_pow (Nat.le_of_lt (Nat.lt_pow_self (by decide : 1 < 2)))
  have logEnvelope : Nat.clog 2 B ≤ B :=
    Nat.clog_le_of_le_pow (Nat.le_of_lt (Nat.lt_pow_self (by decide : 1 < 2)))
  have first := inserts.trans (Nat.mul_le_mul_left B (show Nat.clog 2 G + 1 ≤ 2 * G by omega))
  have second := Nat.mul_le_mul_left G variation
  have one : 1 ≤ G * B := Nat.mul_pos gapPositive envelopePositive
  have rateBound : coefficientRate coefficients G ≤ 4 * G * B := by
    unfold coefficientRate
    nlinarith only [first, second, one]
  have power : 4 * G * B ≤ 2 ^ (2 + Nat.clog 2 G + Nat.clog 2 B) := by
    rw [pow_add, pow_add]
    exact Nat.mul_le_mul (Nat.mul_le_mul_left 4 (Nat.le_pow_clog (by decide) G))
      (Nat.le_pow_clog (by decide) B)
  have logarithm := Nat.clog_le_of_le_pow (rateBound.trans power)
  have factorLog : Nat.clog 2 (coefficientRate coefficients G) + 1 ≤
      4 * B * (Nat.clog 2 G + 1) := by
    have product := Nat.mul_le_mul_right (Nat.clog 2 G + 1) envelopePositive
    nlinarith only [logarithm, logEnvelope, product, envelopePositive]
  unfold coefficientFactor
  calc
    _ ≤ (4 * G * B) * (4 * B * (Nat.clog 2 G + 1)) := Nat.mul_le_mul rateBound factorLog
    _ = _ := by ring

end Splay.Analysis
