import Mathlib

/-!
Natural-number endpoint for the literal compressed trace.

The only input is the three finite inequalities supplied by the original
interface, the compressed trace, and the original source tail. The transformed
trace and its cost may depend on the chosen cutoff. No real logarithm or
asymptotic convention occurs in the endpoint.
-/

namespace Splay.Research.HistoricalCompressionNatEndpoint

def logScale (R : ℕ) : ℕ := Nat.clog 2 (R + 1) + 1

def constantCutoff (cv K : ℕ) : ℕ := Nat.clog 2 (4 * cv * K + 1)

def endpointConstant (ci cv K : ℕ) : ℕ :=
  2 * ci + 2 * cv * K + 1 + 2 * cv * K * (constantCutoff cv K + 3)

def compressionConstant (growingLimit exemption decayBlock : ℕ) : ℕ :=
  38 + 686 * ((1 + growingLimit) * (exemption + decayBlock) + 1) + 42

/-- Put the actual row-ledger constants in the polynomial input form used
below. The fixed source exemption and decay block contribute only to K. -/
theorem compression_polynomial_bound
    (growingLimit exemption decayBlock R I V newV late k : ℕ)
    (rangePositive : 1 ≤ R)
    (rowBudget : newV ≤ 38 * R * I +
      686 * ((1 + growingLimit) * (exemption + decayBlock * k) + 1) * V +
      (40 * R + 2) * late) :
    newV ≤ compressionConstant growingLimit exemption decayBlock *
      (R * I + (k + 1) * V + R * late) := by
  let B := (1 + growingLimit) * (exemption + decayBlock) + 1
  let K := compressionConstant growingLimit exemption decayBlock
  have cutoff : exemption + decayBlock * k ≤ (exemption + decayBlock) * (k + 1) := by
    nlinarith only [Nat.mul_le_mul_left exemption (show 1 ≤ k + 1 by omega),
      Nat.zero_le decayBlock]
  have errorCoefficient : (1 + growingLimit) * (exemption + decayBlock * k) + 1 ≤
      B * (k + 1) := by
    have scaled := Nat.mul_le_mul_left (1 + growingLimit) cutoff
    dsimp [B]
    nlinarith only [scaled, Nat.zero_le k]
  have lateCoefficient : 40 * R + 2 ≤ 42 * R := by omega
  have insertionConstant : 38 ≤ K := by dsimp [K, compressionConstant]; omega
  have errorConstant : 686 * B ≤ K := by dsimp [K, B, compressionConstant]; omega
  have lateConstant : 42 ≤ K := by dsimp [K, compressionConstant]; omega
  have first := Nat.mul_le_mul_right (R * I) insertionConstant
  have second₁ := Nat.mul_le_mul_right V (Nat.mul_le_mul_left 686 errorCoefficient)
  have second₂ := Nat.mul_le_mul_right ((k + 1) * V) errorConstant
  have third₁ := Nat.mul_le_mul_right late lateCoefficient
  have third₂ := Nat.mul_le_mul_right (R * late) lateConstant
  change newV ≤ K * (R * I + (k + 1) * V + R * late)
  nlinarith only [rowBudget, first, second₁, second₂, third₁, third₂]

theorem logScale_positive (R : ℕ) : 1 ≤ logScale R := by
  unfold logScale
  omega

theorem logScale_le_succ (R : ℕ) : logScale R ≤ R + 1 := by
  have power : R + 1 ≤ 2 ^ R := Nat.succ_le_of_lt (Nat.lt_pow_self (by norm_num))
  have logarithm : Nat.clog 2 (R + 1) ≤ R := Nat.clog_le_of_le_pow power
  unfold logScale
  omega

theorem succ_le_power_logScale (R : ℕ) : R + 1 ≤ 2 ^ logScale R := by
  have power := Nat.le_pow_clog (by norm_num : 1 < (2 : ℕ)) (R + 1)
  unfold logScale
  rw [pow_succ]
  omega

theorem cutoff_absorbs (cv K R : ℕ) :
    2 * cv * K * logScale R * R ≤
      2 ^ (2 * logScale R + constantCutoff cv K) := by
  have constantPower := Nat.le_pow_clog (by norm_num : 1 < (2 : ℕ))
    (4 * cv * K + 1)
  have smallConstant : 2 * cv * K ≤ 2 ^ constantCutoff cv K := by
    unfold constantCutoff
    nlinarith
  have basePower := succ_le_power_logScale R
  have scalePower : logScale R ≤ 2 ^ logScale R :=
    (logScale_le_succ R).trans basePower
  have rankPower : R ≤ 2 ^ logScale R := by omega
  calc
    2 * cv * K * logScale R * R = (2 * cv * K) * (logScale R * R) := by ring
    _ ≤ 2 ^ constantCutoff cv K * (2 ^ logScale R * 2 ^ logScale R) :=
      Nat.mul_le_mul smallConstant (Nat.mul_le_mul scalePower rankPower)
    _ = 2 ^ (2 * logScale R + constantCutoff cv K) := by
      rw [show 2 * logScale R = logScale R + logScale R by omega,
        pow_add, pow_add]
      ring

/-- Finite absorption at the explicitly chosen logarithmic cutoff. -/
theorem activity_endpoint
    (ci cv K A I V R : ℕ)
    (realizations : ∀ k : ℕ, ∃ newV late : ℕ,
      A ≤ ci * (R + 1) * I + cv * Nat.clog 2 (R + 1) * newV ∧
      newV ≤ K * (R * I + (k + 1) * V + R * late) ∧
      2 ^ k * late ≤ A + I) :
    A ≤ endpointConstant ci cv K *
      (I * (R + 1) * logScale R + V * logScale R ^ 2) := by
  let q := logScale R
  let h := constantCutoff cv K
  let k := 2 * q + h
  obtain ⟨newV, late, coarse, compression, tail⟩ := realizations k
  have qPositive : 1 ≤ q := logScale_positive R
  have logarithm : Nat.clog 2 (R + 1) ≤ q := by
    dsimp [q, logScale]
    omega
  have coarse' : A ≤ ci * (R + 1) * I + cv * q * newV := by
    exact coarse.trans (Nat.add_le_add_left
      (Nat.mul_le_mul_right newV (Nat.mul_le_mul_left cv logarithm)) _)
  have compression' : newV ≤ K * ((R + 1) * I + (k + 1) * V + R * late) := by
    apply compression.trans
    apply Nat.mul_le_mul_left
    exact Nat.add_le_add_right
      (Nat.add_le_add_right (Nat.mul_le_mul_right I (Nat.le_succ R)) _) _
  have combined : A ≤
      ci * (R + 1) * I + cv * K * q * (R + 1) * I +
        cv * K * q * (k + 1) * V + cv * K * q * R * late := by
    have scaled := Nat.mul_le_mul_left (cv * q) compression'
    nlinarith only [coarse', scaled]
  have coefficient : 2 * cv * K * q * R ≤ 2 ^ k := cutoff_absorbs cv K R
  have paidTail : 2 * (cv * K * q * R * late) ≤ A + I := by
    have scaled := Nat.mul_le_mul_right late coefficient
    nlinarith only [scaled, tail]
  have absorbed : A ≤
      2 * ci * (R + 1) * I + 2 * cv * K * q * (R + 1) * I +
        2 * cv * K * q * (k + 1) * V + I := by
    nlinarith only [combined, paidTail]
  have cutoff : k + 1 ≤ (h + 3) * q := by
    dsimp [k]
    nlinarith only [Nat.mul_le_mul_left (h + 1) qPositive]
  have first := Nat.mul_le_mul_left (2 * ci * (R + 1) * I) qPositive
  have insertion : I ≤ I * (R + 1) * q := by
    have rank : 1 ≤ R + 1 := by omega
    have scale : 1 ≤ (R + 1) * q := by simpa using Nat.mul_le_mul rank qPositive
    nlinarith only [Nat.mul_le_mul_left I scale]
  have value := Nat.mul_le_mul_left (2 * cv * K * q * V) cutoff
  have separated : A ≤
      (2 * ci + 2 * cv * K + 1) * (I * (R + 1) * q) +
      (2 * cv * K * (h + 3)) * (V * q ^ 2) := by
    nlinarith only [absorbed, first, insertion, value]
  have joined :
      (2 * ci + 2 * cv * K + 1) * (I * (R + 1) * q) +
      (2 * cv * K * (h + 3)) * (V * q ^ 2) ≤
      (2 * ci + 2 * cv * K + 1 + 2 * cv * K * (h + 3)) *
        (I * (R + 1) * q + V * q ^ 2) := by
    have leftCoefficient : 2 * ci + 2 * cv * K + 1 ≤
        2 * ci + 2 * cv * K + 1 + 2 * cv * K * (h + 3) := by omega
    have rightCoefficient : 2 * cv * K * (h + 3) ≤
        2 * ci + 2 * cv * K + 1 + 2 * cv * K * (h + 3) := by omega
    have left := Nat.mul_le_mul_right (I * (R + 1) * q) leftCoefficient
    have right := Nat.mul_le_mul_right (V * q ^ 2) rightCoefficient
    nlinarith only [left, right]
  exact separated.trans joined

theorem uniform_activity_endpoint (ci cv K : ℕ) :
    ∃ C : ℕ, 0 < C ∧ ∀ A I V R : ℕ,
      (∀ k : ℕ, ∃ newV late : ℕ,
        A ≤ ci * (R + 1) * I + cv * Nat.clog 2 (R + 1) * newV ∧
        newV ≤ K * (R * I + (k + 1) * V + R * late) ∧
        2 ^ k * late ≤ A + I) →
      A ≤ C * (I * (R + 1) * logScale R + V * logScale R ^ 2) := by
  refine ⟨endpointConstant ci cv K, ?_, ?_⟩
  · unfold endpointConstant
    omega
  · intro A I V R realizations
    exact activity_endpoint ci cv K A I V R realizations

#print axioms activity_endpoint
#print axioms uniform_activity_endpoint
#print axioms compression_polynomial_bound

end Splay.Research.HistoricalCompressionNatEndpoint
