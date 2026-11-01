import Splay.Interface.LayerCoefficients

namespace Splay.Analysis.LayerEnvelope

open Splay.Interface Splay.Research
open LayerCompression LayerCoefficients

/-- Integer iterated-log depth: iterate the binary compressed cap until it
is at most two. `cap_le_clog` below identifies the step as a ceiling log. -/
def depth (G : ℕ) : ℕ :=
  if _small : G ≤ 2 then 0 else depth (cap G) + 1
termination_by G
decreasing_by exact SharperDyadicCompressionRowBudget.cap_lt_of_two_lt (by omega)

theorem depth_of_large (G : ℕ) (large : 2 < G) : depth G = depth (cap G) + 1 := by
  rw [depth]
  simp only [show ¬G ≤ 2 by omega, dite_false]

theorem cap_le_clog {G : ℕ} (large : 2 < G) : cap G ≤ Nat.clog 2 G := by
  have positive : G - 1 ≠ 0 := by omega
  have lower := Nat.pow_log_le_self 2 positive
  have less : Nat.log 2 (G - 1) < Nat.clog 2 G :=
    (Nat.lt_clog_iff_pow_lt (by decide)).mpr (by omega)
  have two : 2 ≤ Nat.clog 2 G := by
    have := (Nat.lt_clog_iff_pow_lt (by decide : 1 < 2)).mpr
      (show 2 ^ 1 < G by simpa using large)
    omega
  unfold cap SharperDyadicCompressionRowBudget.cap DyadicRankCompression.label
  exact max_le two (by omega)

theorem cap_eq_clog {G : ℕ} (large : 2 < G) : cap G = Nat.clog 2 G := by
  apply Nat.le_antisymm (cap_le_clog large)
  have upper := Nat.lt_pow_succ_log_self (by decide : 1 < 2) (G - 1)
  have ceil : Nat.clog 2 G ≤ Nat.log 2 (G - 1) + 1 := Nat.clog_le_of_le_pow (by omega)
  exact ceil.trans (by
    unfold cap SharperDyadicCompressionRowBudget.cap DyadicRankCompression.label
    omega)

theorem depth_mono : Monotone depth := by
  have bound : ∀ G, ∀ a ≤ G, depth a ≤ depth G := by
    intro G
    induction G using Nat.strong_induction_on with
    | h G ih =>
      intro a order
      by_cases smallA : a ≤ 2
      · have zero : depth a = 0 := by rw [depth]; simp only [dif_pos smallA]
        rw [zero]
        exact Nat.zero_le _
      · have largeA : 2 < a := by omega
        have largeG : 2 < G := by omega
        have capOrder : cap a ≤ cap G := by
          rw [cap_eq_clog largeA, cap_eq_clog largeG]
          exact Nat.clog_mono_right 2 order
        have smaller := SharperDyadicCompressionRowBudget.cap_lt_of_two_lt largeG
        have previous := ih (cap G) smaller (cap a) capOrder
        rw [depth_of_large a largeA, depth_of_large G largeG]
        omega
  exact fun a b order => bound b a order

/-- A factorial majorant for the cap-independent coefficient recurrence.
Its logarithm is O((t+1) log(t+2)); no hidden depth-dependent constants occur. -/
def envelope (t : ℕ) : ℕ := 2 ^ (20 * (t + 1)) * (Nat.factorial (t + 1)) ^ 2

theorem envelope_pos (t : ℕ) : 0 < envelope t := by
  unfold envelope
  have := Nat.factorial_pos (t + 1)
  positivity

theorem envelope_succ (t : ℕ) :
    envelope (t + 1) = envelope t * 2 ^ 20 * (t + 2) ^ 2 := by
  unfold envelope
  rw [show t + 1 + 1 = t + 2 by omega, Nat.factorial_succ,
    show 20 * (t + 2) = 20 * (t + 1) + 20 by omega, pow_add]
  ring

theorem envelope_growth (t : ℕ) : 13 * envelope t ≤ envelope (t + 1) := by
  rw [envelope_succ]
  have positive : 1 ≤ (t + 2) ^ 2 := by
    have : 0 < (t + 2) ^ 2 := by positivity
    omega
  have := Nat.mul_le_mul_left (envelope t * 2 ^ 20) positive
  norm_num at this ⊢
  omega

theorem envelope_mono : Monotone envelope :=
  monotone_nat_of_le_succ (fun t => (by omega : envelope t ≤ 13 * envelope t).trans (envelope_growth t))

theorem factorial_le_pow (n : ℕ) : Nat.factorial n ≤ n ^ n := by
  exact Nat.factorial_le_pow n

theorem envelope_le_pow (t : ℕ) :
    envelope t ≤ 2 ^ (20 * (t + 1) + 2 * (t + 1) ^ 2) := by
  have integerLog : Nat.clog 2 (t + 1) ≤ t + 1 :=
    Nat.clog_le_of_le_pow (Nat.le_of_lt (Nat.lt_pow_self (by decide : 1 < 2)))
  have factor := (factorial_le_pow (t + 1)).trans
    (Nat.pow_le_pow_left (Nat.le_pow_clog (by decide : 1 < 2) (t + 1)) (t + 1))
  have power : (Nat.factorial (t + 1)) ^ 2 ≤ 2 ^ (2 * (t + 1) ^ 2) := by
    calc
      _ ≤ ((2 ^ Nat.clog 2 (t + 1)) ^ (t + 1)) ^ 2 := Nat.pow_le_pow_left factor 2
      _ = 2 ^ (Nat.clog 2 (t + 1) * (t + 1) * 2) := by
        rw [← pow_mul, ← pow_mul, Nat.mul_assoc]
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (by nlinarith)
  unfold envelope
  rw [pow_add]
  exact Nat.mul_le_mul_left _ power

theorem cutoff_envelope (t : ℕ) :
    cutoff (envelope t) ≤ 5 + 20 * (t + 1) + 2 * (t + 1) ^ 2 := by
  apply Nat.clog_le_of_le_pow
  have positive := envelope_pos t
  calc
    24 * envelope t + 1 ≤ 32 * envelope t := by omega
    _ ≤ 2 ^ 5 * 2 ^ (20 * (t + 1) + 2 * (t + 1) ^ 2) :=
      Nat.mul_le_mul_left _ (envelope_le_pow t)
    _ = _ := by rw [← pow_add]; congr 1; omega

theorem variation_le_envelope {shape : Shape} (smallShape : shapeConstant shape ≤ 31)
    {b t : ℕ} (bounded : b ≤ envelope t) :
    variationCoefficient shape b ≤ envelope (t + 1) := by
  have cutoffBound : cutoff b ≤ 5 + 20 * (t + 1) + 2 * (t + 1) ^ 2 :=
    (Nat.clog_mono_right 2 (by omega : 24 * b + 1 ≤ 24 * envelope t + 1)).trans (cutoff_envelope t)
  have numeric : 24 * 31 * (5 + 20 * (t + 1) + 2 * (t + 1) ^ 2 + 2) ≤
      2 ^ 20 * (t + 2) ^ 2 := by norm_num; nlinarith
  calc
    variationCoefficient shape b ≤
        24 * envelope t * 31 * (5 + 20 * (t + 1) + 2 * (t + 1) ^ 2 + 2) := by
      unfold variationCoefficient
      gcongr
    _ = envelope t * (24 * 31 * (5 + 20 * (t + 1) + 2 * (t + 1) ^ 2 + 2)) := by ring
    _ ≤ envelope t * (2 ^ 20 * (t + 2) ^ 2) := Nat.mul_le_mul_left _ numeric
    _ = envelope (t + 1) := by rw [envelope_succ]; ring

/-- Both coefficients have a factorial envelope in the iterated-log depth. -/
theorem coefficients_le (shape : Shape) (smallShape : shapeConstant shape ≤ 31) (G : ℕ) :
    (coefficients shape G).1 ≤ envelope (depth G) * (Nat.clog 2 G + 1) ∧
    (coefficients shape G).2 ≤ envelope (depth G) := by
  induction G using Nat.strong_induction_on with
  | h G ih =>
    by_cases small : G ≤ 2
    · have smallCoefficients : coefficients shape G = (4, 5) := by
        rw [coefficients]
        simp only [dif_pos small]
      have smallDepth : depth G = 0 := by
        rw [depth]
        simp only [dif_pos small]
      rw [smallCoefficients, smallDepth]
      norm_num [envelope]
      omega
    · have large : 2 < G := by omega
      have previous := ih (cap G) (SharperDyadicCompressionRowBudget.cap_lt_of_two_lt large)
      rw [coefficients_of_large shape G large, depth_of_large G large]
      dsimp only [Prod.fst, Prod.snd]
      refine ⟨?_, variation_le_envelope smallShape previous.2⟩
      have Rpositive := SharperDyadicCompressionRowBudget.cap_ge_two G
      change 2 ≤ cap G at Rpositive
      have Bpositive := envelope_pos (depth (cap G))
      have logBound : Nat.clog 2 (cap G) + 1 ≤ 2 * cap G := by
        have := Nat.clog_le_of_le_pow (Nat.le_of_lt (Nat.lt_pow_self (by decide : 1 < 2) (n := cap G)))
        omega
      have insertBound := previous.1.trans (Nat.mul_le_mul_left _ logBound)
      have raw : insertionCoefficient (coefficients shape (cap G)).1
          (coefficients shape (cap G)).2 (cap G) ≤ 13 * envelope (depth (cap G)) * cap G := by
        unfold insertionCoefficient
        have second := Nat.mul_le_mul_right (4 * cap G - 2) previous.2
        have coefficient : 4 * cap G - 2 ≤ 4 * cap G := Nat.sub_le _ _
        have enlarged := second.trans (Nat.mul_le_mul_left _ coefficient)
        have one : 1 ≤ envelope (depth (cap G)) * cap G :=
          Nat.mul_pos Bpositive (by omega)
        nlinarith only [insertBound, enlarged, one]
      calc
        _ ≤ _ := raw
        _ ≤ envelope (depth (cap G) + 1) * cap G :=
          Nat.mul_le_mul_right _ (envelope_growth _)
        _ ≤ envelope (depth (cap G) + 1) * (Nat.clog 2 G + 1) :=
          Nat.mul_le_mul_left _ ((cap_le_clog large).trans (by omega))

/-- The explicit slowly growing loss used in the final splay bound. Its
finite growth estimate is `E_le_iterated_log_exponential` below. -/
def E (G : ℕ) : ℕ := envelope (depth G) ^ 2

theorem E_pos (G : ℕ) : 0 < E G := by
  unfold E
  exact pow_pos (envelope_pos _) _

theorem E_mono : Monotone E := fun _ _ order =>
  Nat.pow_le_pow_left (envelope_mono (depth_mono order)) 2

/-- A precise integer form of `E(G) = exp(O(log* G log(log* G + 2)))`.
Here `depth` is exactly iteration of ceiling binary log down to two, as
proved by `cap_eq_clog` and `depth_of_large`. -/
theorem E_le_iterated_log_exponential (G : ℕ) :
    E G ≤ 2 ^ (44 * (depth G + 1) * (Nat.clog 2 (depth G + 2) + 1)) := by
  let t := depth G
  have powerBase : t + 1 ≤ 2 ^ Nat.clog 2 (t + 2) :=
    (by omega : t + 1 ≤ t + 2).trans (Nat.le_pow_clog (by decide) _)
  have factorial := (factorial_le_pow (t + 1)).trans (Nat.pow_le_pow_left powerBase (t + 1))
  have bound : E G ≤ 2 ^ (40 * (t + 1) + 4 * (Nat.clog 2 (t + 2) * (t + 1))) := by
    calc
      E G ≤ (2 ^ (20 * (t + 1)) * ((2 ^ Nat.clog 2 (t + 2)) ^ (t + 1)) ^ 2) ^ 2 :=
        Nat.pow_le_pow_left (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left factorial 2)) 2
      _ = _ := by
        rw [mul_pow, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_add]
        congr 1
        ring
  apply bound.trans
  apply Nat.pow_le_pow_right (by decide)
  change _ ≤ 44 * (t + 1) * (Nat.clog 2 (t + 2) + 1)
  nlinarith

/-- The standalone interface improvement, ready for any algorithm whose
accounting consumes insertion and unit-variation coefficients. -/
theorem coefficientBound (shape : Shape) (smallShape : shapeConstant shape ≤ 31)
    (exempt : shape.exemptPasses = 2)
    (numerator : shape.matchingNumerator = 1)
    (denominator : shape.matchingDenominator = 8) :
    CoefficientBound shape (fun G => (E G * (Nat.clog 2 G + 1), E G)) := by
  apply (LayerCoefficients.valid shape exempt numerator denominator).mono
  · intro G
    have bounds := coefficients_le shape smallShape G
    have square : envelope (depth G) ≤ E G := by
      unfold E
      have := envelope_pos (depth G)
      nlinarith
    exact bounds.1.trans (Nat.mul_le_mul_right _ square)
  · intro G
    have bounds := coefficients_le shape smallShape G
    have square : envelope (depth G) ≤ E G := by
      unfold E
      have := envelope_pos (depth G)
      nlinarith
    exact bounds.2.trans square

end Splay.Analysis.LayerEnvelope
