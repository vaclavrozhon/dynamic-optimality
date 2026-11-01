import Mathlib.Data.Nat.Log
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# A deterministic depth offset avoids low-rank dyadic spikes

`alternating q` has binary digits 0101...01.  If an insertion promotes
a separator to rank `k`, its changed even frontier is `2 * (t - k)`.
The theorem bounds that frontier's dyadic valuation by a logarithm of
`k`, rather than of the reserved height cap.  This is the arithmetic
kernel only: red-black rank monotonicity and geometric packing of
promotions are proved separately in the research note.
-/

namespace TangoSquared.AlternatingRankOffset

def alternating : Nat → Nat
  | 0 => 0
  | q + 1 => 4 * alternating q + 1

theorem three_mul_add_one (q : Nat) :
    3 * alternating q + 1 = 2 ^ (2 * q) := by
  induction q with
  | zero => simp [alternating]
  | succ q ih =>
    simp only [alternating]
    calc
      3 * (4 * alternating q + 1) + 1 = 4 * (3 * alternating q + 1) := by ring
      _ = 4 * 2 ^ (2 * q) := by rw [ih]
      _ = 2 ^ (2 * (q + 1)) := by
        rw [show 2 * (q + 1) = 2 * q + 2 by omega, pow_add]
        ring

/-- Every dyadic divisor of the shifted rank is at most `3*k+1`. -/
theorem dyadic_divisor_le {t h k r : Nat}
    (ht : 3 * t + 1 = 2 ^ h) (hk : k < t)
    (hdvd : 2 ^ r ∣ t - k) : 2 ^ r ≤ 3 * k + 1 := by
  have hpos : 0 < t - k := Nat.sub_pos_of_lt hk
  have hsmall : 2 ^ r ≤ t - k := Nat.le_of_dvd hpos hdvd
  have hrh : r ≤ h := by
    by_contra hnot
    have hhr : h ≤ r := by omega
    have hpow : 2 ^ h ≤ 2 ^ r := Nat.pow_le_pow_right (by omega) hhr
    omega
  have htotal : 2 ^ r ∣ 2 ^ h := Nat.pow_dvd_pow 2 hrh
  have hpart : 2 ^ r ∣ 3 * (t - k) := dvd_mul_of_dvd_right hdvd 3
  have hid : 3 * (t - k) + (3 * k + 1) = 2 ^ h := by omega
  have hrem : 2 ^ r ∣ 3 * k + 1 := by
    have hsum : 2 ^ r ∣ 3 * (t - k) + (3 * k + 1) := by
      rw [hid]
      exact htotal
    exact (Nat.dvd_add_iff_right hpart).mpr hsum
  exact Nat.le_of_dvd (by omega) hrem

theorem shifted_valuation_le {t h k : Nat}
    (ht : 3 * t + 1 = 2 ^ h) (hk : k < t) :
    padicValNat 2 (t - k) ≤ Nat.log 2 (3 * k + 1) := by
  apply Nat.le_log_of_pow_le (by omega)
  exact dyadic_divisor_le ht hk pow_padicValNat_dvd

theorem even_frontier_valuation_le (q k : Nat)
    (hk : k < alternating q) :
    padicValNat 2 (2 * (alternating q - k)) ≤
      1 + Nat.log 2 (3 * k + 1) := by
  have hn : alternating q - k ≠ 0 := by omega
  rw [padicValNat.mul (by decide) hn, padicValNat.self (by decide)]
  exact Nat.add_le_add_left
    (shifted_valuation_le (three_mul_add_one q) hk) 1

end TangoSquared.AlternatingRankOffset
