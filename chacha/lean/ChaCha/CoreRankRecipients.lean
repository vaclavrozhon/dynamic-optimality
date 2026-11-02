import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith

/-!
# Dyadic core recipients at a rank near the terminal level

This is only the arithmetic kernel for the weighted retained-event
transport. A core dyadic interval ends at a multiple `e` of its length,
with `d < e ≤ L`. The alternating terminal level satisfies
`3 * L + 2 = 2 ^ k`. Its possible dyadic sizes are consequently bounded
by the event's distance from `L`, hence by its black height.
-/

namespace ChaCha.CoreRankRecipients

/-- A dyadic endpoint inside the core leaves a nonzero dyadic remainder. -/
theorem dyadic_remainder_le {L e k h : Nat}
    (hL : 3 * L + 2 = 2 ^ k) (he : e ≤ L) (hepos : 0 < e)
    (hdvd : 2 ^ h ∣ e) :
    2 ^ h ≤ 3 * (L - e) + 2 := by
  have hsmall : 2 ^ h ≤ e := Nat.le_of_dvd hepos hdvd
  have hhk : h ≤ k := by
    by_contra hnot
    have hkh : k ≤ h := by omega
    have hpow : 2 ^ k ≤ 2 ^ h := Nat.pow_le_pow_right (by omega) hkh
    omega
  have htotal : 2 ^ h ∣ 2 ^ k := Nat.pow_dvd_pow 2 hhk
  have hpart : 2 ^ h ∣ 3 * e := dvd_mul_of_dvd_right hdvd 3
  have hid : 3 * e + (3 * (L - e) + 2) = 2 ^ k := by omega
  have hrem : 2 ^ h ∣ 3 * (L - e) + 2 := by
    have hsum : 2 ^ h ∣ 3 * e + (3 * (L - e) + 2) := by
      rw [hid]
      exact htotal
    exact (Nat.dvd_add_iff_right hpart).mpr hsum
  exact Nat.le_of_dvd (by omega) hrem

/-- A core interval containing level `d` has size at most `3*(L-d)-1`. -/
theorem core_size_le {L d e k h : Nat}
    (hL : 3 * L + 2 = 2 ^ k) (he : e ≤ L) (hde : d < e)
    (hdvd : 2 ^ h ∣ e) :
    2 ^ h ≤ 3 * (L - d) - 1 := by
  have hr := dyadic_remainder_le hL he (by omega) hdvd
  omega

/-- Rank `2*beta+chi` has only logarithmically many possible core sizes. -/
theorem core_height_le {L d e k h beta chi : Nat}
    (hL : 3 * L + 2 = 2 ^ k) (he : e ≤ L) (hde : d < e)
    (hdvd : 2 ^ h ∣ e) (hchi : chi ≤ 1)
    (hrank : d + 2 * beta + chi + 1 = L) :
    h ≤ Nat.log 2 (6 * beta + 5) := by
  apply Nat.le_log_of_pow_le (by omega)
  have hr := core_size_le hL he hde hdvd
  omega

end ChaCha.CoreRankRecipients
