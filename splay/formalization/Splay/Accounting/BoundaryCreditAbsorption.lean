import Splay.Accounting.BoundaryCreditHistory
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace Splay.Accounting

/-- Absorb the boundary contribution to activity using the actual global
credit inequality. No comparison between the two pairing classes is assumed. -/
theorem boundary_credit_absorb {activity boundary volume reserve rate cutoff : ℕ}
    (positive : 0 < cutoff) (large : 16 * rate ≤ cutoff)
    (activityBound : activity ≤ rate * (volume + boundary))
    (boundaryBound : cutoff * (2 * boundary) ≤ 4 * cutoff * reserve + 16 * activity) :
    activity ≤ 2 * rate * (volume + 2 * reserve) ∧ boundary ≤ 2 * reserve + 8 * activity := by
  have activityWeighted := Nat.mul_le_mul_left cutoff activityBound
  have boundaryWeighted := Nat.mul_le_mul_left rate boundaryBound
  have absorption := Nat.mul_le_mul_right activity large
  have scaled : cutoff * activity ≤ cutoff * (2 * rate * (volume + 2 * reserve)) := by
    nlinarith
  have activityPaid : activity ≤ 2 * rate * (volume + 2 * reserve) := by
    nlinarith
  have boundaryPaid : boundary ≤ 2 * reserve + 8 * activity := by
    nlinarith
  exact ⟨activityPaid, boundaryPaid⟩

/-- A polynomial cutoff suffices for absorption and has logarithmic credit
capacity. Its coefficient will be fixed before quantifying over tree sizes. -/
theorem polynomial_boundary_cutoff {coefficient gap : ℕ}
    (coefficientPositive : 0 < coefficient) (gapPositive : 0 < gap) :
    let cutoff := 32 * coefficient * gap ^ 2
    0 < cutoff ∧ 16 * (coefficient * (gap * (Nat.clog 2 gap + 1))) ≤ cutoff ∧
      Interface.boundaryCreditCapacity cutoff ≤
        (16 * Nat.clog 2 (32 * coefficient) + 46) * (Nat.clog 2 gap + 1) := by
  dsimp only
  have logSmall : Nat.clog 2 gap ≤ gap :=
    Nat.clog_le_of_le_pow (Nat.le_of_lt (Nat.lt_pow_self (by decide : 1 < 2)))
  have cutoffPositive : 0 < 32 * coefficient * gap ^ 2 := by positivity
  have large : 16 * (coefficient * (gap * (Nat.clog 2 gap + 1))) ≤ 32 * coefficient * gap ^ 2 := by
    nlinarith [Nat.mul_le_mul_left (16 * coefficient * gap) (show Nat.clog 2 gap + 1 ≤ 2 * gap by omega)]
  have firstPow := Nat.le_pow_clog (by decide : 1 < 2) (32 * coefficient)
  have secondPow := Nat.pow_le_pow_left (Nat.le_pow_clog (by decide : 1 < 2) gap) 2
  have cutoffPow : 32 * coefficient * gap ^ 2 ≤
      2 ^ (Nat.clog 2 (32 * coefficient) + 2 * Nat.clog 2 gap) := by
    calc
      32 * coefficient * gap ^ 2 ≤ 2 ^ Nat.clog 2 (32 * coefficient) * (2 ^ Nat.clog 2 gap) ^ 2 :=
        Nat.mul_le_mul firstPow secondPow
      _ = _ := by rw [pow_add, ← pow_mul]; congr 2; omega
  have logBound := Nat.clog_le_of_le_pow cutoffPow
  have capacity := Interface.boundaryCreditCapacity_bound (32 * coefficient * gap ^ 2)
  exact ⟨cutoffPositive, large, by nlinarith⟩

end Splay.Accounting
