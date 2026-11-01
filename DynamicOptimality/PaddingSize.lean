import Mathlib.Data.Nat.Log
import Lean.Elab.Tactic.Omega

/-! A power-of-two virtual universe within a constant factor of every
nonempty original universe. Its extra keys are removed from the actual BST
by prefix projection; these numerical lemmas do not add physical keys. -/

namespace DynamicOptimality.Padding

def height (n : Nat) : Nat := Nat.clog 2 n

def capacity (n : Nat) : Nat := 2 ^ (height n + 1)

theorem le_capacity (n : Nat) : n ≤ capacity n := by
  have bound : n ≤ 2 ^ Nat.clog 2 n := Nat.le_pow_clog (by decide) n
  unfold capacity height
  rw [Nat.pow_add_one]
  omega

theorem capacity_le_four_mul {n : Nat} (positive : 0 < n) : capacity n ≤ 4 * n := by
  by_cases one : n = 1
  · subst n
    simp [capacity, height]
  · have greater : 1 < n := by omega
    have power := Nat.pow_pred_clog_lt_self (b := 2) (by decide) greater
    rw [Nat.pred_eq_sub_one] at power
    have logPositive : 0 < Nat.clog 2 n := Nat.clog_pos (by decide) greater
    have exponent : Nat.clog 2 n = (Nat.clog 2 n - 1) + 1 := by omega
    have whole : 2 ^ Nat.clog 2 n = 2 ^ (Nat.clog 2 n - 1) * 2 := by
      conv_lhs => rw [exponent]
      exact Nat.pow_add_one _ _
    unfold capacity height
    rw [Nat.pow_add_one, whole]
    omega

end DynamicOptimality.Padding
