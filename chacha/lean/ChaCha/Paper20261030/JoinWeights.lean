import ChaCha.Paper20261030.AuxiliaryJoin

/-!
# Weight decay along an imbalanced join

The weight of an auxiliary tree is its size plus one. When joining around
a separator, recursive descent into the larger input decreases the
combined weight by a constant factor. Keeping the smaller input's weight
in the bound is essential for the telescoping split analysis.
-/

namespace ChaCha.Paper20261030.Auxiliary

open Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl

theorem join_weight_decay (a b c s : Nat) (ha : 1 ≤ a)
    (hs : s = b + 1 + c) (hb : BalancedAtRoot b c) (hbig : delta * a < s) :
    a ≤ delta * b ∧ 8 * (a + b + 2) ≤ 7 * (a + s + 2) := by
  simp only [BalancedAtRoot,delta] at *
  omega

theorem sixth_weight (a b : Nat) (h : 8 * a ≤ 7 * b) : 2 * a ^ 6 ≤ b ^ 6 := by
  have hp := Nat.pow_le_pow_left h 6
  simp only [mul_pow] at hp
  norm_num at hp
  omega

theorem weight_steps_log {steps a b : Nat} (ha : a ≠ 0)
    (h : 2 ^ steps * a ^ 6 ≤ b ^ 6) :
    steps + 6 * Nat.log 2 a ≤ 6 * Nat.clog 2 b := by
  have hlo := Nat.pow_le_pow_left (Nat.pow_log_le_self 2 ha) 6
  have hhi := Nat.pow_le_pow_left (Nat.le_pow_clog (by decide : 1 < 2) b) 6
  have hp := (Nat.mul_le_mul_left (2 ^ steps) hlo).trans (h.trans hhi)
  simp only [← pow_mul,← pow_add] at hp
  have he := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hp
  omega

end ChaCha.Paper20261030.Auxiliary
