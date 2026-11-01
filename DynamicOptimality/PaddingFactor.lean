import DynamicOptimality.PaddingSize
import Splay.Analysis.IteratedLog

/-! The explicit padded Tango² factor is bounded by the same stabilized
third logarithm used by the other shared competitive statements. -/

namespace DynamicOptimality.Padding

theorem factor_le_four_iteratedLog (n : Nat) :
    Nat.clog 2 (Nat.clog 2 (height n + 1) + 2) + 1 ≤
      4 * Splay.Analysis.iteratedLog 3 n := by
  let first := Splay.Analysis.iteratedLog 1 n
  let second := Splay.Analysis.iteratedLog 2 n
  let third := Splay.Analysis.iteratedLog 3 n
  have firstBound : height n ≤ first :=
    Nat.clog_mono_right 2 (Nat.le_max_right 2 n)
  have firstPower : first ≤ 2 ^ second := by
    have bound := Nat.le_pow_clog (b := 2) (by decide) (max 2 first)
    have lower : first ≤ max 2 first := Nat.le_max_right _ _
    exact lower.trans bound
  have secondPower : second ≤ 2 ^ third := by
    have bound := Nat.le_pow_clog (b := 2) (by decide) (max 2 second)
    have lower : second ≤ max 2 second := Nat.le_max_right _ _
    exact lower.trans bound
  have powerPositive : 0 < 2 ^ second := Nat.two_pow_pos _
  have inner : Nat.clog 2 (height n + 1) ≤ second + 1 := by
    apply Nat.clog_le_of_le_pow
    rw [Nat.pow_add_one]
    omega
  have thirdPositive : 0 < third := Splay.Analysis.iteratedLog_pos (by decide)
  have powerThird : 0 < 2 ^ third := Nat.two_pow_pos _
  have outer : Nat.clog 2 (Nat.clog 2 (height n + 1) + 2) ≤ third + 2 := by
    apply Nat.clog_le_of_le_pow
    rw [show third + 2 = (third + 1) + 1 by omega, Nat.pow_add_one, Nat.pow_add_one]
    omega
  change _ ≤ 4 * third
  omega

end DynamicOptimality.Padding
