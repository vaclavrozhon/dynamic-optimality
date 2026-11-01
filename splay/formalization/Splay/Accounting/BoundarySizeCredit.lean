import Splay.Interface.Decay
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace Splay.Accounting

/-- Integer logarithmic credit for the lifetime of a shrinking source,
capped at the threshold separating important and unimportant sources. -/
def boundarySizeCredit (cutoff size : ℕ) : ℕ :=
  min (Nat.clog 2 (cutoff ^ 16 + 1)) (Nat.clog 2 (size ^ 16 + 1))

@[simp] theorem boundarySizeCredit_zero (cutoff : ℕ) : boundarySizeCredit cutoff 0 = 0 := by
  simp [boundarySizeCredit]

theorem boundarySizeCredit_mono (cutoff : ℕ) {first second : ℕ} (order : first ≤ second) :
    boundarySizeCredit cutoff first ≤ boundarySizeCredit cutoff second :=
  min_le_min_left _ (Nat.clog_mono_right 2 (Nat.add_le_add_right (Nat.pow_le_pow_left order 16) 1))

theorem boundarySizeCredit_of_le {cutoff size : ℕ} (within : size ≤ cutoff) :
    boundarySizeCredit cutoff size = Nat.clog 2 (size ^ 16 + 1) := by
  apply min_eq_right
  exact Nat.clog_mono_right 2 (Nat.add_le_add_right (Nat.pow_le_pow_left within 16) 1)

theorem clog_two_mul (value : ℕ) (positive : 0 < value) :
    Nat.clog 2 (2 * value) = Nat.clog 2 value + 1 := by
  rw [Nat.clog_of_two_le (by decide : 1 < 2) (by omega : 2 ≤ 2 * value)]
  congr 2
  omega

/-- A single one-eighth loss has a factor-four effect on sixteenth powers.
Only natural-number arithmetic is needed for the logarithmic credit. -/
theorem one_eighth_decay_power {before after : ℕ} (decay : 8 * after ≤ 7 * before) :
    4 * after ^ 16 ≤ before ^ 16 := by
  have powered := Nat.pow_le_pow_left decay 16
  rw [Nat.mul_pow, Nat.mul_pow] at powered
  have coefficient : 4 * 7 ^ 16 ≤ 8 ^ 16 := by norm_num
  have weighted : 8 ^ 16 * (4 * after ^ 16) ≤ 8 ^ 16 * before ^ 16 := by
    calc
      _ = 4 * (8 ^ 16 * after ^ 16) := by ring
      _ ≤ 4 * (7 ^ 16 * before ^ 16) := Nat.mul_le_mul_left _ powered
      _ = (4 * 7 ^ 16) * before ^ 16 := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ coefficient
  norm_num at weighted
  omega

/-- Every positive source at or below the cutoff spends one unit of credit
when a nonexempt pass removes at least one eighth of its elements. -/
theorem boundarySizeCredit_decay {cutoff before after : ℕ}
    (positive : 0 < before) (within : before ≤ cutoff) (decay : 8 * after ≤ 7 * before) :
    boundarySizeCredit cutoff after + 1 ≤ boundarySizeCredit cutoff before := by
  have afterLe : after ≤ before := by omega
  rw [boundarySizeCredit_of_le (afterLe.trans within), boundarySizeCredit_of_le within]
  by_cases empty : after = 0
  · subst after
    simp only [Nat.zero_pow (by decide : 0 < 16), Nat.zero_add, Nat.clog_one_right, Nat.zero_add]
    exact Nat.clog_pos (by decide) (by have := pow_pos positive 16; omega)
  · have afterPower : 0 < after ^ 16 := pow_pos (by omega) _
    have powerBound := one_eighth_decay_power decay
    have doubled : 2 * (after ^ 16 + 1) ≤ before ^ 16 + 1 := by omega
    have bound := Nat.clog_mono_right 2 doubled
    rw [clog_two_mul _ (by omega)] at bound
    exact bound

/-- The initial credit is bounded by a uniform multiple of log(cutoff). -/
theorem boundarySizeCredit_bound (cutoff size : ℕ) :
    boundarySizeCredit cutoff size ≤ 16 * Nat.clog 2 cutoff + 1 := by
  apply (min_le_left _ _).trans
  apply Nat.clog_le_of_le_pow
  have powered := Nat.pow_le_pow_left (Nat.le_pow_clog (by decide : 1 < 2) cutoff) 16
  have powerEq : (2 ^ Nat.clog 2 cutoff) ^ 16 = 2 ^ (16 * Nat.clog 2 cutoff) := by
    rw [← Nat.pow_mul]
    congr 1
    omega
  rw [powerEq] at powered
  have positive : 0 < 2 ^ (16 * Nat.clog 2 cutoff) := pow_pos (by decide) _
  rw [pow_succ (2 : ℕ)]
  omega

end Splay.Accounting
