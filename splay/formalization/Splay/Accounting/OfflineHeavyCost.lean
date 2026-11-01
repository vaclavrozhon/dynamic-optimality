import Splay.Accounting.OfflineHeavyPotential

namespace Splay.Accounting.OfflineConnectedSupport

open OfflineNormalForm.RibStack

/-- A worst-case local bound, separate from the constant amortized bound. -/
def heavyUnitCost (capacity : ℕ) : ℕ := 16 * (Nat.clog 2 (capacity + 1) + 1) ^ 2 + 3

theorem counterPush_le_unit {capacity : ℕ} (digits : List Digits.Digit)
    (fits : Digits.value digits ≤ capacity) :
    16 * Digits.pushCost 0 digits + 3 ≤ heavyUnitCost capacity := by
  have cost := Digits.pushCost_le_logSquared digits
  have levels := Nat.clog_mono_right 2 (Nat.add_le_add_right fits 1)
  have powers := Nat.pow_le_pow_left (Nat.add_le_add_right levels 1) 2
  dsimp [heavyUnitCost]
  omega

theorem counterPop_le_unit {capacity : ℕ} (digits : List Digits.Digit)
    (fits : Digits.value digits ≤ capacity) :
    16 * Digits.popCost 0 digits + 3 ≤ heavyUnitCost capacity := by
  have cost := Digits.popCost_le_logSquared digits
  have levels := Nat.clog_mono_right 2 (Nat.add_le_add_right fits 1)
  have powers := Nat.pow_le_pow_left (Nat.add_le_add_right levels 1) 2
  dsimp [heavyUnitCost]
  omega

end Splay.Accounting.OfflineConnectedSupport
