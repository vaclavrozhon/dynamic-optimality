import Splay.Interface.Decay
import Splay.Accounting.Certificate

namespace Splay.Accounting

/-- Four losses of at least a quarter halve the remaining size. -/
theorem quarter_decay_four {size : ℕ → ℕ} {start : ℕ}
    (decay : ∀ index < 4, 4 * size (start + index + 1) ≤ 3 * size (start + index)) :
    2 * size (start + 4) ≤ size start := by
  have first := decay 0 (by decide)
  have second := decay 1 (by decide)
  have third := decay 2 (by decide)
  have fourth := decay 3 (by decide)
  change 4 * size (start + 1) ≤ 3 * size start at first
  change 4 * size (start + 2) ≤ 3 * size (start + 1) at second
  change 4 * size (start + 3) ≤ 3 * size (start + 2) at third
  change 4 * size (start + 4) ≤ 3 * size (start + 3) at fourth
  omega

/-- A chronological quarter-decay sequence loses a factor two per four
events. The argument allows larger drops and termination at zero. -/
theorem quarter_decay_dyadic {size : ℕ → ℕ} {steps groups : ℕ}
    (decay : ∀ index < steps, 4 * size (index + 1) ≤ 3 * size index)
    (within : 4 * groups ≤ steps) :
    2 ^ groups * size (4 * groups) ≤ size 0 := by
  induction groups with
  | zero => simp
  | succ groups ih =>
      have earlier := ih (by omega)
      have four : 2 * size (4 * groups + 4) ≤ size (4 * groups) :=
        quarter_decay_four (fun index small => decay (4 * groups + index) (by omega))
      calc
        2 ^ (groups + 1) * size (4 * (groups + 1)) =
            2 ^ groups * (2 * size (4 * groups + 4)) := by
              rw [show 4 * (groups + 1) = 4 * groups + 4 by omega, pow_succ]
              ring
        _ ≤ 2 ^ groups * size (4 * groups) := Nat.mul_le_mul_left _ four
        _ ≤ size 0 := earlier

/-- A nonempty block below the cutoff supports only logarithmically many
quarter-decaying requests, including the request which empties it. -/
theorem quarter_decay_steps_le {size : ℕ → ℕ} {steps cutoff : ℕ}
    (decay : ∀ index < steps, 4 * size (index + 1) ≤ 3 * size index)
    (live : ∀ index < steps, 0 < size index) (initial : size 0 ≤ cutoff) :
    steps ≤ 4 * (Nat.clog 2 cutoff + 1) := by
  by_contra tooMany
  have within : 4 * (Nat.clog 2 cutoff + 1) < steps := by omega
  have mass := quarter_decay_dyadic decay (Nat.le_of_lt within)
  have positive := live _ within
  have atLeastPower : 2 ^ (Nat.clog 2 cutoff + 1) ≤ size 0 :=
    (Nat.le_mul_of_pos_right _ positive).trans mass
  have cutoffPower := Nat.le_pow_clog (by decide : 1 < 2) cutoff
  have powerPositive : 0 < 2 ^ Nat.clog 2 cutoff := pow_pos (by decide) _
  rw [pow_succ] at atLeastPower
  omega

end Splay.Accounting
