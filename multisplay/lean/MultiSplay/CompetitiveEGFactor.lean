import MultiSplay.CompetitiveFactor
import Splay.Accounting.IteratedLogEGBound

/-!
# The improved composed factor for classical MultiSplay

The common-forest comparison contributes the existing Splay factor at the
primary reference height. The secondary comparator contributes one additional
third iterated logarithm. This file only translates these numerical factors;
it does not assert that a particular comparator or algorithm satisfies a cost
bound. The previous `competitiveFactor` remains unchanged.
-/

namespace Splay.Analysis

theorem iteratedLog_mono (depth : Nat) : Monotone (iteratedLog depth) := by
  induction depth with
  | zero => exact fun _ _ order => order
  | succ depth ih =>
      intro a b order
      exact Nat.clog_mono_right 2 (max_le_max (Nat.le_refl 2) (ih order))

theorem egTargetFactor_mono : Monotone egTargetFactor := by
  intro a b order
  have second := iteratedLog_mono 2 order
  have third := iteratedLog_mono 3 order
  exact Nat.mul_le_mul (Nat.mul_le_mul second third)
    (LayerEnvelope.E_mono (Nat.mul_le_mul_left 24 second))

theorem egTargetFactor_pos (n : Nat) : 0 < egTargetFactor n := by
  unfold egTargetFactor
  exact Nat.mul_pos (Nat.mul_pos (iteratedLog_pos (by decide))
    (iteratedLog_pos (by decide))) (LayerEnvelope.E_pos _)

end Splay.Analysis

namespace MultiSplay

open Splay.Analysis

/-- The literal `L₃(n) * g(2 L₁(n))` factor, where `g` is the strongest
currently exported Splay factor and `Lₖ` is the stabilized binary logarithm. -/
def shiftedEGFactor (n : Nat) : Nat :=
  iteratedLog 3 n * egTargetFactor (2 * iteratedLog 1 n)

/-- An explicit expanded bound for the composed factor. The factor 48
inside the slowly growing envelope covers the balanced reference height. -/
def competitiveEGFactor (n : Nat) : Nat :=
  (iteratedLog 3 n)^2 * iteratedLog 4 n * LayerEnvelope.E (48 * iteratedLog 3 n)

theorem shiftedEGFactor_pos (n : Nat) : 0 < shiftedEGFactor n :=
  Nat.mul_pos (iteratedLog_pos (by decide)) (egTargetFactor_pos _)

theorem competitiveEGFactor_pos (n : Nat) : 0 < competitiveEGFactor n := by
  unfold competitiveEGFactor
  have third : 0 < iteratedLog 3 n := iteratedLog_pos (by decide)
  have fourth : 0 < iteratedLog 4 n := iteratedLog_pos (by decide)
  have envelope := LayerEnvelope.E_pos (48 * iteratedLog 3 n)
  exact Nat.mul_pos (Nat.mul_pos (pow_pos third 2) fourth) envelope

theorem balancedReference_splayEGFactor_le (n : Nat) :
    egTargetFactor (balancedReference n).height ≤
      4 * iteratedLog 3 n * iteratedLog 4 n * LayerEnvelope.E (48 * iteratedLog 3 n) := by
  have second : iteratedLog 2 (balancedReference n).height ≤ 2 * iteratedLog 3 n :=
    balancedReference_iteratedLog_le n 2
  have third : iteratedLog 3 (balancedReference n).height ≤ 2 * iteratedLog 4 n :=
    balancedReference_iteratedLog_le n 3
  have envelope := LayerEnvelope.E_mono
    (show 24 * iteratedLog 2 (balancedReference n).height ≤ 48 * iteratedLog 3 n by omega)
  calc
    _ ≤ (2 * iteratedLog 3 n) * (2 * iteratedLog 4 n) *
        LayerEnvelope.E (48 * iteratedLog 3 n) :=
      Nat.mul_le_mul (Nat.mul_le_mul second third) envelope
    _ = _ := by ring

/-- Direct form of the intended weaker target: the comparator factor times
the Splay factor at the balanced reference is `O(L₃(n) * g(O(log n)))`. -/
theorem balancedReference_composedEGFactor_le_shifted (n : Nat) :
    comparisonFactor (balancedReference n).height * egTargetFactor (balancedReference n).height ≤
      5 * shiftedEGFactor n := by
  have splay := egTargetFactor_mono (balancedReference_height_le_log n)
  calc
    _ ≤ (5 * iteratedLog 3 n) * egTargetFactor (2 * iteratedLog 1 n) :=
      Nat.mul_le_mul (balancedReference_comparisonFactor_le n) splay
    _ = _ := by unfold shiftedEGFactor; ring

/-- The explicit fourth-log and envelope form, uniform also at small and
empty universes. Neither the comparator factor nor the Splay factor cancels. -/
theorem balancedReference_composedEGFactor_le (n : Nat) :
    comparisonFactor (balancedReference n).height * egTargetFactor (balancedReference n).height ≤
      20 * competitiveEGFactor n := by
  calc
    _ ≤ (5 * iteratedLog 3 n) *
        (4 * iteratedLog 3 n * iteratedLog 4 n * LayerEnvelope.E (48 * iteratedLog 3 n)) :=
      Nat.mul_le_mul (balancedReference_comparisonFactor_le n)
        (balancedReference_splayEGFactor_le n)
    _ = _ := by unfold competitiveEGFactor; ring

end MultiSplay
