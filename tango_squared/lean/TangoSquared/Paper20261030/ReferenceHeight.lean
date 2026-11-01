import TangoSquared.Paper20261030.SecondaryReference
import Mathlib.Data.Nat.Log

/-!
# Height of the actual midpoint secondary reference

The leaf interval `[a,b]` has `b+1-a` labels. Its midpoint tree has height
at most the ceiling of the binary logarithm of that number. Completion
adds one level, and every local suffix restriction preserves the bound.
-/

namespace TangoSquared.Paper20261030.LocalReferences

open RouterProjection

theorem midpoint_height_power (k a b : Nat) (hab : a ≤ b)
    (hwidth : b + 1 - a ≤ 2 ^ k) :
    (depthReference (DepthTree.midpoint a b hab)).height ≤ k := by
  induction k generalizing a b with
  | zero =>
    have heq : a = b := by simp only [pow_zero] at hwidth; omega
    subst b
    simp [DepthTree.midpoint,depthReference,Router.height]
  | succ k ih =>
    by_cases heq : a = b
    · subst b
      simp [DepthTree.midpoint,depthReference,Router.height]
    · have hp : 0 < 2 ^ k := Nat.two_pow_pos k
      have hl : (a + b) / 2 + 1 - a ≤ 2 ^ k := by
        rw [pow_succ] at hwidth
        omega
      have hr : b + 1 - ((a + b) / 2 + 1) ≤ 2 ^ k := by
        rw [pow_succ] at hwidth
        omega
      have il := ih a ((a + b) / 2) (by omega) hl
      have ir := ih ((a + b) / 2 + 1) b (by omega) hr
      rw [DepthTree.midpoint,dif_neg heq]
      simp only [depthReference,Router.height]
      omega

theorem midpoint_height_log (a b : Nat) (hab : a ≤ b) :
    (depthReference (DepthTree.midpoint a b hab)).height ≤ Nat.clog 2 (b + 1 - a) :=
  midpoint_height_power _ a b hab (Nat.le_pow_clog (by decide) _)

theorem completed_midpoint_height (h : Nat) :
    (completedReference (DepthTree.midpoint 0 h (Nat.zero_le h))).height ≤
      Nat.clog 2 (h + 1) + 1 := by
  have hm := midpoint_height_log 0 h (Nat.zero_le h)
  simpa [completedReference,Router.height] using Nat.add_le_add_right hm 1

theorem restricted_midpoint_height (h : Nat) (keep : Nat → Bool) :
    (Router.prune keep (completedReference (DepthTree.midpoint 0 h (Nat.zero_le h)))).height ≤
      Nat.clog 2 (h + 1) + 1 :=
  (Router.height_prune_le _ _).trans (completed_midpoint_height h)

end TangoSquared.Paper20261030.LocalReferences
