import TangoSquared.ColoredMerge
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# First-free finite primary merging without a startup term

The cyclic merge theorem has a direct finite consequence.  Closing a
nonconstant word adds at most its existing finite alternation count.
This module does not prove any secondary-demand merge inequality.
-/

namespace TangoSquared.FiniteColoredMerge

theorem closing_edge_le_changes {α : Type*} [DecidableEq α]
    (a : α) (xs : List α) :
    edgeChange (xs.getLastD a) a ≤ changesFrom a xs := by
  induction xs generalizing a with
  | nil => simp
  | cons b bs ih =>
    have ht := edgeChange_triangle (bs.getLastD b) b a
    have hb := ih b
    rw [edgeChange_comm b a] at ht
    simp only [List.getLastD_cons, changesFrom_cons]
    omega

theorem cyclicAlternations_le_twice {α : Type*} [DecidableEq α]
    (xs : List α) : cyclicAlternations xs ≤ 2 * alternations xs := by
  cases xs with
  | nil => rfl
  | cons a as =>
    have hc := closing_edge_le_changes a as
    simp only [cyclicAlternations, changesFrom_cons, alternations]
    omega

theorem cyclicPrimary_le_twice (h : Nat) (xs : List Primary.Key) :
    cyclicPrimary h xs ≤ 2 * primaryCount h xs := by
  unfold cyclicPrimary primaryCount primaryAlternations
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun _ _ => cyclicAlternations_le_twice _

open ColoredMerge

/-- Occurrence colors can overlap in their key supports.  The ordinary
first-local-occurrence-free count needs no initialization allowance. -/
theorem primaryCount_merge (h : Nat) (xs : List ColoredKey)
    (hx : UniformHeight h xs) :
    primaryCount h (xs.map Prod.snd) ≤
      6 * (primaryCount h ((colorFilter false xs).map Prod.snd) +
        primaryCount h ((colorFilter true xs).map Prod.snd)) + xs.length := by
  have hfinite := primary_le_cyclic h (xs.map Prod.snd)
  have hmerge := cyclicPrimary_merge_length h xs hx
  have hzero := cyclicPrimary_le_twice h ((colorFilter false xs).map Prod.snd)
  have hone := cyclicPrimary_le_twice h ((colorFilter true xs).map Prod.snd)
  omega

end TangoSquared.FiniteColoredMerge
