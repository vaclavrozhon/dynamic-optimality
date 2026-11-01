import Mathlib

/-! Scalar arithmetic for relabeling an original strict interface by the
logarithm of its immutable historical ranks. The chronology and incidence
budgets are separate modules; no activity conclusion is assumed here. -/

namespace Splay.Research.HistoricalRankCompression

noncomputable section

def label (rank : ℝ) : ℤ := ⌊16 * Real.log (1+rank)⌋ + 1

def rise (before after : ℝ) : ℝ := max 0 ((label after:ℝ)-label before)

def fall (before after : ℝ) : ℝ := rise after before

def preparation (winner loser : ℝ) : ℝ := max 0 ((label winner:ℝ)+1-label loser)

theorem label_bounds (rank : ℝ) :
    16*Real.log (1+rank) < (label rank:ℝ) ∧
      (label rank:ℝ) ≤ 16*Real.log (1+rank)+1 := by
  have lower := Int.lt_floor_add_one (16*Real.log (1+rank))
  have upper := Int.floor_le (16*Real.log (1+rank))
  simp only [label, Int.cast_add, Int.cast_one]
  constructor <;> linarith

theorem label_positive {rank : ℝ} (nonnegative : 0 ≤ rank) : 1 ≤ label rank := by
  have logarithm := Real.log_nonneg (show 1 ≤ 1+rank by linarith)
  have floor := Int.floor_nonneg.mpr (mul_nonneg (by norm_num : (0:ℝ) ≤ 16) logarithm)
  unfold label
  omega

theorem label_monotone {first second : ℝ} (nonnegative : 0 ≤ first)
    (order : first ≤ second) : label first ≤ label second := by
  have logarithm := Real.log_le_log (by linarith : 0 < 1+first)
    (show 1+first ≤ 1+second by linarith)
  unfold label
  have floors := Int.floor_mono (by nlinarith :
    16*Real.log (1+first) ≤ 16*Real.log (1+second))
  omega

theorem log_increment_le {first second : ℝ} (nonnegative : 0 ≤ first)
    (order : first ≤ second) :
    Real.log (1+second)-Real.log (1+first) ≤ second-first := by
  have firstPositive : 0 < 1+first := by linarith
  have secondPositive : 0 < 1+second := by linarith
  have bound := Real.log_le_sub_one_of_pos (div_pos secondPositive firstPositive)
  rw [Real.log_div (ne_of_gt secondPositive) (ne_of_gt firstPositive)] at bound
  have rational : (1+second)/(1+first)-1 ≤ second-first := by
    have fraction : (1+second)/(1+first) ≤ second-first+1 := by
      apply (div_le_iff₀ firstPositive).mpr
      nlinarith [mul_nonneg nonnegative (sub_nonneg.mpr order)]
    linarith
  linarith

theorem log_difference_lower {first second bound : ℝ}
    (firstPositive : 0 < 1+first) (secondPositive : 0 < 1+second)
    (rational : bound ≤ 1-(1+second)/(1+first)) :
    bound ≤ Real.log (1+first)-Real.log (1+second) := by
  have lower := Real.one_sub_inv_le_log_of_pos (div_pos firstPositive secondPositive)
  rw [inv_div, Real.log_div (ne_of_gt firstPositive) (ne_of_gt secondPositive)] at lower
  exact rational.trans lower

/-- Rounding adds no unconditional charge per link: a positive historical
rise requires error exceeding the winner's rank, which is at least one. -/
theorem positive_relabel_bound {a old b error charge : ℝ}
    (winner : 1 ≤ a) (oldNonnegative : 0 ≤ old) (newNonnegative : 0 ≤ b)
    (identity : b = old-a+error) (chargeNonnegative : 0 ≤ charge)
    (charged : error ≤ charge) : rise old b ≤ 17*charge := by
  by_cases order : b ≤ old
  · have labels := label_monotone newNonnegative order
    have castLabels : (label b:ℝ) ≤ label old := by exact_mod_cast labels
    rw [rise, max_eq_left (by linarith)]
    positivity
  · have growth : old ≤ b := by linarith
    have logarithm := log_increment_le oldNonnegative growth
    have first := label_bounds old
    have second := label_bounds b
    have chargeLarge : 1 ≤ charge := by linarith
    unfold rise
    apply max_le
    · positivity
    · nlinarith

theorem good_preparation_bound {a old b error : ℝ}
    (winner : 1 ≤ a) (newNonnegative : 0 ≤ b)
    (identity : b = old-a+error) (good : error ≤ a/2) :
    preparation a old ≤ 18 := by
  have oldPositive : 0 < 1+old := by linarith
  have winnerPositive : 0 < 1+a := by linarith
  have argument : 1+a ≤ 2*(1+old) := by linarith
  have logarithm := Real.log_le_log winnerPositive argument
  rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (ne_of_gt oldPositive)] at logarithm
  have logTwo : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
    norm_num at h ⊢
    exact h
  have first := label_bounds a
  have second := label_bounds old
  unfold preparation
  apply max_le <;> linarith

theorem moderate_fall {a old b error : ℝ}
    (winner : 1 ≤ a) (newNonnegative : 0 ≤ b)
    (identity : b = old-a+error) (good : error ≤ a/2) (moderate : b ≤ 2*a) :
    1 ≤ fall old b := by
  have oldPositive : 0 < 1+old := by linarith
  have newPositive : 0 < 1+b := by linarith
  have rational : (1:ℝ)/7 ≤ 1-(1+b)/(1+old) := by
    have fraction : (1+b)/(1+old) ≤ 6/7 := by
      apply (div_le_iff₀ oldPositive).mpr
      nlinarith
    linarith
  have logarithm := log_difference_lower oldPositive newPositive rational
  have first := label_bounds old
  have second := label_bounds b
  have difference : 1 ≤ (label old:ℝ)-label b := by linarith
  exact difference.trans (le_max_right _ _)

theorem large_needs_no_preparation {a old b error : ℝ}
    (winner : 1 ≤ a) (newNonnegative : 0 ≤ b)
    (identity : b = old-a+error) (good : error ≤ a/2) (large : 2*a < b) :
    preparation a old = 0 := by
  have oldPositive : 0 < 1+old := by linarith
  have winnerPositive : 0 < 1+a := by linarith
  have rational : (1:ℝ)/3 ≤ 1-(1+a)/(1+old) := by
    have fraction : (1+a)/(1+old) ≤ 2/3 := by
      apply (div_le_iff₀ oldPositive).mpr
      nlinarith
    linarith
  have logarithm := log_difference_lower oldPositive winnerPositive rational
  have first := label_bounds old
  have second := label_bounds a
  unfold preparation
  apply max_eq_left
  linarith

theorem bad_preparation_bound {a old b error charge : ℝ}
    (winner : 1 ≤ a) (oldNonnegative : 0 ≤ old) (newNonnegative : 0 ≤ b)
    (identity : b = old-a+error) (bad : a/2 < error) (charged : error ≤ charge) :
    preparation a old ≤ 20*charge := by
  have chargeLarge : 1/2 < charge := by linarith
  have first := label_bounds a
  have second := label_bounds old
  by_cases order : a ≤ old
  · have labels := label_monotone (by linarith : 0 ≤ a) order
    have castLabels : (label a:ℝ) ≤ label old := by exact_mod_cast labels
    unfold preparation
    apply max_le <;> linarith
  · have logarithm := log_increment_le oldNonnegative (by linarith : old ≤ a)
    unfold preparation
    apply max_le <;> nlinarith

/-- Every rounding/strictness repair is charged either to an actual
decrease of the compressed losing rank or to the original temporal error. -/
theorem preparation_bound {a old b error charge : ℝ}
    (winner : 1 ≤ a) (oldNonnegative : 0 ≤ old) (newNonnegative : 0 ≤ b)
    (identity : b = old-a+error) (chargeNonnegative : 0 ≤ charge)
    (charged : error ≤ charge) :
    preparation a old ≤ 18*fall old b + 20*charge := by
  have fallNonnegative : 0 ≤ fall old b := le_max_left _ _
  by_cases good : error ≤ a/2
  · by_cases moderate : b ≤ 2*a
    · have prep := good_preparation_bound winner newNonnegative identity good
      have drop := moderate_fall winner newNonnegative identity good moderate
      nlinarith
    · rw [large_needs_no_preparation winner newNonnegative identity good (by linarith)]
      positivity
  · have prep := bad_preparation_bound winner oldNonnegative newNonnegative identity
      (by linarith) charged
    nlinarith

def natLabel (rank : ℕ) : ℕ := (label (rank:ℝ)).toNat

theorem natLabel_cast (rank : ℕ) : (natLabel rank : ℤ) = label (rank:ℝ) := by
  exact Int.toNat_of_nonneg (by have := label_positive (Nat.cast_nonneg rank); omega)

theorem natLabel_positive (rank : ℕ) : 1 ≤ natLabel rank := by
  have positive := label_positive (Nat.cast_nonneg rank)
  rw [← natLabel_cast] at positive
  exact_mod_cast positive

theorem natLabel_monotone {first second : ℕ} (order : first ≤ second) :
    natLabel first ≤ natLabel second := by
  have bound := label_monotone (Nat.cast_nonneg first)
    (show (first : ℝ) ≤ (second : ℝ) by exact_mod_cast order)
  rw [← natLabel_cast first, ← natLabel_cast second] at bound
  exact_mod_cast bound

theorem natLabel_real_cast (rank : ℕ) : (natLabel rank : ℝ) = label (rank:ℝ) := by
  exact_mod_cast natLabel_cast rank

#print axioms positive_relabel_bound
#print axioms preparation_bound

end
end Splay.Research.HistoricalRankCompression
