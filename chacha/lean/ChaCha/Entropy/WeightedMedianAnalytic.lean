import ChaCha.Entropy.Histogram
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Entropy paid by a weighted-median split

All logarithms in this module are natural logarithms. A ternary split
has entropy at most its total weight times log(3). If its two outer
weights are at most half the total, the binary split isolating the larger
outer part pays at least half the total non-pivot weight.
-/

namespace ChaCha.Entropy

theorem log_three_nonnegative : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)

theorem entropy_tangent {part total : ℝ} (partNonnegative : 0 ≤ part) (totalPositive : 0 < total) :
    part*Real.log total-part*Real.log part ≤ part*Real.log 3+total/3-part := by
  by_cases zero : part = 0
  · subst part
    simp only [zero_mul,sub_self,zero_add,sub_zero]
    positivity
  · have positive : 0 < part := lt_of_le_of_ne partNonnegative (Ne.symm zero)
    have divisor : 0 < 3*part := by positivity
    have logarithm := Real.log_le_sub_one_of_pos (div_pos totalPositive divisor)
    rw [Real.log_div (ne_of_gt totalPositive) (ne_of_gt divisor),
      Real.log_mul (by norm_num : (3:ℝ) ≠ 0) zero] at logarithm
    have paid := mul_le_mul_of_nonneg_left logarithm partNonnegative
    have fraction : part*(total/(3*part)) = total/3 := by field_simp
    simp only [mul_sub,mul_one,fraction] at paid
    nlinarith

theorem ternary_entropy_le {left pivot right : ℝ}
    (leftNonnegative : 0 ≤ left) (pivotPositive : 0 < pivot) (rightNonnegative : 0 ≤ right) :
    (left+pivot+right)*Real.log (left+pivot+right) -
      left*Real.log left-pivot*Real.log pivot-right*Real.log right ≤
        (left+pivot+right)*Real.log 3 := by
  have total : 0 < left+pivot+right := by linarith
  have a := entropy_tangent leftNonnegative total
  have b := entropy_tangent (le_of_lt pivotPositive) total
  have c := entropy_tangent rightNonnegative total
  nlinarith

theorem binary_toll_nonnegative {left right : ℝ} (a : 0 ≤ left) (b : 0 ≤ right) :
    0 ≤ 2*left*right/(left+right) := by positivity

theorem smaller_side_paid {left right : ℝ} (leftNonnegative : 0 ≤ left)
    (rightPositive : 0 < right) (smaller : left ≤ right) :
    left ≤ 2*left*right/(left+right) := by
  apply (le_div_iff₀ (by positivity : 0 < left+right)).mpr
  nlinarith

theorem median_left_charge {left pivot right : ℝ}
    (leftNonnegative : 0 ≤ left) (pivotPositive : 0 < pivot) (rightNonnegative : 0 ≤ right)
    (median : 2*left ≤ left+pivot+right) (larger : right ≤ left) :
    left+pivot+right ≤ 2*(2*left*(pivot+right)/(left+(pivot+right)))+pivot := by
  have paid := smaller_side_paid leftNonnegative
    (show 0 < pivot+right by linarith) (show left ≤ pivot+right by linarith)
  linarith

theorem median_right_charge {left pivot right : ℝ}
    (leftNonnegative : 0 ≤ left) (pivotPositive : 0 < pivot) (rightNonnegative : 0 ≤ right)
    (median : 2*right ≤ left+pivot+right) (larger : left ≤ right) :
    left+pivot+right ≤ 2*(2*(left+pivot)*right/((left+pivot)+right))+pivot := by
  have paid := smaller_side_paid rightNonnegative
    (show 0 < left+pivot by linarith) (show right ≤ left+pivot by linarith)
  have same : 2*right*(left+pivot)/(right+(left+pivot)) =
      2*(left+pivot)*right/((left+pivot)+right) := by ring
  rw [same] at paid
  linarith

theorem entropyMass_split (f : Int → Nat) (left : List Int) (pivot : Int) (right : List Int) :
    entropyMass f (left++pivot::right) = entropyMass f left+entropyMass f right+
      (((weight f left:ℝ)+(f pivot:ℝ)+(weight f right:ℝ))*
        Real.log ((weight f left:ℝ)+(f pivot:ℝ)+(weight f right:ℝ))-
        (weight f left:ℝ)*Real.log (weight f left:ℝ)-
        (f pivot:ℝ)*Real.log (f pivot:ℝ)-(weight f right:ℝ)*Real.log (weight f right:ℝ)) := by
  simp only [entropyMass,weight_append,weight_cons,Nat.cast_add,List.map_append,List.sum_append,
    List.map_cons,List.sum_cons]
  rw [show (weight f left:ℝ)+((f pivot:ℝ)+(weight f right:ℝ)) =
    (weight f left:ℝ)+(f pivot:ℝ)+(weight f right:ℝ) by ring]
  ring

end ChaCha.Entropy
