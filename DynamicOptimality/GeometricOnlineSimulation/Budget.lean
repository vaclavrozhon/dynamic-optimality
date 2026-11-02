import DynamicOptimality.GeometricOnlineSimulation.DyadicCut
import DynamicOptimality.GeometricOnlineSimulation.LogBudget

/-!
# Combining split-tree credits

The three terms pay respectively for expanding perfect blocks, transferring
whole blocks from the smaller component, and persistent deque imbalance.
This file is accounting only; the physical split lemmas supply its explicit
rotation-count premise.
-/

namespace DynamicOptimality.GeometricOnlineSimulation

theorem Dyadic.Mountain.prefix {before after : List Nat}
    (mountain : Mountain (before ++ after)) : Mountain before := by
  cases after with
  | nil => simpa only [List.append_nil] using mountain
  | cons level rest => exact mountain.left_segment

theorem Dyadic.Mountain.suffix {before after : List Nat}
    (mountain : Mountain (before ++ after)) : Mountain after := by
  induction before with
  | nil => exact mountain
  | cons level rest ih =>
      have next : Mountain ([] ++ level :: (rest ++ after)) := mountain
      exact ih next.right_segment

def blockBudget (levels : List Nat) (size imbalance : Nat) : Nat :=
  100 * Dyadic.credit levels + 40 * logarithmicCredit size + imbalance

theorem blockBudget_initial {levels : List Nat} {size imbalance : Nat}
    (blocks : Dyadic.credit levels ≤ size) (queue : imbalance ≤ 4 * size) :
    blockBudget levels size imbalance ≤ 184 * size := by
  have logarithm := logarithmicCredit_le size
  unfold blockBudget
  omega

theorem blockBudget_split {before left right : List Nat}
    {leftSize rightSize beforeQueue leftQueue rightQueue expanded count : Nat}
    (blocks : Dyadic.credit left + Dyadic.credit right + expanded = Dyadic.credit before)
    (physical : count + leftQueue + rightQueue ≤ beforeQueue + 100 * expanded +
      40 * (Nat.log 2 (min (leftSize + 1) (rightSize + 1)) + 1)) :
    count + blockBudget left leftSize leftQueue + blockBudget right rightSize rightQueue ≤
      blockBudget before (leftSize + rightSize + 1) beforeQueue := by
  have logarithm := logarithmicCredit_step leftSize rightSize
  unfold blockBudget
  omega

theorem separator_transfer_bound {left right : List Nat} {leftCount rightCount : Nat}
    (mountain : Dyadic.Mountain (left ++ right))
    (leftLength : left.length = leftCount + 1) (rightLength : right.length = rightCount + 1) :
    20 * (min leftCount rightCount + 1) ≤
      40 * (Nat.log 2 (min (Dyadic.weight left) (Dyadic.weight right)) + 1) := by
  rcases le_total (Dyadic.weight left) (Dyadic.weight right) with smaller | smaller
  · rw [min_eq_left smaller]
    have bound := mountain.prefix.length_le_log
    have selected := Nat.min_le_left leftCount rightCount
    omega
  · rw [min_eq_right smaller]
    have bound := mountain.suffix.length_le_log
    have selected := Nat.min_le_right leftCount rightCount
    omega

end DynamicOptimality.GeometricOnlineSimulation
