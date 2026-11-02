import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-!
# The logarithmic smaller-component budget

An `n`-key component has `n + 1` external gaps. Splitting at a key replaces
one component by two whose numbers of gaps add to the old number. The
credit `2*n - log₂(n+1)` pays `1 + log₂(min(left+1,right+1))` for every cut.
The lower integer logarithm is used throughout, including empty components.
-/

namespace DynamicOptimality.GeometricOnlineSimulation

theorem log_sum_bound {a b : Nat} (ordered : a ≤ b) (positive : 0 < b) :
    Nat.log 2 (a + b) ≤ Nat.log 2 b + 1 := by
  have monotone : Nat.log 2 (a + b) ≤ Nat.log 2 (b * 2) :=
    Nat.log_mono_right (by omega)
  simpa only [Nat.log_mul_base (b := 2) (n := b) (by decide) (by omega)] using monotone

theorem log_fragmentation_step (left right : Nat) :
    Nat.log 2 (min (left + 1) (right + 1)) + Nat.log 2 (left + right + 2) ≤
      Nat.log 2 (left + 1) + Nat.log 2 (right + 1) + 1 := by
  rcases le_total left right with ordered | ordered
  · have bound := log_sum_bound (a := left + 1) (b := right + 1) (by omega) (by omega)
    rw [min_eq_left (by omega : left + 1 ≤ right + 1)]
    have same : left + 1 + (right + 1) = left + right + 2 := by omega
    rw [same] at bound
    omega
  · have bound := log_sum_bound (a := right + 1) (b := left + 1) (by omega) (by omega)
    rw [min_eq_right (by omega : right + 1 ≤ left + 1)]
    have same : right + 1 + (left + 1) = left + right + 2 := by omega
    rw [same] at bound
    omega

def logarithmicCredit (size : Nat) : Nat := 2 * size - Nat.log 2 (size + 1)

theorem logarithmicCredit_exact (size : Nat) :
    logarithmicCredit size + Nat.log 2 (size + 1) = 2 * size := by
  have bounded := Nat.log_lt_self (b := 2) (by omega : size + 1 ≠ 0)
  simp only [logarithmicCredit]
  omega

@[simp] theorem logarithmicCredit_zero : logarithmicCredit 0 = 0 := by decide

theorem logarithmicCredit_le (size : Nat) : logarithmicCredit size ≤ 2 * size :=
  Nat.sub_le _ _

theorem logarithmicCredit_step (left right : Nat) :
    1 + Nat.log 2 (min (left + 1) (right + 1)) +
        logarithmicCredit left + logarithmicCredit right ≤
      logarithmicCredit (left + right + 1) := by
  have roots := log_fragmentation_step left right
  have before := logarithmicCredit_exact (left + right + 1)
  have afterLeft := logarithmicCredit_exact left
  have afterRight := logarithmicCredit_exact right
  have same : left + right + 1 + 1 = left + right + 2 := by omega
  rw [same] at before
  omega

end DynamicOptimality.GeometricOnlineSimulation
