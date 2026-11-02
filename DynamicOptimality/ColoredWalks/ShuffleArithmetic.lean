import DynamicOptimality.MultiFinger.SimulationBound
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-! Elementary estimates used after the actual BST construction. -/

namespace DynamicOptimality.ColoredWalks

open MultiFinger

theorem logarithmicFactor_pos (count : Nat) : 0 < logarithmicFactor count := by
  unfold logarithmicFactor
  omega

theorem logarithmicFactor_mono : Monotone logarithmicFactor := by
  intro first last order
  exact Nat.add_le_add_left (Nat.log_mono_right (Nat.add_le_add_right order 1)) 1

theorem embedding_height_le (count : Nat) :
    Nat.clog 2 (2*count+1) ≤ 2*logarithmicFactor count := by
  have power := Nat.lt_pow_succ_log_self (by decide : 1<2) (count+1)
  have upper : Nat.clog 2 (2*count+1) ≤ Nat.log 2 (count+1)+2 := by
    apply Nat.clog_le_of_le_pow
    rw [show Nat.log 2 (count+1)+2 = (Nat.log 2 (count+1)+1)+1 by omega, pow_succ]
    omega
  unfold logarithmicFactor
  omega

theorem shuffle_budget {length size count colors fingerCost : Nat}
    (sizeBound : size ≤ length) (countBound : count ≤ length) (colorsBound : count ≤ colors)
    (fingerBound : fingerCost ≤ length*(4*Nat.clog 2 (2*count+1)+1)) :
    (fingerCost+count)*logarithmicFactor count+size ≤
      11*length*(logarithmicFactor colors)^2 := by
  let factor := logarithmicFactor colors
  have positive : 1 ≤ factor := logarithmicFactor_pos colors
  have mono : logarithmicFactor count ≤ factor := logarithmicFactor_mono colorsBound
  have height : Nat.clog 2 (2*count+1) ≤ 2*factor :=
    (embedding_height_le count).trans (Nat.mul_le_mul_left 2 mono)
  have front : fingerCost+count ≤ length*(8*factor+2) := by nlinarith
  have product := Nat.mul_le_mul front mono
  have scalar : (8*factor+2)*factor+1 ≤ 11*factor^2 := by nlinarith
  have scaled := Nat.mul_le_mul_left length scalar
  nlinarith

end DynamicOptimality.ColoredWalks
