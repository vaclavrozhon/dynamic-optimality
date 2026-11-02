import DynamicOptimality.MultiFinger.StateRun
import Mathlib.Data.Nat.Log

/-! # Actual logarithmic simulation of static persistent fingers

The construction retains the reference's exact original keys, initializes
its compressed physical hand once, and executes every finger movement
and service with persistent queues. The final theorem discharges the
`SimulationBound` interface with one uniform numerical constant.
-/

namespace DynamicOptimality.MultiFinger

open ChaCha.MTR

theorem topCapacity_log (fingers : Nat) :
    Nat.log 2 (topCapacity fingers+4) ≤ Nat.log 2 (fingers+1)+5 := by
  have power := Nat.lt_pow_succ_log_self (by decide : 1<2) (fingers+1)
  have scaled := Nat.mul_lt_mul_of_pos_left power (by decide : 0<32)
  have identity : 32*2^(Nat.log 2 (fingers+1)+1) = 2^(Nat.log 2 (fingers+1)+6) := by
    rw [show Nat.log 2 (fingers+1)+6 = (Nat.log 2 (fingers+1)+1)+5 by omega]
    norm_num [pow_add]
    omega
  have bound : topCapacity fingers+4 < 2^(Nat.log 2 (fingers+1)+6) := by
    rw [← identity]
    unfold topCapacity
    omega
  have logarithm := Nat.log_lt_of_lt_pow' (by omega : Nat.log 2 (fingers+1)+6 ≠ 0) bound
  omega

theorem operationAllowance_le (fingers : Nat) :
    operationAllowance fingers ≤ 412*logarithmicFactor fingers := by
  have bound := topCapacity_log fingers
  unfold operationAllowance logarithmicFactor
  omega

theorem startup_credit_le {fingers size credit : Nat} (positive : 0<fingers)
    (bound : credit ≤ 20*(fingers+1)*Nat.log 2 (10*(fingers+1))+4*size) :
    credit ≤ 200*fingers*logarithmicFactor fingers+4*size := by
  have first : Nat.log 2 (10*(fingers+1)) ≤ Nat.log 2 (topCapacity fingers+4) :=
    Nat.log_mono_right (by unfold topCapacity; omega)
  have second := topCapacity_log fingers
  have logarithm : Nat.log 2 (10*(fingers+1)) ≤ 5*logarithmicFactor fingers := by
    unfold logarithmicFactor
    omega
  have count : fingers+1 ≤ 2*fingers := by omega
  have product := Nat.mul_le_mul count logarithm
  nlinarith

/-- Unconditional simulation by actual searches and ordinary rotations. -/
theorem simulationBound : SimulationBound 1024 := by
  intro reference fingers initial final word fingerCost ordered positive live run
  have distinct : reference.inorder.Nodup := ordered.imp (fun less => ne_of_lt less)
  obtain ⟨state,initialCredit⟩ := initial.initialize_state distinct
  obtain ⟨last,total,trace,paid⟩ := run.simulate ordered live state
  have sourceOrdered : initial.hand.source.Ordered := by rw [initial.hand_source]; exact ordered
  obtain ⟨after,cost,search,searchPaid⟩ := trace.to_search (state.ordered sourceOrdered)
  refine ⟨state.tree,after,cost,state.ordered sourceOrdered,?_,search,?_⟩
  · rw [state.word,initial.hand_source]
  · have startup := startup_credit_le positive initialCredit
    have unit := operationAllowance_le fingers
    have operations := Nat.mul_le_mul_left fingerCost unit
    nlinarith

end DynamicOptimality.MultiFinger
