import Splay.Lazy.ValueTrace
import Splay.Interface.OperationCounts

namespace Splay.Lazy.State

theorem totalIncreases_adjustValueEvents {n : ℕ} (state : State n)
    (element : Interface.Element n) (target : ℕ) :
    Interface.totalIncreases (eraseOperations (state.adjustValueEvents element target)) =
      target - state.value element := by
  rw [eraseOperations_adjustValueEvents]
  split <;> simp_all [Interface.totalIncreases, Interface.Operation.increaseCount]

theorem totalIncreases_adjustValueEvents_le {n : ℕ} (state : State n)
    (element : Interface.Element n) (target : ℕ) :
    Interface.totalIncreases (eraseOperations (state.adjustValueEvents element target)) ≤ target := by
  rw [totalIncreases_adjustValueEvents]
  exact Nat.sub_le _ _

@[simp] theorem totalActivity_adjustValueEvents {n : ℕ} (state : State n)
    (element : Interface.Element n) (target : ℕ) :
    Interface.totalActivity (eraseOperations (state.adjustValueEvents element target)) = 0 := by
  rw [eraseOperations_adjustValueEvents]
  split <;> simp [Interface.totalActivity, Interface.Operation.activity]

@[simp] theorem totalBlockGrowth_adjustValueEvents {n : ℕ} (state : State n)
    (element : Interface.Element n) (target : ℕ) :
    Interface.totalBlockGrowth (eraseOperations (state.adjustValueEvents element target)) = 0 := by
  rw [eraseOperations_adjustValueEvents]
  split <;> simp [Interface.totalBlockGrowth, Interface.Operation.blockGrowth]

end Splay.Lazy.State
