import Splay.Lazy.SafeInsert
import Splay.Lazy.ValueAdjustmentCost

namespace Splay.Lazy.State

@[simp] theorem safeInsertEvents_totalInserts {n : ℕ} (state : State n)
    (blockId : Interface.BlockId) (block : Block n) (element : Interface.Element n) :
    Interface.totalInserts (eraseOperations (state.safeInsertEvents blockId block element)) = 1 := by
  simp only [safeInsertEvents, eraseOperations_append, Interface.totalInserts_append,
    totalInserts_adjustValueEvents]
  rfl

@[simp] theorem safeInsertEvents_totalActivity {n : ℕ} (state : State n)
    (blockId : Interface.BlockId) (block : Block n) (element : Interface.Element n) :
    Interface.totalActivity (eraseOperations (state.safeInsertEvents blockId block element)) = 0 := by
  simp only [safeInsertEvents, eraseOperations_append, Interface.totalActivity_append,
    totalActivity_adjustValueEvents]
  rfl

@[simp] theorem safeInsertEvents_totalBlockGrowth {n : ℕ} (state : State n)
    (blockId : Interface.BlockId) (block : Block n) (element : Interface.Element n) :
    Interface.totalBlockGrowth (eraseOperations (state.safeInsertEvents blockId block element)) = 0 := by
  simp only [safeInsertEvents, eraseOperations_append, Interface.totalBlockGrowth_append,
    totalBlockGrowth_adjustValueEvents]
  rfl

/-- All unit increases, including creator restoration, fit three gap bounds. -/
theorem safeInsertEvents_totalIncreases_le {n : ℕ} {params : Interface.Parameters}
    (state : State n) (blockId : Interface.BlockId) (block : Block n)
    (element : Interface.Element n) (valid : state.Valid params) :
    Interface.totalIncreases (eraseOperations (state.safeInsertEvents blockId block element)) ≤
      3 * params.valueBound := by
  have creatorPositive := (valid.toInterface.2.1 block.creator).1
  have creatorBound := (valid.toInterface.2.1 block.creator).2
  have elementBound := (valid.toInterface.2.1 element).2
  change 1 ≤ state.value block.creator at creatorPositive
  change state.value block.creator ≤ params.valueBound at creatorBound
  change state.value element ≤ params.valueBound at elementBound
  have boundPositive := params.valueBound_ge_two
  simp only [safeInsertEvents, eraseOperations_append, Interface.totalIncreases_append,
    totalIncreases_adjustValueEvents]
  have noCreatorIncrease : 1 - state.value block.creator = 0 := by omega
  rw [noCreatorIncrease]
  change 0 + (2 - _) + 0 + (state.value element - _) + (state.value block.creator - _) ≤ _
  omega

end Splay.Lazy.State
