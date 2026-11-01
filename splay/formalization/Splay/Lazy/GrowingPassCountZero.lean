import Splay.Lazy.Trace
import Splay.Interface.PassCountHistory

namespace Splay.Lazy

/-- The interface's growing-counter invariant also controls the exact rich
blocks, because mode and pass count are retained by projection. -/
theorem Trace.growingPassCountZero {n : ℕ} {params : Interface.Parameters}
    {before after : State n} {events : List (Event n)} (trace : Trace params before events after)
    (zero : Interface.GrowingPassCountZero before.toInterface) :
    Interface.GrowingPassCountZero after.toInterface := by
  obtain ⟨labels, history⟩ := Interface.HistoryTrace.lift trace.toInterface []
  exact history.preserveGrowingPassCountZero zero

theorem State.shrinking_of_passCount_ne_zero {n : ℕ} {state : State n}
    (zero : Interface.GrowingPassCountZero state.toInterface) {id : Interface.BlockId} {block : Block n}
    (found : state.blocks[id]? = some block) (positive : block.passCount ≠ 0) : block.mode = .shrinking := by
  cases mode : block.mode with
  | shrinking => rfl
  | growing =>
    have interfaceFound : state.toInterface.block? id = some block.toInterface := by
      simpa [State.toInterface, Interface.State.block?] using congrArg (Option.map Block.toInterface) found
    exact (positive (zero id block.toInterface interfaceFound mode)).elim

end Splay.Lazy
