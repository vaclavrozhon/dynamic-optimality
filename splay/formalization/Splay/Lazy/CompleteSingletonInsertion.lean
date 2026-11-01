import Splay.Lazy.CompleteExcept
import Splay.Lazy.SingletonInsertion

namespace Splay.Lazy.State

/-- Inserting and immediately converting the sole detached non-root
element completes a canonical checkpoint. Full child segments ensure that
reattaching it cannot interrupt any surrounding interval. -/
theorem insertSingleton_stable_of_completeExcept {n : ℕ} {params : Interface.Parameters} {state : State n}
    (valid : state.Valid params) (ordered : state.view.HeapOrdered)
    (one : state.OneGrowingPerSide) (topmost : state.GrowingTopmost) (values : state.ValuesRealizeGaps)
    (element : Element n) (complete : state.CompleteExcept element) (elementOne : state.value element = 1)
    {id : Interface.BlockId} {block : Block n} (found : state.blocks[id]? = some block)
    (growing : block.mode = .growing) (empty : block.elements = [])
    (parent : state.view.parent element = some block.owner) (side : state.view.side element = block.side)
    (fullSegments : ∀ current ∈ state.blocks, IsSegment current.elements (state.view.topDown current.owner current.side)) :
    Trace params state (state.insertSingletonEvents id block element) (state.insertSingleton id block element) ∧
      (state.insertSingleton id block element).Stable params := by
  have unassigned : element ∉ state.allElements := by rw [complete element]; simp
  have parented : state.view.parent element ≠ none := by rw [parent]; simp
  have insertedComplete := complete.insert parented found
  have attachedFull (owner : Element n) (childSide : Side) :
      state.view.attachedTopDown (state.insert id element).allElements owner childSide = state.view.topDown owner childSide :=
    insertedComplete.attachedTopDown_eq_topDown owner childSide
  have afterSegment : IsSegment (block.inserted element).elements
      (state.view.attachedTopDown (state.insert id element).allElements block.owner block.side) := by
    rw [attachedFull]
    have inside := state.view.mem_topDown_iff.mpr ⟨parent, side⟩
    obtain ⟨front, back, decomposition⟩ := List.mem_iff_append.mp inside
    refine ⟨front, back, ?_⟩
    simpa [Block.inserted, empty] using decomposition
  have otherValid : ∀ otherId : Fin state.blocks.length, id ≠ otherId.val →
      (state.blocks.get otherId).StructurallyValid state.view (state.insert id element).allElements := by
    intro otherId _different
    have member := List.get_mem state.blocks otherId
    have old := valid.2 _ member
    exact ⟨by rw [attachedFull]; exact fullSegments _ member, old.2⟩
  have gapNonnegative := le_of_lt (state.view.rawGap_pos_of_heapOrdered ordered parent)
  have insertedTrace := state.safeInsert_trace id block element valid found growing unassigned gapNonnegative afterSegment otherValid
  have trace := state.insertSingleton_trace id block element valid found growing empty unassigned gapNonnegative afterSegment otherValid
  refine ⟨trace, trace.final_valid, ?_, ordered,
    state.insertSingleton_oneGrowingPerSide id block element insertedTrace.final_valid found growing one,
    state.insertSingleton_growingTopmost id block element found topmost,
    state.insertSingleton_valuesRealizeGaps id block element values found empty elementOne⟩
  intro queried
  change queried ∈ (state.insertSingleton id block element).allElements ↔ state.view.parent queried ≠ none
  rw [insertSingleton, create_allElements, convert_allElements]
  exact insertedComplete queried

end Splay.Lazy.State
