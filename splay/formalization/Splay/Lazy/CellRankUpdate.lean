import Splay.Lazy.IsolatedRankUpdate

namespace Splay.Lazy.State

/-- The rank difference intrinsic to two numeric snapshots. -/
def numericRankShift {n : ℕ} (state : State n) (after : HeapView n) (element : Element n) : ℤ :=
  (after.rank element : ℤ) - state.view.rank element

/-- Uniform child rank differences suffice for shrinking blocks; growing
children must share their owner's difference. The stored shift is computed
from the first actual payload element, including negative transient gaps. -/
theorem rankUpdateCompatible_of_uniformChildShift {n : ℕ} {params : Interface.Parameters}
    {state : State n} (valid : state.Valid params) (after : HeapView n)
    (same : state.view.SameStructure after)
    (growing : ∀ block ∈ state.blocks, block.mode = .growing → ∀ element ∈ block.elements,
      state.numericRankShift after element = state.numericRankShift after block.owner)
    (shrinking : ∀ block ∈ state.blocks, block.mode = .shrinking →
      ∀ first ∈ block.elements, ∀ second ∈ block.elements,
        state.numericRankShift after first = state.numericRankShift after second) :
    state.RankUpdateCompatible after (state.isolatedRankBlockShift after) := by
  apply BlockwiseUniformRankShift.compatible (elementShift := state.numericRankShift after) _ valid
  refine ⟨same, ?_, ?_, ?_, ?_⟩
  · intro element
    simp only [HeapView.RankShift, numericRankShift]
    omega
  · intro block member mode
    exact ⟨by simp [isolatedRankBlockShift, mode], growing block member mode⟩
  · intro block _member mode empty
    simp [isolatedRankBlockShift, mode, empty]
  · intro block member mode nonempty
    cases elements : block.elements with
    | nil => exact (nonempty elements).elim
    | cons first rest =>
        have firstIn : first ∈ block.elements := by simp [elements]
        refine ⟨state.numericRankShift after first,
          fun element inside => shrinking block member mode element (by simpa [elements] using inside) first firstIn, ?_⟩
        have parent := (valid.2 block member).parent_eq firstIn
        simp only [isolatedRankBlockShift, mode, reduceCtorEq, ↓reduceIte, elements,
          HeapView.rawGap, same.parent_apply, parent, numericRankShift]
        omega

end Splay.Lazy.State
