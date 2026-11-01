import Splay.Lazy.DeletionGeometry
import Splay.Lazy.BlockRefinement
import Splay.Lazy.ComparisonRootSwapComplete

namespace Splay.Lazy.State

/-- Every valid shrinking singleton realizes value one, regardless of the
sign of its raw gap. This supplies the new root's synchronized value. -/
theorem ValuesRealizeGaps.singleton_value_one {n : ℕ} {params : Interface.Parameters} {state : State n}
    (values : state.ValuesRealizeGaps) (valid : state.Valid params)
    {block : Block n} (member : block ∈ state.blocks) (shrinking : block.mode = .shrinking)
    {element : Element n} (singleton : block.elements = [element]) : state.value element = 1 := by
  have gapValid := (valid.2 block member).2.2
  simp only [Block.GapValid, shrinking] at gapValid
  have intervalEq : block.intervalGap = state.view.rawGap element := by
    rcases gapValid with empty | nonempty
    · simp [singleton] at empty
    · obtain ⟨minimum, minimumIn, attained⟩ := nonempty.2.1
      have equal : minimum = element := by simpa [singleton] using minimumIn
      subst minimum
      exact attained.symm
  rw [values.2 block member element (by simp [singleton]), intervalEq]
  exact Analysis.transientContractedGap_self _

theorem delete_blocks_cases {n : ℕ} (state : State n) (sourceId : Interface.BlockId) (source : Block n)
    (element : Element n) (gap : ℤ) (found : state.blocks[sourceId]? = some source)
    {block : Block n} (member : block ∈ (state.delete sourceId element gap).blocks) :
    block = source.deleted element gap ∨ block ∈ state.blocks := by
  obtain ⟨id, blockFound⟩ := List.mem_iff_getElem?.mp member
  change (state.blocks.modify sourceId fun old => old.deleted element gap)[id]? = some block at blockFound
  rw [List.getElem?_modify] at blockFound
  split at blockFound
  next equal =>
    subst id
    rw [found] at blockFound
    exact Or.inl (by simpa using blockFound.symm)
  next different =>
    exact Or.inr (List.mem_of_getElem? (by simpa using blockFound))

/-- A real shrinking singleton can be detached without any preparation of
the surrounding blocks. The emptied source has interval gap zero. -/
theorem deleteSingleton_trace {n : ℕ} {params : Interface.Parameters} {state : State n}
    (valid : state.Valid params) {sourceId : Interface.BlockId} {source : Block n}
    (found : state.blocks[sourceId]? = some source) (shrinking : source.mode = .shrinking)
    (element : Element n) (singleton : source.elements = [element]) :
    Trace params state [.operation (.delete sourceId element)] (state.delete sourceId element 0) := by
  apply Trace.singleton
  exact delete_step_of_gapValid valid found shrinking element (by simp [singleton]) 0
    (by simp [Block.GapValid, Block.deleted, shrinking, singleton])

/-- All nonempty blocks survive literal singleton deletion. -/
theorem deleteSingleton_nonempty_preserved {n : ℕ} (state : State n)
    {sourceId : Interface.BlockId} {source : Block n} (found : state.blocks[sourceId]? = some source)
    (element : Element n) (singleton : source.elements = [element]) :
    ∀ block ∈ (state.delete sourceId element 0).blocks, block.elements ≠ [] → block ∈ state.blocks := by
  intro block member nonempty
  rcases delete_blocks_cases state sourceId source element 0 found member with changed | old
  · exact (nonempty (by simp [changed, Block.deleted, singleton])).elim
  · exact old

theorem deleteSingleton_growing_preserved {n : ℕ} (state : State n)
    {sourceId : Interface.BlockId} {source : Block n} (found : state.blocks[sourceId]? = some source)
    (shrinking : source.mode = .shrinking) (element : Element n) :
    ∀ block ∈ (state.delete sourceId element 0).blocks, block.mode = .growing → block ∈ state.blocks := by
  intro block member growing
  rcases delete_blocks_cases state sourceId source element 0 found member with changed | old
  · simp [changed, Block.deleted, shrinking] at growing
  · exact old

theorem deleteSingleton_valuesRealizeGaps {n : ℕ} {state : State n} (values : state.ValuesRealizeGaps)
    {sourceId : Interface.BlockId} {source : Block n} (found : state.blocks[sourceId]? = some source)
    (element : Element n) (singleton : source.elements = [element]) :
    (state.delete sourceId element 0).ValuesRealizeGaps := by
  refine ⟨values.1, ?_⟩
  intro block member child inside
  exact values.2 block (deleteSingleton_nonempty_preserved state found element singleton block member (List.ne_nil_of_mem inside)) child inside

theorem deleteSingleton_growingTopmost {n : ℕ} {state : State n} (topmost : state.GrowingTopmost)
    {sourceId : Interface.BlockId} {source : Block n} (found : state.blocks[sourceId]? = some source)
    (shrinking : source.mode = .shrinking) (element : Element n) :
    (state.delete sourceId element 0).GrowingTopmost := by
  intro id
  dsimp only
  intro growing
  let block := (state.delete sourceId element 0).blocks.get id
  have member : block ∈ (state.delete sourceId element 0).blocks := List.get_mem _ _
  have oldMember := deleteSingleton_growing_preserved state found shrinking element block member growing
  obtain ⟨oldId, oldFound⟩ := List.mem_iff_getElem?.mp oldMember
  obtain ⟨lt, oldEq⟩ := List.getElem?_eq_some_iff.mp oldFound
  have result := topmost ⟨oldId, lt⟩
  dsimp only at result
  rw [show state.blocks.get ⟨oldId, lt⟩ = block from oldEq] at result
  exact result growing

end Splay.Lazy.State
