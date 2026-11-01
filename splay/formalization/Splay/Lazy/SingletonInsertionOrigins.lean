import Splay.Lazy.SingletonInsertion

namespace Splay.Lazy.State

/-- Singleton insertion cannot modify any block containing two or more
elements. Such a block survives literally from the old state. -/
theorem insertSingleton_large_preserved {n : ℕ} (state : State n) (blockId : Interface.BlockId)
    (block : Block n) (element : Element n) (found : state.blocks[blockId]? = some block)
    (empty : block.elements = []) {current : Block n}
    (member : current ∈ (state.insertSingleton blockId block element).blocks)
    (large : 1 < current.elements.length) : current ∈ state.blocks := by
  rw [insertSingleton_blocks] at member
  rcases List.mem_append.mp member with modified | replacement
  · obtain ⟨id, currentFound⟩ := List.mem_iff_getElem?.mp modified
    rw [List.getElem?_modify] at currentFound
    split at currentFound
    next selected =>
      have original : state.blocks[id]? = some block := by simpa only [selected] using found
      rw [original] at currentFound
      have equal : (block.inserted element).converted (state.view.rawGap element) = current := by simpa using currentFound
      simp [← equal, Block.converted, Block.inserted, empty] at large
    next untouched =>
      exact List.mem_of_getElem? (show state.blocks[id]? = some current by simpa using currentFound)
  · rw [List.mem_singleton.mp replacement] at large
    simp [Block.emptyGrowing] at large

end Splay.Lazy.State
