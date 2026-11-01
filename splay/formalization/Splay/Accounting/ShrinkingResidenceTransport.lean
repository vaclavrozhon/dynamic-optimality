import Splay.Interface.ShrinkingResidence
import Splay.Interface.ShrinkingSingletonResidence
import Splay.Accounting.ArticleSourceView
import Splay.Lazy.BoundaryRelocation

namespace Splay.Accounting

open Splay.Lazy

@[simp]
theorem retains_iff_not_leaves {n : ℕ} (operation : Interface.Operation n) (element : Interface.Element n) :
    operation.Retains element ↔ ¬ operationLeavesElement operation element := by
  cases operation <;> simp [Interface.Operation.Retains, operationLeavesElement, ne_comm]

/-- The interface property exposes a concrete shrinking rich block, including
its current persistent ID. -/
theorem hasShrinkingElement_iff {n : ℕ} (state : Lazy.State n) (element : Interface.Element n) :
    state.toInterface.HasShrinkingElement element ↔
      ∃ (sourceId : Interface.BlockId) (source : Lazy.Block n), state.blocks[sourceId]? = some source ∧
        source.mode = .shrinking ∧ element ∈ source.elements := by
  constructor
  · rintro ⟨block, member, shrinking, inside⟩
    obtain ⟨source, sourceMember, equal⟩ := List.mem_map.mp member
    obtain ⟨sourceId, found⟩ := List.mem_iff_getElem?.mp sourceMember
    subst block
    exact ⟨sourceId, source, found, shrinking, inside⟩
  · rintro ⟨sourceId, source, found, shrinking, inside⟩
    exact ⟨source.toInterface, List.mem_map.mpr ⟨source, List.mem_of_getElem? found, rfl⟩,
      shrinking, inside⟩

/-- Singleton isolation is visible in the interface and recovers an actual
rich singleton block at its current ID. -/
theorem hasShrinkingSingleton_iff {n : ℕ} (state : Lazy.State n) (element : Interface.Element n) :
    state.toInterface.HasShrinkingSingleton element ↔
      ∃ (sourceId : Interface.BlockId) (source : Lazy.Block n), state.blocks[sourceId]? = some source ∧
        source.mode = .shrinking ∧ source.elements = [element] := by
  constructor
  · rintro ⟨id, block, found, shrinking, singleton⟩
    change (state.blocks.map Lazy.Block.toInterface)[id]? = some block at found
    rw [List.getElem?_map] at found
    obtain ⟨source, sourceFound, equal⟩ := Option.map_eq_some_iff.mp found
    subst block
    exact ⟨id, source, sourceFound, shrinking, singleton⟩
  · rintro ⟨id, source, found, shrinking, singleton⟩
    refine ⟨id, source.toInterface, ?_, shrinking, singleton⟩
    change (state.blocks.map Lazy.Block.toInterface)[id]? = some source.toInterface
    simp [found]

/-- A nonleaving isolated singleton remains isolated throughout a rich trace,
including splits and silent changes of placement or gap offset. -/
theorem shrinkingSingleton_after_trace {n : ℕ} {params : Interface.Parameters}
    {initial final : Lazy.State n} {events : List (Lazy.Event n)}
    (trace : Lazy.Trace params initial events final) {element : Interface.Element n}
    {sourceId : Interface.BlockId} {source : Lazy.Block n}
    (sourceFound : initial.blocks[sourceId]? = some source)
    (sourceShrinking : source.mode = .shrinking) (singleton : source.elements = [element])
    (noLeave : element ∉ operationLeavingElementsList (eraseOperations events)) :
    ∃ (finalId : Interface.BlockId) (finalSource : Lazy.Block n), final.blocks[finalId]? = some finalSource ∧
      finalSource.mode = .shrinking ∧ finalSource.elements = [element] := by
  apply (hasShrinkingSingleton_iff final element).mp
  apply trace.toInterface.hasShrinkingSingleton_of_retains
    ((hasShrinkingSingleton_iff initial element).mpr ⟨sourceId, source, sourceFound, sourceShrinking, singleton⟩)
  intro operation operationMember
  apply (retains_iff_not_leaves operation element).mpr
  intro leaves
  apply noLeave
  exact List.mem_flatMap.mpr ⟨operation, operationMember, mem_operationLeavingElements_iff.mpr leaves⟩

/-- Every nonleaving shrinking element has an actual shrinking source at the
end of a rich trace, even if intervening splits changed its source ID. -/
theorem shrinkingResidence_after_trace {n : ℕ} {params : Interface.Parameters}
    {initial final : Lazy.State n} {events : List (Lazy.Event n)}
    (trace : Lazy.Trace params initial events final) {element : Interface.Element n}
    {sourceId : Interface.BlockId} {source : Lazy.Block n}
    (sourceFound : initial.blocks[sourceId]? = some source)
    (sourceShrinking : source.mode = .shrinking) (member : element ∈ source.elements)
    (noLeave : element ∉ operationLeavingElementsList (eraseOperations events)) :
    ∃ (finalId : Interface.BlockId) (finalSource : Lazy.Block n), final.blocks[finalId]? = some finalSource ∧
      finalSource.mode = .shrinking ∧ element ∈ finalSource.elements := by
  apply (hasShrinkingElement_iff final element).mp
  apply trace.toInterface.hasShrinkingElement_of_retains
    ((hasShrinkingElement_iff initial element).mpr ⟨sourceId, source, sourceFound, sourceShrinking, member⟩)
  intro operation operationMember
  apply (retains_iff_not_leaves operation element).mpr
  intro leaves
  apply noLeave
  exact List.mem_flatMap.mpr ⟨operation, operationMember, mem_operationLeavingElements_iff.mpr leaves⟩

/-- An unprocessed boundary loser remains in some actual shrinking source
through the complete internal worklist. -/
theorem ArticleSourceMacroChain.shrinkingSource_of_not_loser
    {n : ℕ} {params : Interface.Parameters} {initial : Lazy.State n}
    (chain : ArticleSourceMacroChain params initial) {element : Interface.Element n}
    {sourceId : Interface.BlockId} {source : Lazy.Block n}
    (sourceFound : initial.blocks[sourceId]? = some source)
    (sourceShrinking : source.mode = .shrinking) (member : element ∈ source.elements)
    (notLoser : element ∉ chain.batches.flatMap fun batch =>
      Interface.pairingLosers (batch.firstMatching ++ batch.secondMatching)) :
    ∃ (finalId : Interface.BlockId) (finalSource : Lazy.Block n), chain.final.blocks[finalId]? = some finalSource ∧
      finalSource.mode = .shrinking ∧ element ∈ finalSource.elements := by
  apply shrinkingResidence_after_trace chain.trace sourceFound sourceShrinking member
  rw [chain.leavingElements_eq]
  exact notLoser

end Splay.Accounting
