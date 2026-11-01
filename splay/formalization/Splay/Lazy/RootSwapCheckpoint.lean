import Splay.Lazy.CompleteSingletonInsertion
import Splay.Lazy.CellRankUpdate

namespace Splay.Lazy.State

/-- A root change after deletion, relocation and numeric-rank absorption,
with only the old root still awaiting its actual singleton insertion. -/
structure RootSwapCheckpoint {n : ℕ} (params : Interface.Parameters) (initial : State n) (target : HeapView n) where
  state : State n
  events : List (Event n)
  trace : Trace params initial events state
  valid : state.Valid params
  view_eq : state.view = target
  completeExcept : state.CompleteExcept initial.view.root
  oneGrowing : state.OneGrowingPerSide
  topmost : state.GrowingTopmost
  values : state.ValuesRealizeGaps
  oldRootValue : state.value initial.view.root = 1
  empty : ∀ block ∈ state.blocks, block.mode = .growing →
    block.owner = (target.parent initial.view.root).getD target.root → block.elements = []
  fullSegments : ∀ block ∈ state.blocks, IsSegment block.elements (target.topDown block.owner block.side)
  births : state.blocks.length = initial.blocks.length
  noInserts : Interface.totalInserts (eraseOperations events) = 0
  noIncreases : Interface.totalIncreases (eraseOperations events) = 0
  largeOrigin : ∀ block ∈ state.blocks, 1 < block.elements.length →
    ∃ old ∈ initial.blocks, block.elements = old.elements ∧ block.passCount = old.passCount

namespace RootSwapCheckpoint

/-- Construct the root-changing partial checkpoint without atomizing any
unrelated interval. Every premise refers to actual prepared input blocks. -/
theorem exists_of_prepared {n : ℕ} {params : Interface.Parameters} {initial : State n}
    (stable : initial.Stable params) (target : HeapView n)
    {sourceId : Interface.BlockId} {source : Block n} (found : initial.blocks[sourceId]? = some source)
    (sourceShrinking : source.mode = .shrinking) (sourceSingleton : source.elements = [target.root])
    (segments : ∀ block ∈ initial.blocks, block.mode = .shrinking → block.elements ≠ [] → target.root ∉ block.elements →
      ∃ owner side, IsSegment block.elements (target.topDown owner side))
    (prefixes : ∀ block ∈ initial.blocks, block.mode = .growing →
      ∃ suffix, target.topDown block.owner block.side = block.elements ++ suffix)
    (growingShift : ∀ block ∈ initial.blocks, block.mode = .growing → ∀ element ∈ block.elements,
      initial.numericRankShift target element = initial.numericRankShift target block.owner)
    (shrinkingShift : ∀ block ∈ initial.blocks, block.mode = .shrinking →
      ∀ first ∈ block.elements, ∀ second ∈ block.elements,
        initial.numericRankShift target first = initial.numericRankShift target second)
    (empty : ∀ block ∈ initial.blocks, block.mode = .growing →
      block.owner = (target.parent initial.view.root).getD target.root → block.elements = []) :
    Nonempty (RootSwapCheckpoint params initial target) := by
  let detached := initial.delete sourceId target.root 0
  have deletion := deleteSingleton_trace stable.1 found sourceShrinking target.root sourceSingleton
  have detachedPayloads : detached.allElements = initial.allElements.erase target.root :=
    delete_allElements sourceId source target.root 0 found (by simp [sourceSingleton]) stable.1.allElements_nodup
  have targetAbsent : target.root ∉ detached.allElements := by rw [detachedPayloads]; exact stable.1.allElements_nodup.not_mem_erase
  have detachedSegments : ∀ block ∈ detached.blocks, block.mode = .shrinking → block.elements ≠ [] →
      ∃ owner side, IsSegment block.elements (target.topDown owner side) := by
    intro block member shrinking nonempty
    exact segments block (deleteSingleton_nonempty_preserved initial found target.root sourceSingleton block member nonempty)
      shrinking nonempty (fun inside => targetAbsent (mem_allElements_iff.mpr ⟨block, member, inside⟩))
  have detachedPrefixes : ∀ block ∈ detached.blocks, block.mode = .growing →
      ∃ suffix, target.topDown block.owner block.side = block.elements ++ suffix := by
    intro block member growing
    exact prefixes block (deleteSingleton_growing_preserved initial found sourceShrinking target.root block member growing) growing
  let transient := target.withRank initial.view.rank
  let relocated := detached.relocateBlocks transient
  have geometry : detached.RelocationGeometry transient :=
    RelocationGeometry.of_partial_full_segments deletion.final_valid transient rfl detachedSegments detachedPrefixes
  have relocation := relocateBlocks_trace deletion.final_valid geometry
  have relocatedValid : relocated.Valid params := relocation.final_valid
  have same : relocated.view.SameStructure target := ⟨rfl, rfl, rfl, rfl, rfl⟩
  have compatible : relocated.RankUpdateCompatible target (relocated.isolatedRankBlockShift target) := by
    apply rankUpdateCompatible_of_uniformChildShift relocatedValid target same
    · intro block member growing element inside
      obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp member
      have oldGrowing : old.mode = .growing := by simpa only [Block.relocated_mode] using growing
      rw [Block.relocated_of_growing _ _ _ oldGrowing] at inside ⊢
      exact growingShift old (deleteSingleton_growing_preserved initial found sourceShrinking target.root old oldMember oldGrowing) oldGrowing element inside
    · intro block member shrinking first firstIn second secondIn
      obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp member
      have oldShrinking : old.mode = .shrinking := by simpa only [Block.relocated_mode] using shrinking
      rw [Block.relocated_elements] at firstIn secondIn
      exact shrinkingShift old (deleteSingleton_nonempty_preserved initial found target.root sourceSingleton old oldMember (List.ne_nil_of_mem firstIn))
        oldShrinking first firstIn second secondIn
  let final := relocated.absorbRankUpdate target (relocated.isolatedRankBlockShift target)
  have rankTrace : Trace params relocated [.silent] final := relocated.absorbRankUpdate_trace relocatedValid compatible
  have fullTrace := deletion.append (relocation.append rankTrace)
  have values : relocated.ValuesRealizeGaps := relocateBlocks_values_of_root_value deletion.final_valid
    (deleteSingleton_valuesRealizeGaps stable.2.2.2.2.2 found target.root sourceSingleton) geometry
    (stable.2.2.2.2.2.singleton_value_one stable.1 (List.mem_of_getElem? found) sourceShrinking sourceSingleton)
  have one : relocated.OneGrowingPerSide := relocateBlocks_oneGrowingPerSide
    (stable.2.2.2.1.delete sourceId target.root 0) transient
  have topmost : relocated.GrowingTopmost := relocateBlocks_growingTopmost transient detachedPrefixes
  have fullSegments : ∀ block ∈ relocated.blocks, IsSegment block.elements (relocated.view.topDown block.owner block.side) :=
    relocateBlocks_fullSegments detached transient detachedSegments detachedPrefixes
  refine ⟨{
    state := final
    events := [.operation (.delete sourceId target.root), .silent, .silent]
    trace := fullTrace
    valid := rankTrace.final_valid
    view_eq := rfl
    completeExcept := ?_
    oneGrowing := relocated.absorbRankUpdate_oneGrowingPerSide target _ one
    topmost := relocated.absorbRankUpdate_growingTopmost topmost same
    values := absorbRankUpdate_valuesRealizeGaps values compatible
    oldRootValue := stable.2.2.2.2.2.1
    empty := ?_
    fullSegments := absorbRankUpdate_fullSegments target _ same fullSegments
    births := by simp [final, relocated, detached, State.absorbRankUpdate, State.relocateBlocks, State.delete]
    noInserts := rfl
    noIncreases := rfl
    largeOrigin := by
      intro block member large
      obtain ⟨moved, movedMember, rfl⟩ := List.mem_map.mp member
      obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp movedMember
      have oldLarge : 1 < old.elements.length := by
        simpa only [Block.shiftedInterval, Block.relocated_elements] using large
      have nonempty : old.elements ≠ [] := by intro empty; simp [empty] at oldLarge
      refine ⟨old, deleteSingleton_nonempty_preserved initial found target.root sourceSingleton old oldMember nonempty,
        Block.relocated_elements _ _ _, ?_⟩
      exact congrArg Interface.Block.passCount (old.relocated_toInterface detached.view transient)
  }⟩
  · apply stable.2.1.completeExcept_of_root_swap stable.1
    change final.allElements = initial.allElements.erase target.root
    simpa only [final, absorbRankUpdate_allElements, relocated, relocateBlocks_allElements] using detachedPayloads
  · intro block member growing ownerEq
    obtain ⟨moved, movedMember, rfl⟩ := List.mem_map.mp member
    obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp movedMember
    have oldGrowing : old.mode = .growing := by simpa only [Block.shiftedInterval, Block.relocated_mode] using growing
    change (old.relocated detached.view transient).elements = []
    change (old.relocated detached.view transient).owner = _ at ownerEq
    rw [Block.relocated_of_growing _ _ _ oldGrowing] at ownerEq ⊢
    exact empty old (deleteSingleton_growing_preserved initial found sourceShrinking target.root old oldMember oldGrowing) oldGrowing ownerEq

end RootSwapCheckpoint
end Splay.Lazy.State
