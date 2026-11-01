import Splay.Lazy.BlockRelocation
import Splay.Lazy.ShrinkingSingletons
import Splay.Accounting.RootHeavyPathBoundaryDecomposition

namespace Splay.Lazy

/-- Any nonempty segment fixes the relocation algorithm's computed parent
and side through its first actual member. -/
theorem Block.relocated_placement_of_segment {n : ℕ} (before after : HeapView n) (block : Block n)
    (shrinking : block.mode = .shrinking) (nonempty : block.elements ≠ [])
    {owner : Element n} {side : Side} (segment : IsSegment block.elements (after.topDown owner side)) :
    (block.relocated before after).owner = owner ∧ (block.relocated before after).side = side := by
  have firstIn : block.elements.headD block.owner ∈ block.elements := by
    cases elements : block.elements with
    | nil => exact (nonempty elements).elim
    | cons first rest => simp
  obtain ⟨parentEq, sideEq⟩ := after.mem_topDown_iff.mp (segment.mem firstIn)
  rw [Block.relocated, if_pos ⟨shrinking, nonempty⟩]
  change (after.parent (block.elements.headD block.owner)).getD block.owner = owner ∧
    after.side (block.elements.headD block.owner) = side
  simp only [parentEq, sideEq, Option.getD_some, and_self]

namespace State

/-- Full target segments and actual growing prefixes discharge every
relocation obligation. Equal numeric ranks then force growing raw gaps to
stay unchanged, using the shared parent found in those prefixes. -/
theorem RelocationGeometry.of_full_segments {n : ℕ} {params : Interface.Parameters} {state : State n}
    (valid : state.Valid params) (complete : state.Complete) (after : HeapView n)
    (ranks : after.rank = state.view.rank) (root : after.root = state.view.root)
    (segments : ∀ block ∈ state.blocks, block.mode = .shrinking → block.elements ≠ [] →
      ∃ owner side, IsSegment block.elements (after.topDown owner side))
    (prefixes : ∀ block ∈ state.blocks, block.mode = .growing →
      ∃ suffix, after.topDown block.owner block.side = block.elements ++ suffix) :
    state.RelocationGeometry after := by
  have attached (owner : Element n) (side : Side) :
      after.attachedTopDown state.allElements owner side = after.topDown owner side := by
    have result := (relocateBlocks_complete complete after root).attachedTopDown_eq_topDown owner side
    change after.attachedTopDown (state.relocateBlocks after).allElements owner side = after.topDown owner side at result
    simpa only [relocateBlocks_allElements] using result
  refine ⟨ranks, ?_, ?_⟩
  · intro block member
    rw [attached]
    by_cases empty : block.elements = []
    · rw [empty]
      exact ⟨[], after.topDown (block.relocated state.view after).owner (block.relocated state.view after).side, by simp⟩
    · cases mode : block.mode with
      | shrinking =>
          obtain ⟨owner, side, segment⟩ := segments block member mode empty
          obtain ⟨ownerEq, sideEq⟩ := Block.relocated_placement_of_segment state.view after block mode empty segment
          rw [ownerEq, sideEq]
          exact segment
      | growing =>
          rw [Block.relocated_of_growing _ _ _ mode]
          obtain ⟨suffix, decomposition⟩ := prefixes block member mode
          exact ⟨[], suffix, by simpa using decomposition⟩
  · intro block member growing element inside
    obtain ⟨suffix, decomposition⟩ := prefixes block member growing
    have newInside : element ∈ after.topDown block.owner block.side := by rw [decomposition]; simp [inside]
    have newParent := (after.mem_topDown_iff.mp newInside).1
    have oldParent := (valid.2 block member).parent_eq inside
    simp [HeapView.rawGap, newParent, oldParent, ranks]

theorem relocateBlocks_rankPrepared {n : ℕ} {params : Interface.Parameters} {state : State n}
    (prepared : state.RankPrepared params) {after : HeapView n}
    (geometry : state.RelocationGeometry after) (root : after.root = state.view.root)
    (prefixes : ∀ block ∈ state.blocks, block.mode = .growing →
      ∃ suffix, after.topDown block.owner block.side = block.elements ++ suffix) :
    (state.relocateBlocks after).RankPrepared params :=
  ⟨relocateBlocks_valid prepared.valid geometry,
    relocateBlocks_complete prepared.complete after root,
    relocateBlocks_oneGrowingPerSide prepared.oneGrowingPerSide after,
    relocateBlocks_growingTopmost after prefixes,
    relocateBlocks_values prepared.valid prepared.valuesRealizeGaps geometry root⟩

/-- Relocation changes neither singleton payloads nor modes, and preserves
each growing block literally. Thus it preserves prepared rank isolation. -/
theorem IsolatedRanks.relocateBlocks {n : ℕ} {state : State n} {selected : Finset (Element n)}
    (isolated : state.IsolatedRanks selected) (after : HeapView n) :
    (state.relocateBlocks after).IsolatedRanks selected := by
  constructor
  · intro block member growing marked
    obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp member
    have oldGrowing : old.mode = .growing := by simpa only [Block.relocated_mode] using growing
    rw [Block.relocated_of_growing _ _ _ oldGrowing] at marked ⊢
    exact isolated.growingEmpty old oldMember oldGrowing marked
  · intro element marked block member inside
    obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp member
    rw [Block.relocated_elements] at inside
    simpa only [Block.relocated_mode, Block.relocated_elements] using isolated.singleton element marked old oldMember inside

end State
end Splay.Lazy
