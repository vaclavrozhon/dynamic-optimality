import Splay.Lazy.BlockRelocationGeometry

namespace Splay.Lazy

/-- Filtering an ambient child order preserves a segment whose payload is
entirely retained. This also covers a temporarily detached old heap root. -/
theorem IsSegment.filter_ambient {α : Type*} {inside whole : List α}
    (segment : IsSegment inside whole) (predicate : α → Bool)
    (retained : ∀ element ∈ inside, predicate element = true) :
    IsSegment inside (whole.filter predicate) := by
  obtain ⟨front, back, decomposition⟩ := segment
  refine ⟨front.filter predicate, back.filter predicate, ?_⟩
  rw [decomposition, List.filter_append, List.filter_append, List.filter_eq_self.mpr retained]

namespace State

/-- The relocated blocks retain full target segments, not merely segments
after filtering detached vertices. This stronger fact permits reinsertion. -/
theorem relocateBlocks_fullSegments {n : ℕ} (state : State n) (after : HeapView n)
    (segments : ∀ block ∈ state.blocks, block.mode = .shrinking → block.elements ≠ [] →
      ∃ owner side, IsSegment block.elements (after.topDown owner side))
    (prefixes : ∀ block ∈ state.blocks, block.mode = .growing →
      ∃ suffix, after.topDown block.owner block.side = block.elements ++ suffix) :
    ∀ block ∈ (state.relocateBlocks after).blocks, IsSegment block.elements (after.topDown block.owner block.side) := by
  intro block member
  obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp member
  rw [Block.relocated_elements]
  by_cases empty : old.elements = []
  · rw [empty]
    exact IsSegment.nil _
  · cases mode : old.mode with
    | shrinking =>
        obtain ⟨owner, side, segment⟩ := segments old oldMember mode empty
        obtain ⟨ownerEq, sideEq⟩ := Block.relocated_placement_of_segment state.view after old mode empty segment
        rw [ownerEq, sideEq]
        exact segment
    | growing =>
        rw [Block.relocated_of_growing _ _ _ mode]
        obtain ⟨suffix, decomposition⟩ := prefixes old oldMember mode
        exact ⟨[], suffix, by simpa using decomposition⟩

theorem absorbRankUpdate_fullSegments {n : ℕ} {state : State n} (after : HeapView n) (shift : Block n → ℤ)
    (same : state.view.SameStructure after)
    (segments : ∀ block ∈ state.blocks, IsSegment block.elements (state.view.topDown block.owner block.side)) :
    ∀ block ∈ (state.absorbRankUpdate after shift).blocks,
      IsSegment block.elements (after.topDown block.owner block.side) := by
  intro block member
  obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp member
  change IsSegment old.elements (after.topDown old.owner old.side)
  rw [same.topDown_apply]
  exact segments old oldMember

/-- A root-changing relocation also preserves synchronized values when the
new root was prepared as a value-one singleton before its deletion. -/
theorem relocateBlocks_values_of_root_value {n : ℕ} {params : Interface.Parameters} {state : State n}
    (valid : state.Valid params) (values : state.ValuesRealizeGaps)
    {after : HeapView n} (geometry : state.RelocationGeometry after) (rootValue : state.value after.root = 1) :
    (state.relocateBlocks after).ValuesRealizeGaps := by
  refine ⟨rootValue, ?_⟩
  intro block member element inside
  obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp member
  rw [Block.relocated_elements] at inside
  change state.value element = Analysis.transientContractedGap (after.rawGap element)
    (old.relocated state.view after).intervalGap
  by_cases selected : old.mode = .shrinking ∧ old.elements ≠ []
  · rw [(Block.relocated_isTransfer (valid.2 old oldMember) geometry.ranks selected.1 selected.2
      (geometry.segments old oldMember)).contractedGap_eq inside]
    exact values.2 old oldMember element inside
  · have growing : old.mode = .growing := by
      cases mode : old.mode with
      | growing => rfl
      | shrinking => exact (selected ⟨mode, List.ne_nil_of_mem inside⟩).elim
    rw [Block.relocated_of_growing _ _ _ growing, geometry.growingRaw old oldMember growing element inside]
    exact values.2 old oldMember element inside

/-- Full canonical segments suffice for relocation even while vertices are
detached and even when the root changes. Filtering by the actual assigned
payload removes detached vertices without splitting any retained segment. -/
theorem RelocationGeometry.of_partial_full_segments {n : ℕ} {params : Interface.Parameters} {state : State n}
    (valid : state.Valid params) (after : HeapView n) (ranks : after.rank = state.view.rank)
    (segments : ∀ block ∈ state.blocks, block.mode = .shrinking → block.elements ≠ [] →
      ∃ owner side, IsSegment block.elements (after.topDown owner side))
    (prefixes : ∀ block ∈ state.blocks, block.mode = .growing →
      ∃ suffix, after.topDown block.owner block.side = block.elements ++ suffix) :
    state.RelocationGeometry after := by
  have restrict {block : Block n} (member : block ∈ state.blocks) {owner : Element n} {side : Side}
      (segment : IsSegment block.elements (after.topDown owner side)) :
      IsSegment block.elements (after.attachedTopDown state.allElements owner side) := by
    apply segment.filter_ambient
    intro element inside
    exact decide_eq_true (mem_allElements_iff.mpr ⟨block, member, inside⟩)
  refine ⟨ranks, ?_, ?_⟩
  · intro block member
    by_cases empty : block.elements = []
    · rw [empty]
      exact ⟨[], after.attachedTopDown state.allElements (block.relocated state.view after).owner
        (block.relocated state.view after).side, by simp⟩
    · cases mode : block.mode with
      | shrinking =>
          obtain ⟨owner, side, segment⟩ := segments block member mode empty
          obtain ⟨ownerEq, sideEq⟩ := Block.relocated_placement_of_segment state.view after block mode empty segment
          rw [ownerEq, sideEq]
          exact restrict member segment
      | growing =>
          rw [Block.relocated_of_growing _ _ _ mode]
          obtain ⟨suffix, decomposition⟩ := prefixes block member mode
          exact restrict member ⟨[], suffix, by simpa using decomposition⟩
  · intro block member growing element inside
    obtain ⟨suffix, decomposition⟩ := prefixes block member growing
    have newInside : element ∈ after.topDown block.owner block.side := by rw [decomposition]; simp [inside]
    have newParent := (after.mem_topDown_iff.mp newInside).1
    have oldParent := (valid.2 block member).parent_eq inside
    simp [HeapView.rawGap, newParent, oldParent, ranks]

end State
end Splay.Lazy
