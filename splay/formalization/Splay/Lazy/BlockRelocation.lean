import Splay.Lazy.DetachedReparenting
import Splay.Lazy.StableRankUpdate

namespace Splay.Lazy

namespace Block

/-- A shrinking block is placed at the target parent and side of its first
element. Its interval gap absorbs the owner-rank difference. Empty blocks
and all growing blocks retain their administrative placement. -/
noncomputable def relocated {n : ℕ} (before after : HeapView n) (block : Block n) : Block n := by
  classical
  exact if block.mode = .shrinking ∧ block.elements ≠ [] then
    let first := block.elements.headD block.owner
    let owner := (after.parent first).getD block.owner
    block.transferred owner (after.side first) ((before.rank block.owner : ℤ) - after.rank owner)
  else block

@[simp]
theorem relocated_toInterface {n : ℕ} (before after : HeapView n) (block : Block n) :
    (block.relocated before after).toInterface = block.toInterface := by
  unfold relocated
  split <;> rfl

@[simp]
theorem relocated_elements {n : ℕ} (before after : HeapView n) (block : Block n) :
    (block.relocated before after).elements = block.elements := by
  unfold relocated
  split <;> rfl

@[simp]
theorem relocated_mode {n : ℕ} (before after : HeapView n) (block : Block n) :
    (block.relocated before after).mode = block.mode := by
  unfold relocated
  split <;> rfl

theorem relocated_of_growing {n : ℕ} (before after : HeapView n) (block : Block n)
    (growing : block.mode = .growing) : block.relocated before after = block := by
  simp [relocated, growing]

/-- Segment validity at the new placement proves the common new parent of
every member; the exact uniform raw-gap shift follows from equal ranks. -/
noncomputable def relocated_isTransfer {n : ℕ} {before after : HeapView n}
    {assigned : List (Element n)} {block : Block n}
    (valid : block.StructurallyValid before assigned) (ranks : after.rank = before.rank)
    (shrinking : block.mode = .shrinking) (nonempty : block.elements ≠ [])
    (segment : IsSegment block.elements (after.attachedTopDown assigned
      (block.relocated before after).owner (block.relocated before after).side)) :
    block.IsTransfer before after (block.relocated before after) := by
  let first := block.elements.headD block.owner
  let owner := (after.parent first).getD block.owner
  have blockEq : block.relocated before after =
      block.transferred owner (after.side first) ((before.rank block.owner : ℤ) - after.rank owner) := by
    rw [relocated, if_pos ⟨shrinking, nonempty⟩]
  rw [blockEq] at segment ⊢
  apply Block.transferred_isTransfer _ _ _ _ _ _ shrinking
  intro element inside
  have newParent : after.parent element = some owner :=
    (after.mem_topDown_iff.mp ((after.mem_attachedTopDown_iff.mp (segment.mem inside)).1)).1
  have oldParent := valid.parent_eq inside
  simp only [HeapView.rawGap, newParent, oldParent, ranks]
  omega

/-- Once a shrinking block fits the new child order, relocation preserves
its full gap invariant and every interface field. -/
theorem relocated_structurallyValid {n : ℕ} {before after : HeapView n}
    {assigned : List (Element n)} {block : Block n}
    (valid : block.StructurallyValid before assigned) (ranks : after.rank = before.rank)
    (segment : IsSegment block.elements (after.attachedTopDown assigned
      (block.relocated before after).owner (block.relocated before after).side))
    (growingRaw : block.mode = .growing → ∀ element ∈ block.elements,
      after.rawGap element = before.rawGap element) :
    (block.relocated before after).StructurallyValid after assigned := by
  by_cases selected : block.mode = .shrinking ∧ block.elements ≠ []
  · exact (relocated_isTransfer valid ranks selected.1 selected.2 segment).after_structurallyValid valid selected.2
      (by simpa only [relocated_elements] using segment)
  · have fixed : block.relocated before after = block := by simp [relocated, selected]
    rw [fixed] at segment ⊢
    apply valid.of_rawGap_eq segment
    intro element inside
    cases mode : block.mode with
    | growing => exact growingRaw mode element inside
    | shrinking => exact (selected ⟨mode, List.ne_nil_of_mem inside⟩).elim

end Block

namespace State

/-- Simultaneously relocate all whole shrinking blocks into a new view.
No block identity, payload, counter, creator, or interface value is changed. -/
noncomputable def relocateBlocks {n : ℕ} (state : State n) (after : HeapView n) : State n where
  view := after
  blocks := state.blocks.map (Block.relocated state.view after)
  value := state.value

@[simp]
theorem relocateBlocks_toInterface {n : ℕ} (state : State n) (after : HeapView n) :
    (state.relocateBlocks after).toInterface = state.toInterface := by
  unfold relocateBlocks toInterface
  congr 1
  simp [List.map_map, Function.comp_def]

@[simp]
theorem relocateBlocks_allElements {n : ℕ} (state : State n) (after : HeapView n) :
    (state.relocateBlocks after).allElements = state.allElements := by
  simp [relocateBlocks, allElements, List.flatMap_map]

@[simp]
theorem relocateBlocks_blocks_length {n : ℕ} (state : State n) (after : HeapView n) :
    (state.relocateBlocks after).blocks.length = state.blocks.length := by
  simp [relocateBlocks]

/-- Concrete geometric obligations for whole-block relocation: each block
fits a target child interval and growing blocks retain their raw gaps. -/
structure RelocationGeometry {n : ℕ} (state : State n) (after : HeapView n) : Prop where
  ranks : after.rank = state.view.rank
  segments : ∀ block ∈ state.blocks,
    IsSegment block.elements (after.attachedTopDown state.allElements
      (block.relocated state.view after).owner (block.relocated state.view after).side)
  growingRaw : ∀ block ∈ state.blocks, block.mode = .growing →
    ∀ element ∈ block.elements, after.rawGap element = state.view.rawGap element

theorem relocateBlocks_valid {n : ℕ} {params : Interface.Parameters} {state : State n}
    (valid : state.Valid params) {after : HeapView n} (geometry : state.RelocationGeometry after) :
    (state.relocateBlocks after).Valid params := by
  refine ⟨?_, ?_⟩
  · rw [relocateBlocks_toInterface]
    exact valid.1
  · intro block member
    obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp member
    rw [relocateBlocks_allElements]
    exact Block.relocated_structurallyValid (valid.2 old oldMember) geometry.ranks
      (geometry.segments old oldMember) (geometry.growingRaw old oldMember)

/-- All transfers form one checked silent event, regardless of how many
already prepared shrinking blocks there are. -/
theorem relocateBlocks_trace {n : ℕ} {params : Interface.Parameters} {state : State n}
    (valid : state.Valid params) {after : HeapView n} (geometry : state.RelocationGeometry after) :
    Trace params state [.silent] (state.relocateBlocks after) :=
  Trace.singleton (Step.silent valid (relocateBlocks_valid valid geometry) (relocateBlocks_toInterface _ _).symm)

theorem relocateBlocks_values {n : ℕ} {params : Interface.Parameters} {state : State n}
    (valid : state.Valid params) (values : state.ValuesRealizeGaps)
    {after : HeapView n} (geometry : state.RelocationGeometry after) (root : after.root = state.view.root) :
    (state.relocateBlocks after).ValuesRealizeGaps := by
  refine ⟨?_, ?_⟩
  · change state.value after.root = 1
    rw [root]
    exact values.1
  · intro block member element inside
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

theorem relocateBlocks_complete {n : ℕ} {state : State n} (complete : state.Complete)
    (after : HeapView n) (root : after.root = state.view.root) : (state.relocateBlocks after).Complete := by
  intro element
  rw [relocateBlocks_allElements, complete element]
  change state.view.parent element ≠ none ↔ after.parent element ≠ none
  constructor
  · intro attached absent
    have equal := (after.parent_eq_none element absent).trans root
    exact attached (equal ▸ state.view.root_parent)
  · intro attached absent
    have equal := (state.view.parent_eq_none element absent).trans root.symm
    exact attached (equal ▸ after.root_parent)

theorem relocateBlocks_oneGrowingPerSide {n : ℕ} {state : State n}
    (one : state.OneGrowingPerSide) (after : HeapView n) : (state.relocateBlocks after).OneGrowingPerSide := by
  intro owner side
  obtain ⟨oldId, oldProperty, unique⟩ := one owner side
  dsimp only at oldProperty
  let newId : Fin (state.relocateBlocks after).blocks.length := ⟨oldId.val, by simpa using oldId.isLt⟩
  have fixed : (state.relocateBlocks after).blocks.get newId = state.blocks.get oldId := by
    simp only [relocateBlocks, List.get_eq_getElem, List.getElem_map]
    exact Block.relocated_of_growing _ _ _ oldProperty.1
  refine ⟨newId, ?_, ?_⟩
  · dsimp only
    rw [fixed]
    exact oldProperty
  · intro candidate property
    dsimp only at property
    let oldCandidate : Fin state.blocks.length := ⟨candidate.val, by simpa using candidate.isLt⟩
    have growing : (state.blocks.get oldCandidate).mode = .growing := by
      simpa [relocateBlocks, oldCandidate] using property.1
    have candidateFixed : (state.relocateBlocks after).blocks.get candidate = state.blocks.get oldCandidate := by
      simp only [relocateBlocks, List.get_eq_getElem, List.getElem_map]
      exact Block.relocated_of_growing _ _ _ growing
    rw [candidateFixed] at property
    apply Fin.ext
    exact congrArg (fun id : Fin state.blocks.length => id.val) (unique oldCandidate property)

theorem relocateBlocks_growingTopmost {n : ℕ} {state : State n} (after : HeapView n)
    (prefixes : ∀ block ∈ state.blocks, block.mode = .growing →
      ∃ suffix, after.topDown block.owner block.side = block.elements ++ suffix) :
    (state.relocateBlocks after).GrowingTopmost := by
  intro index
  dsimp only
  intro growing
  let oldId : Fin state.blocks.length := ⟨index.val, by simpa using index.isLt⟩
  have oldGrowing : (state.blocks.get oldId).mode = .growing := by
    simpa [relocateBlocks, oldId] using growing
  have fixed : (state.relocateBlocks after).blocks.get index = state.blocks.get oldId := by
    simp only [relocateBlocks, List.get_eq_getElem, List.getElem_map]
    exact Block.relocated_of_growing _ _ _ oldGrowing
  rw [fixed]
  exact prefixes _ (List.get_mem _ _) oldGrowing

/-- Once the bounded preparation establishes segment geometry and growing
prefixes, simultaneous relocation reaches a stable, numerically ordered heap. -/
theorem relocateBlocks_stable {n : ℕ} {params : Interface.Parameters} {state : State n}
    (prepared : state.RankPrepared params) {after : HeapView n}
    (geometry : state.RelocationGeometry after) (root : after.root = state.view.root)
    (ordered : after.HeapOrdered)
    (prefixes : ∀ block ∈ state.blocks, block.mode = .growing →
      ∃ suffix, after.topDown block.owner block.side = block.elements ++ suffix) :
    (state.relocateBlocks after).Stable params :=
  ⟨relocateBlocks_valid prepared.valid geometry,
    relocateBlocks_complete prepared.complete after root, ordered,
    relocateBlocks_oneGrowingPerSide prepared.oneGrowingPerSide after,
    relocateBlocks_growingTopmost after prefixes,
    relocateBlocks_values prepared.valid prepared.valuesRealizeGaps geometry root⟩

end State
end Splay.Lazy
