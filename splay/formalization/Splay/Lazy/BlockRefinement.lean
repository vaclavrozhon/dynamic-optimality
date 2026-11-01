import Splay.Lazy.SplitBlockCases

namespace Splay.Lazy.State

/-- Every new block is a sublist of an old block at the same placement. -/
def BlockRefinement {n : ℕ} (before after : State n) : Prop :=
  ∀ block ∈ after.blocks, ∃ old ∈ before.blocks,
    block.owner = old.owner ∧ block.side = old.side ∧ block.elements.Sublist old.elements

namespace BlockRefinement

theorem refl {n : ℕ} (state : State n) : state.BlockRefinement state :=
  fun block member => ⟨block, member, rfl, rfl, List.Sublist.refl _⟩

theorem trans {n : ℕ} {first middle last : State n}
    (left : first.BlockRefinement middle) (right : middle.BlockRefinement last) : first.BlockRefinement last := by
  intro block member
  obtain ⟨intermediate, inMiddle, ownerEq, sideEq, sublist⟩ := right block member
  obtain ⟨old, inFirst, oldOwner, oldSide, oldSublist⟩ := left intermediate inMiddle
  exact ⟨old, inFirst, ownerEq.trans oldOwner, sideEq.trans oldSide, sublist.trans oldSublist⟩

/-- Refinement cannot introduce a crossing of an already cleared cut. -/
theorem preserves_clearCut {n : ℕ} {before after : State n}
    (refines : before.BlockRefinement after) (owner : Element n) (side : Side) (cut : ℕ)
    (clear : ∀ block ∈ before.blocks, block.owner = owner → block.side = side → ¬ block.CrossesCut cut) :
    ∀ block ∈ after.blocks, block.owner = owner → block.side = side → ¬ block.CrossesCut cut := by
  intro block member ownerEq sideEq crossing
  obtain ⟨old, oldMember, oldOwner, oldSide, sublist⟩ := refines block member
  apply clear old oldMember (oldOwner.symm.trans ownerEq) (oldSide.symm.trans sideEq)
  obtain ⟨low, lowIn, high, highIn, lowBound, highBound⟩ := crossing
  exact ⟨low, sublist.mem lowIn, high, sublist.mem highIn, lowBound, highBound⟩

end BlockRefinement

/-- A shrinking split refines all blocks without relocating their contents. -/
theorem split_blockRefinement {n : ℕ} (state : State n) (sourceId : Interface.BlockId) (source : Block n)
    (length : ℕ) (prefixGap suffixGap : ℤ) (found : state.blocks[sourceId]? = some source) :
    state.BlockRefinement (state.split sourceId source length prefixGap suffixGap) := by
  intro block member
  have sourceMember := List.mem_of_getElem? found
  rcases state.split_blocks_cases sourceId source length prefixGap suffixGap found member with
    empty | prefixEq | suffixEq | ⟨oldId, oldFound, _⟩
  · subst block
    exact ⟨source, sourceMember, rfl, rfl, List.nil_sublist _⟩
  · subst block
    exact ⟨source, sourceMember, rfl, rfl, List.take_sublist _ _⟩
  · subst block
    exact ⟨source, sourceMember, rfl, rfl, List.drop_sublist _ _⟩
  · exact ⟨block, List.mem_of_getElem? oldFound, rfl, rfl, List.Sublist.refl _⟩

/-- Every growing block present after a shrinking split was already present
literally beforehand. In particular all empty growing slots remain empty. -/
theorem split_growing_blocks_preserved {n : ℕ} (state : State n) (sourceId : Interface.BlockId) (source : Block n)
    (length : ℕ) (prefixGap suffixGap : ℤ) (found : state.blocks[sourceId]? = some source)
    (shrinking : source.mode = .shrinking) :
    ∀ block ∈ (state.split sourceId source length prefixGap suffixGap).blocks,
      block.mode = .growing → block ∈ state.blocks := by
  intro block member growing
  rcases state.split_blocks_cases sourceId source length prefixGap suffixGap found member with
    empty | prefixEq | suffixEq | ⟨oldId, oldFound, _⟩
  · simp [empty, Block.emptiedAfterSplit, shrinking] at growing
  · simp [prefixEq, Block.splitPrefix, shrinking] at growing
  · simp [suffixEq, Block.splitSuffix, shrinking] at growing
  · exact List.mem_of_getElem? oldFound

end Splay.Lazy.State
