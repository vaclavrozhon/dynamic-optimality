import Splay.Lazy.BlockRefinement

namespace Splay.Lazy.State

/-- Every block with a nonzero pass counter descends from an old block at
the same placement, with unchanged counter and a smaller payload. Fresh
growing blocks have counter zero and need no predecessor. -/
def PassRefinement {n : ℕ} (before after : State n) : Prop :=
  ∀ block ∈ after.blocks, block.passCount ≠ 0 → ∃ old ∈ before.blocks,
    block.owner = old.owner ∧ block.side = old.side ∧
      block.elements.Sublist old.elements ∧ block.passCount = old.passCount

namespace PassRefinement

theorem refl {n : ℕ} (state : State n) : state.PassRefinement state :=
  fun block member _ => ⟨block, member, rfl, rfl, List.Sublist.refl _, rfl⟩

theorem trans {n : ℕ} {first middle last : State n}
    (left : first.PassRefinement middle) (right : middle.PassRefinement last) : first.PassRefinement last := by
  intro block member positive
  obtain ⟨intermediate, inMiddle, ownerEq, sideEq, sublist, counter⟩ := right block member positive
  obtain ⟨old, inFirst, oldOwner, oldSide, oldSublist, oldCounter⟩ :=
    left intermediate inMiddle (by simpa only [← counter] using positive)
  exact ⟨old, inFirst, ownerEq.trans oldOwner, sideEq.trans oldSide,
    sublist.trans oldSublist, counter.trans oldCounter⟩

theorem of_blocks_eq {n : ℕ} {before after : State n} (equal : after.blocks = before.blocks) :
    before.PassRefinement after := by
  intro block member _
  exact ⟨block, equal ▸ member, rfl, rfl, List.Sublist.refl _, rfl⟩

end PassRefinement

theorem split_passRefinement {n : ℕ} (state : State n) (sourceId : Interface.BlockId) (source : Block n)
    (length : ℕ) (prefixGap suffixGap : ℤ) (found : state.blocks[sourceId]? = some source) :
    state.PassRefinement (state.split sourceId source length prefixGap suffixGap) := by
  intro block member _
  have sourceMember := List.mem_of_getElem? found
  rcases state.split_blocks_cases sourceId source length prefixGap suffixGap found member with
    empty | prefixEq | suffixEq | ⟨oldId, oldFound, _⟩
  · subst block
    exact ⟨source, sourceMember, rfl, rfl, List.nil_sublist _, rfl⟩
  · subst block
    exact ⟨source, sourceMember, rfl, rfl, List.take_sublist _ _, rfl⟩
  · subst block
    exact ⟨source, sourceMember, rfl, rfl, List.drop_sublist _ _, rfl⟩
  · exact ⟨block, List.mem_of_getElem? oldFound, rfl, rfl, List.Sublist.refl _, rfl⟩

theorem convert_passRefinement {n : ℕ} (state : State n) (sourceId : Interface.BlockId) (gap : ℤ) :
    state.PassRefinement (state.convert sourceId gap) := by
  intro block member _
  obtain ⟨id, found⟩ := List.mem_iff_getElem?.mp member
  change (state.blocks.modify sourceId (fun old => old.converted gap))[id]? = some block at found
  rw [List.getElem?_modify] at found
  split at found
  · obtain ⟨old, oldFound, equal⟩ := Option.map_eq_some_iff.mp found
    subst block
    exact ⟨old, List.mem_of_getElem? oldFound, rfl, rfl, List.Sublist.refl _, rfl⟩
  · have oldFound : state.blocks[id]? = some block := by simpa using found
    exact ⟨block, List.mem_of_getElem? oldFound, rfl, rfl, List.Sublist.refl _, rfl⟩

theorem create_passRefinement {n : ℕ} (state : State n) (owner : Element n) (side : Side) :
    state.PassRefinement (state.create owner side) := by
  intro block member positive
  rcases List.mem_append.mp member with old | fresh
  · exact ⟨block, old, rfl, rfl, List.Sublist.refl _, rfl⟩
  · have equal := List.mem_singleton.mp fresh
    exact (positive (by rw [equal]; rfl)).elim

end Splay.Lazy.State
