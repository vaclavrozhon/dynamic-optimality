import Splay.Lazy.CutPartition

namespace Splay.Lazy.State

/-- Exact origin of every block after a rich split: the empty administrative
source, one of its two fresh pieces, or an unchanged different old ID. -/
theorem split_blocks_cases {n : ℕ} (state : State n) (sourceId : Interface.BlockId) (source : Block n)
    (length : ℕ) (prefixGap suffixGap : ℤ) (found : state.blocks[sourceId]? = some source)
    {block : Block n} (member : block ∈ (state.split sourceId source length prefixGap suffixGap).blocks) :
    block = source.emptiedAfterSplit ∨ block = source.splitPrefix length prefixGap ∨
      block = source.splitSuffix length suffixGap ∨
        ∃ oldId, state.blocks[oldId]? = some block ∧ oldId ≠ sourceId := by
  change block ∈ state.blocks.modify sourceId Block.emptiedAfterSplit ++
    [source.splitPrefix length prefixGap, source.splitSuffix length suffixGap] at member
  rcases List.mem_append.mp member with modified | pieces
  · obtain ⟨oldId, oldFound⟩ := List.mem_iff_getElem?.mp modified
    rw [List.getElem?_modify] at oldFound
    split at oldFound
    next selected =>
      have atSource : state.blocks[oldId]? = some source := by simpa only [selected] using found
      rw [atSource] at oldFound
      exact Or.inl (by simpa using oldFound.symm)
    next untouched =>
      exact Or.inr (Or.inr (Or.inr ⟨oldId, by simpa using oldFound, by simpa [eq_comm] using untouched⟩))
  · rcases List.mem_cons.mp pieces with prefixEq | suffixEq
    · exact Or.inr (Or.inl prefixEq)
    · exact Or.inr (Or.inr (Or.inl (List.mem_singleton.mp suffixEq)))

/-- A numerical cut split removes every crossing at this owner and side.
Any other alleged crossing would already have shared the unique source ID. -/
theorem split_cut_no_crossing {n : ℕ} {params : Interface.Parameters} (state : State n)
    (valid : state.Valid params) (sourceId : Interface.BlockId) (source : Block n) (cut : ℕ)
    (prefixGap suffixGap : ℤ) (found : state.blocks[sourceId]? = some source)
    (crosses : source.CrossesCut cut) :
    ∀ block ∈ (state.split sourceId source (source.cutPrefixLength cut) prefixGap suffixGap).blocks,
      block.owner = source.owner → block.side = source.side → ¬ block.CrossesCut cut := by
  have segment := (valid.2 source (List.mem_of_getElem? found)).isSegment
  have order : source.elements.Pairwise (fun a b => match source.side with
      | .left => a.val < b.val | .right => b.val < a.val) := by
    have sublist := Splay.Lazy.Canonical.IsSegment.sublist segment
    cases side : source.side with
    | left =>
        rw [side] at sublist
        exact (((state.view.topDown_ordered source.owner).1.filter _).sublist sublist)
    | right =>
        rw [side] at sublist
        exact (((state.view.topDown_ordered source.owner).2.filter _).sublist sublist)
  have pieces := source.cut_split_not_crosses cut prefixGap suffixGap order
  intro block member ownerEq sideEq crossing
  rcases state.split_blocks_cases sourceId source _ prefixGap suffixGap found member with
    empty | prefixEq | suffixEq | ⟨oldId, oldFound, different⟩
  · rw [empty] at crossing
    simp [Block.CrossesCut, Block.emptiedAfterSplit] at crossing
  · exact pieces.1 (prefixEq ▸ crossing)
  · exact pieces.2 (suffixEq ▸ crossing)
  · exact different (valid.blockId_eq_of_crossesCut oldFound found ownerEq sideEq cut crossing crosses)

end Splay.Lazy.State
