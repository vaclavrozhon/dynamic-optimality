import Splay.Lazy.RankUpdateTrace

namespace Splay.Lazy

namespace State

/--
Concrete blockwise criterion for absorbing a pointwise rank update.

Growing blocks may contain only children whose rank shift equals their
owner's.  Every nonempty shrinking block may have a different common child
shift; its stored interval gap is shifted by the difference between that
common child shift and the owner's shift.  Empty shrinking blocks keep their
administrative zero gap.

Thus the only blocks that must first be split or converted are precisely
those crossing a boundary of the pointwise shift function.
-/
structure BlockwiseUniformRankShift {n : ℕ}
    (state : State n) (afterView : HeapView n)
    (elementShift : Element n → ℤ)
    (blockShift : Block n → ℤ) : Prop where
  sameStructure : state.view.SameStructure afterView
  rankShift :
    ∀ element,
      HeapView.RankShift state.view afterView element
        (elementShift element)
  growing :
    ∀ block ∈ state.blocks, block.mode = .growing →
      blockShift block = 0 ∧
        ∀ element ∈ block.elements,
          elementShift element = elementShift block.owner
  shrinking_empty :
    ∀ block ∈ state.blocks, block.mode = .shrinking →
      block.elements = [] → blockShift block = 0
  shrinking_nonempty :
    ∀ block ∈ state.blocks, block.mode = .shrinking →
      block.elements ≠ [] →
        ∃ childShift : ℤ,
          (∀ element ∈ block.elements,
            elementShift element = childShift) ∧
          blockShift block =
            childShift - elementShift block.owner

namespace BlockwiseUniformRankShift

/--
The blockwise uniformity criterion discharges the lower-level
`RankUpdateCompatible` predicate used by the silent rank-update primitive.
-/
theorem compatible {n : ℕ}
    {state : State n} {afterView : HeapView n}
    {elementShift : Element n → ℤ}
    {blockShift : Block n → ℤ}
    {params : Interface.Parameters}
    (uniform :
      BlockwiseUniformRankShift
        state afterView elementShift blockShift)
    (valid : state.Valid params) :
    state.RankUpdateCompatible afterView blockShift := by
  refine ⟨uniform.sameStructure, ?_⟩
  intro block member
  cases hMode : block.mode with
  | growing =>
      have hGrowing := uniform.growing block member hMode
      simp only [Block.AbsorbsRankUpdate, hMode]
      refine ⟨hGrowing.1, ?_⟩
      intro element elementMember
      exact
        HeapView.rawGap_eq_of_equal_rankShift uniform.sameStructure
          ((valid.2 block member).parent_eq elementMember)
          (uniform.rankShift element)
          (by
            rw [hGrowing.2 element elementMember]
            exact uniform.rankShift block.owner)
  | shrinking =>
      simp only [Block.AbsorbsRankUpdate, hMode]
      by_cases hEmpty : block.elements = []
      · exact Or.inl
          ⟨hEmpty,
            uniform.shrinking_empty block member hMode hEmpty⟩
      · obtain ⟨childShift, hChildren, hBlockShift⟩ :=
          uniform.shrinking_nonempty block member hMode hEmpty
        refine Or.inr ⟨hEmpty, ?_⟩
        intro element elementMember
        rw [hBlockShift]
        exact
          HeapView.rawGap_eq_add_sub_of_rankShifts
            uniform.sameStructure
            ((valid.2 block member).parent_eq elementMember)
            (by
              rw [← hChildren element elementMember]
              exact uniform.rankShift element)
            (uniform.rankShift block.owner)

end BlockwiseUniformRankShift

/--
A blockwise-uniform comparison-rank update is a one-silent-event rich trace.
-/
theorem absorbRankUpdate_trace_of_blockwiseUniform {n : ℕ}
    {state : State n} {afterView : HeapView n}
    {elementShift : Element n → ℤ}
    {blockShift : Block n → ℤ}
    {params : Interface.Parameters}
    (valid : state.Valid params)
    (uniform :
      BlockwiseUniformRankShift
        state afterView elementShift blockShift) :
    Trace params state [.silent]
      (state.absorbRankUpdate afterView blockShift) :=
  state.absorbRankUpdate_trace valid (uniform.compatible valid)

end State

end Splay.Lazy
