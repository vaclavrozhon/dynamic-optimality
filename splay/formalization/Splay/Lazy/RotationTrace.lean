import Splay.Lazy.UniformRankUpdate
import Splay.Rank.SplayUpdate

namespace Splay.Lazy

open Splay.Rank

namespace State

/--
Purely combinatorial alignment of lazy blocks with a pointwise comparison-rank
shift.  This omits the rank equations themselves; those are supplied by an
`ExactTreeRankUpdate`.
-/
structure BlocksAlignedWithShift {n : ℕ}
    (state : State n) (elementShift : Element n → ℤ)
    (blockShift : Block n → ℤ) : Prop where
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

/--
An exact comparison-tree rank update whose sectors align with the current
blocks is realized by one silent rich lazy event.

This theorem is the checked rank-update half of the rotation-to-trace bridge:
the remaining structural macro must split/convert the finitely many blocks
that cross shift-sector boundaries and establish `BlocksAlignedWithShift`.
-/
theorem trace_of_exactTreeRankUpdate {n : ℕ}
    {beforeTree afterTree : Tree.BST 0 n}
    {elementShiftAt : ℕ → ℤ}
    (update :
      ExactTreeRankUpdate beforeTree afterTree elementShiftAt)
    {state : State n} {afterView : HeapView n}
    {blockShift : Block n → ℤ}
    {params : Interface.Parameters}
    (valid : state.Valid params)
    (sameStructure : state.view.SameStructure afterView)
    (beforeRanks :
      state.view.rank = (Snapshot.ofTree beforeTree).rank)
    (afterRanks :
      afterView.rank = (Snapshot.ofTree afterTree).rank)
    (aligned :
      state.BlocksAlignedWithShift
        (fun element => elementShiftAt element.val) blockShift) :
    Trace params state [.silent]
      (state.absorbRankUpdate afterView blockShift) := by
  apply state.absorbRankUpdate_trace_of_blockwiseUniform valid
  exact {
    sameStructure
    rankShift := fun element =>
      update.heapViewRankShift beforeRanks afterRanks element
    growing := aligned.growing
    shrinking_empty := aligned.shrinking_empty
    shrinking_nonempty := aligned.shrinking_nonempty
  }

end State

end Splay.Lazy

namespace Splay.Tree.BST.RotationAt

open Splay.Lazy
open Splay.Rank

/--
Every contextual comparison-tree rotation exports a unit-valued exact shift.
If the caller has prepared lazy blocks for whichever exact sector witness is
chosen, that shift is immediately realized as a one-event rich trace.
-/
theorem exists_lazyRankUpdateTrace_of_aligned
    {n depth : ℕ}
    {beforeTree afterTree : Tree.BST 0 n}
    (rotation : RotationAt depth beforeTree afterTree)
    {state : State n} {afterView : HeapView n}
    {params : Interface.Parameters}
    (valid : state.Valid params)
    (sameStructure : state.view.SameStructure afterView)
    (beforeRanks :
      state.view.rank = (Snapshot.ofTree beforeTree).rank)
    (afterRanks :
      afterView.rank = (Snapshot.ofTree afterTree).rank)
    (prepare :
      ∀ elementShiftAt : ℕ → ℤ,
        ExactTreeRankUpdate beforeTree afterTree elementShiftAt →
          IsUnitRotationShift elementShiftAt →
          ∃ blockShift : Block n → ℤ,
            state.BlocksAlignedWithShift
              (fun element => elementShiftAt element.val) blockShift) :
    ∃ (elementShiftAt : ℕ → ℤ) (blockShift : Block n → ℤ),
      IsUnitRotationShift elementShiftAt ∧
        Trace params state [.silent]
          (state.absorbRankUpdate afterView blockShift) := by
  obtain ⟨elementShiftAt, update, unitShift⟩ :=
    rotation.existsExactTreeRankUpdate
  obtain ⟨blockShift, aligned⟩ :=
    prepare elementShiftAt update unitShift
  refine ⟨elementShiftAt, blockShift, unitShift, ?_⟩
  exact
    state.trace_of_exactTreeRankUpdate update valid sameStructure
      beforeRanks afterRanks aligned

end Splay.Tree.BST.RotationAt
