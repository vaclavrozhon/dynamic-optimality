import Splay.Lazy.IsolatedRankUpdate
import Splay.Lazy.TwoSideTransfer
import Splay.Lazy.DetachedReparenting

namespace Splay.Lazy.State.IsolatedRanks

/-- A real shrinking singleton residence identifies every containing block,
by the interface's element disjointness. -/
theorem of_singleton_blocks {n : ℕ} {params : Interface.Parameters} {state : State n}
    {selected : Finset (Element n)} (valid : state.Valid params)
    (empty : ∀ block ∈ state.blocks, block.mode = .growing → block.owner ∈ selected → block.elements = [])
    (singletons : ∀ element ∈ selected, ∃ (id : Interface.BlockId) (block : Block n),
      state.blocks[id]? = some block ∧ block.mode = .shrinking ∧ block.elements = [element]) :
    state.IsolatedRanks selected := by
  refine ⟨empty, ?_⟩
  intro element marked other otherMember inside
  obtain ⟨id, block, found, shrinking, singleton⟩ := singletons element marked
  obtain ⟨otherId, otherFound⟩ := List.mem_iff_getElem?.mp otherMember
  have equal := valid.blockId_eq_of_element_mem found (by simp [singleton]) otherFound inside
  rw [← equal, found] at otherFound
  cases Option.some.inj otherFound
  exact ⟨shrinking, singleton⟩

/-- Whole-block transfers preserve finite rank-isolation readiness: each
payload and mode stays fixed, and each growing block stays literally fixed. -/
theorem transferSide {n : ℕ} {state : State n} {selected : Finset (Element n)}
    (prepared : state.IsolatedRanks selected) {source boundary : Element n} {side : Side}
    (geometry : SideTransferGeometry state.view source boundary side) (ordered : state.view.HeapOrdered) :
    (state.transferSide geometry ordered).IsolatedRanks selected := by
  constructor
  · intro block member growing ownerMarked
    obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
    have oldGrowing : original.mode = .growing := by simpa only [Block.sideTransferred_mode] using growing
    rw [Block.sideTransferred_of_growing _ _ _ _ _ oldGrowing] at ownerMarked ⊢
    exact prepared.growingEmpty original originalMember oldGrowing ownerMarked
  · intro element marked block member inside
    obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
    have oldInside : element ∈ original.elements := by simpa only [Block.sideTransferred_elements] using inside
    simpa only [Block.sideTransferred_mode, Block.sideTransferred_elements] using
      prepared.singleton element marked original originalMember oldInside

/-- Both sequential side transfers retain the same isolated rank-change set. -/
theorem transferBothSides {n : ℕ} {state : State n} {selected : Finset (Element n)}
    (prepared : state.IsolatedRanks selected) {source left right : Element n}
    (first : SideTransferGeometry state.view source left .left)
    (second : SideTransferGeometry state.view source right .right) (ordered : state.view.HeapOrdered) :
    (state.transferBothSides first second ordered).IsolatedRanks selected :=
  (prepared.transferSide first ordered).transferSide (first.afterLeft second ordered) (first.after_ordered ordered)

/-- Canonical replacement changes no block data used by rank isolation. -/
theorem replaceView {n : ℕ} {state : State n} {selected : Finset (Element n)}
    (prepared : state.IsolatedRanks selected) (view : HeapView n) :
    (state.replaceView view).IsolatedRanks selected := ⟨prepared.growingEmpty, prepared.singleton⟩

/-- Isolated rank changes retain a rank-prepared checkpoint even when the
new numeric priorities require subsequent heavy-path junctions. -/
theorem trace_rankPrepared {n : ℕ} {state : State n} {selected : Finset (Element n)}
    (isolated : state.IsolatedRanks selected) {params : Interface.Parameters}
    (prepared : state.RankPrepared params) (afterView : HeapView n)
    (same : state.view.SameStructure afterView)
    (ordinary : ∀ element ∉ selected, afterView.rank element = state.view.rank element) :
    Trace params state [.silent] (state.absorbRankUpdate afterView (state.isolatedRankBlockShift afterView)) ∧
      (state.absorbRankUpdate afterView (state.isolatedRankBlockShift afterView)).RankPrepared params := by
  have compatible := isolated.compatible prepared.valid same ordinary
  exact ⟨prepared.absorbRankUpdate_trace compatible, prepared.absorbRankUpdate compatible⟩

end Splay.Lazy.State.IsolatedRanks
