import Splay.Lazy.BoundaryRelocationStable

namespace Splay.Lazy.HeapView

/-- One true outermost pairing has exactly the required growing-prefix
geometry, independently of whether the endpoints share a lazy interval. -/
theorem reparentOne_topDown_eq_cons {n : ℕ} (view : HeapView n)
    (winner loser : Element n) (side : Side)
    (ordered : view.HeapOrdered) (notRoot : loser ≠ view.root)
    (rankLt : view.rank winner < view.rank loser)
    (sideOrder : match side with | .left => loser.val < winner.val | .right => winner.val < loser.val)
    (outermost : ∀ child ∈ view.topDown winner side,
      if side = .left then loser.val < child.val else child.val < loser.val) :
    (view.reparentOne winner loser side ordered notRoot rankLt sideOrder).topDown winner side =
      loser :: view.topDown winner side := by
  let after := view.reparentOne winner loser side ordered notRoot rankLt sideOrder
  have membership : ∀ queried, queried ∈ after.topDown winner side ↔
      queried ∈ loser :: view.topDown winner side := by
    intro queried
    by_cases equal : queried = loser
    · subst queried
      simp [after, HeapView.mem_topDown_iff]
    · simp only [List.mem_cons, equal, false_or, HeapView.mem_topDown_iff,
        after, reparentOne_parent, reparentOne_side, ↓reduceIte]
  cases side with
  | left =>
      have tailOrder := (view.topDown_ordered winner).1
      have fullOrder := (after.topDown_ordered winner).1
      exact List.Pairwise.eq_of_mem_iff fullOrder (List.pairwise_cons.mpr ⟨by simpa using outermost, tailOrder⟩) membership
  | right =>
      have tailOrder := (view.topDown_ordered winner).2
      have fullOrder := (after.topDown_ordered winner).2
      exact List.Pairwise.eq_of_mem_iff fullOrder (List.pairwise_cons.mpr ⟨by simpa using outermost, tailOrder⟩) membership

end Splay.Lazy.HeapView

namespace Splay.Lazy.State

/-- Construct a stable boundary-pairing macro from its actual rank order and
outermost-child inequality. The reparented heap view is constructed here. -/
theorem exists_stableBoundaryPairing {n : ℕ} {params : Interface.Parameters} {state : State n}
    (stable : state.Stable params)
    {sourceId destinationId : Interface.BlockId} {source destination : Block n}
    (sourceFound : state.blocks[sourceId]? = some source) (sourceShrinking : source.mode = .shrinking)
    (destinationFound : state.blocks[destinationId]? = some destination)
    (destinationGrowing : destination.mode = .growing)
    (loser : Element n) (member : loser ∈ source.elements)
    (rankLt : state.view.rank destination.owner < state.view.rank loser)
    (sideOrder : match destination.side with
      | .left => loser.val < destination.owner.val
      | .right => destination.owner.val < loser.val)
    (outermost : ∀ child ∈ state.view.topDown destination.owner destination.side,
      if destination.side = .left then loser.val < child.val else child.val < loser.val)
    (bounded : Analysis.contractedGap (state.view.rank loser - state.view.rank destination.owner) ≤ params.valueBound) :
    ∃ afterView, ∃ relocation : BoundaryRelocation params state sourceId destinationId loser afterView,
      relocation.final.Stable params ∧
        relocation.final.view.parent loser = some destination.owner ∧
        relocation.final.view.side loser = destination.side := by
  have notRoot : loser ≠ state.view.root := by
    intro equal
    have assigned := State.mem_allElements_iff.mpr ⟨source, List.mem_of_getElem? sourceFound, member⟩
    exact stable.valid.root_not_mem (equal ▸ assigned)
  let after := state.view.reparentOne destination.owner loser destination.side stable.2.2.1 notRoot rankLt sideOrder
  have afterOrdered : after.HeapOrdered := state.view.reparentOne_heapOrdered
    destination.owner loser destination.side stable.2.2.1 notRoot rankLt sideOrder
  have paired : after.parent loser = some destination.owner := by simp [after]
  have rawGap : after.rawGap loser = (state.view.rank loser : ℤ) - state.view.rank destination.owner := by
    simp [HeapView.rawGap, after]
  have gapNonnegative : 0 ≤ after.rawGap loser := by rw [rawGap]; omega
  have afterBounded : Analysis.transientContractedGap (after.rawGap loser) 0 ≤ params.valueBound := by
    simpa only [Analysis.transientContractedGap, Analysis.transientPointGap, rawGap,
      sub_zero, Int.toNat_sub, Int.toNat_natCast] using bounded
  let destinationIndex : Fin state.blocks.length :=
    ⟨destinationId, (List.getElem?_eq_some_iff.mp destinationFound).1⟩
  have destinationGet : state.blocks.get destinationIndex = destination :=
    (List.getElem?_eq_some_iff.mp destinationFound).2
  have destinationMode : (state.blocks.get destinationIndex).mode = .growing := by
    rw [destinationGet]
    exact destinationGrowing
  obtain ⟨suffix, oldPrefix⟩ := stable.2.2.2.2.1 destinationIndex destinationMode
  change state.view.topDown (state.blocks.get destinationIndex).owner (state.blocks.get destinationIndex).side =
    (state.blocks.get destinationIndex).elements ++ suffix at oldPrefix
  rw [destinationGet] at oldPrefix
  have newPrefix := state.view.reparentOne_topDown_eq_cons destination.owner loser destination.side
    stable.2.2.1 notRoot rankLt sideOrder outermost
  obtain ⟨relocation⟩ := exists_boundaryRelocation stable.valid stable.2.2.2.2.2
    sourceFound sourceShrinking destinationFound destinationGrowing loser member after rfl rfl
    (by intro queried different; simp [after, different]) gapNonnegative afterBounded
    ⟨suffix, by rw [newPrefix, oldPrefix]; rfl⟩
  refine ⟨after, relocation, relocation.stable stable afterOrdered, ?_, ?_⟩
  · rw [relocation.view_eq]
    exact paired
  · rw [relocation.view_eq]
    simp [after]

end Splay.Lazy.State
