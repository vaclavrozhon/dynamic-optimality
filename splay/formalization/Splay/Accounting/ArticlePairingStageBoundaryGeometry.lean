import Splay.Accounting.ArticlePairingStageGeometry
import Splay.Accounting.ArticleReparentedRootGeometry

namespace Splay.Accounting

open Splay.Lazy Splay.Lazy.Canonical Splay.Rank Splay.Tree.BST

/-- Neither terminal boundary occurs in the proper-ancestor child order. -/
theorem boundary_not_mem_proper_order {n : ℕ} (snapshot : Snapshot n)
    (before : BST 0 n) (key : Fin n) (rankZero : snapshot.rank (valuePos key) = 0)
    (side : Side) :
    let selection := WholeSplayTemporaryBoundaryGeometry.KeyFocus.boundaryMinimumSelection snapshot before key
    let boundary := if side = .left then selection.left else selection.right
    boundary ∉ (rootHeavyPathCanonicalChildOrder snapshot before key.isLt rankZero).elements := by
  let selection := WholeSplayTemporaryBoundaryGeometry.KeyFocus.boundaryMinimumSelection snapshot before key
  let boundary := if side = .left then selection.left else selection.right
  let proper := (rootHeavyPathCanonicalChildOrder snapshot before key.isLt rankZero).elements
  have orderEq : (canonicalHeapView snapshot before).topDown (valuePos key) side =
      proper.filter (fun child => decide (canonicalSide snapshot before child = side)) ++ [boundary] := by
    cases side <;> simpa [proper, boundary, selection] using
      canonicalTopDown_eq_proper_filter_append_boundary snapshot before key rankZero _
  have boundaryMember : boundary ∈ (canonicalHeapView snapshot before).topDown (valuePos key) side := by
    rw [orderEq]
    simp
  have sideEq : canonicalSide snapshot before boundary = side :=
    ((canonicalHeapView snapshot before).mem_topDown_iff.mp boundaryMember).2
  have distinct := (canonicalHeapView snapshot before).topDown_nodup (valuePos key) side
  rw [orderEq] at distinct
  change boundary ∉ proper
  intro member
  have filtered : boundary ∈ proper.filter (fun child => decide (canonicalSide snapshot before child = side)) :=
    List.mem_filter.mpr ⟨member, by simp [sideEq]⟩
  exact (List.nodup_append.mp distinct).2.2 boundary filtered boundary (by simp) rfl

namespace ArticlePairingStage

variable {n : ℕ} {params : Interface.Parameters} {snapshot : Snapshot n}
  {before : BST 0 n} {key : Fin n} {kinds : List SplayStepKind} {initial : Lazy.State n}
  (stage : ArticlePairingStage params snapshot before key kinds initial)

theorem endpoint_mem_proper {pairing : Interface.Pairing n} (member : pairing ∈ stage.matching)
    {element : Element n} (endpoint : element ∈ [pairing.winner, pairing.loser]) :
    element ∈ (rootHeavyPathCanonicalChildOrder snapshot before key.isLt stage.rankZero).elements := by
  obtain ⟨row, rowMember, phase, selected⟩ := stage.rows_sound member
  have inside : element ∈ row.2.1 ++ row.2.2 := by
    cases phase with
    | first =>
        apply List.mem_append_left
        change row.2.1 = _ at selected
        rw [selected]
        exact endpoint
    | second =>
        apply List.mem_append_right
        change row.2.2 = _ at selected
        rw [selected]
        exact endpoint
  have chunk := stage.allBatches.endpoint_mem_chunk rowMember inside
  have bottom := List.mem_of_mem_drop (List.mem_of_mem_take chunk)
  simpa [rootHeavyPathCanonicalChildOrder, rootHeavyPathChildrenBottomUp,
    rootHeavyPathChildrenTopDown, rootHeavyPathEdgesBottomUp, List.map_reverse] using bottom

/-- Actual pairings never touch either of the isolated terminal boundaries. -/
theorem endpoints_ne_boundary (side : Side) {pairing : Interface.Pairing n} (member : pairing ∈ stage.matching) :
    let selection := WholeSplayTemporaryBoundaryGeometry.KeyFocus.boundaryMinimumSelection snapshot before key
    let boundary := if side = .left then selection.left else selection.right
    pairing.winner ≠ boundary ∧ pairing.loser ≠ boundary := by
  have outside := boundary_not_mem_proper_order snapshot before key stage.rankZero side
  constructor
  · intro equal
    apply outside
    rw [← equal]
    exact stage.endpoint_mem_proper member (by simp)
  · intro equal
    apply outside
    rw [← equal]
    exact stage.endpoint_mem_proper member (by simp)

/-- Both endpoints of every actually executed pair belonged to the original
root child order, including pairs implemented by boundary relocation. -/
theorem matching_parents {pairing : Interface.Pairing n} (member : pairing ∈ stage.matching) :
    stage.preparation.final.view.parent pairing.winner = some stage.preparation.final.view.root ∧
      stage.preparation.final.view.parent pairing.loser = some stage.preparation.final.view.root := by
  have root : stage.preparation.final.view.root = valuePos key := by
    rw [stage.preparation.represents.view_eq]
    exact canonicalRoot_eq_of_rank_eq_zero snapshot before stage.rankZero
  rw [root, stage.preparation.represents.view_eq]
  have parents := (rootHeavyPathCanonicalChildOrder snapshot before key.isLt stage.rankZero).parent
  exact ⟨parents _ (stage.endpoint_mem_proper member (by simp)),
    parents _ (stage.endpoint_mem_proper member (by simp))⟩

/-- The post-preparation trace ends exactly the residences of the actual
pairing losers, regardless of how internal and boundary rows were split. -/
theorem pairing_leaving :
    operationLeavingElementsList (eraseOperations (stage.internal.chain.events ++ stage.boundary.events)) =
      Interface.pairingLosers stage.matching := by
  rw [eraseOperations_append, operationLeavingElementsList_append,
    stage.internal.chain.leavingElements_eq, stage.boundary.leaving]
  simp only [matching, Interface.pairingLosers, List.map_append,
    ArticleSourceMacroChain.matching, List.map_flatMap]

/-- Each isolated boundary still occupies an actual shrinking singleton after
all internal passes and both boundary relocation phases. -/
theorem boundary_singleton (side : Side) :
    let selection := WholeSplayTemporaryBoundaryGeometry.KeyFocus.boundaryMinimumSelection snapshot before key
    let boundary := if side = .left then selection.left else selection.right
    ∃ (id : Interface.BlockId) (block : Lazy.Block n), stage.final.blocks[id]? = some block ∧
      block.mode = .shrinking ∧ block.elements = [boundary] := by
  let selection := WholeSplayTemporaryBoundaryGeometry.KeyFocus.boundaryMinimumSelection snapshot before key
  let boundary := if side = .left then selection.left else selection.right
  have initialSingleton : ∃ (id : Interface.BlockId) (block : Lazy.Block n),
      stage.preparation.final.blocks[id]? = some block ∧ block.mode = .shrinking ∧ block.elements = [boundary] := by
    cases side with
    | left =>
        exact ⟨stage.preparation.leftId, stage.preparation.leftBlock, stage.preparation.leftFound,
          stage.preparation.leftShrinking, stage.preparation.leftElements⟩
    | right =>
        exact ⟨stage.preparation.rightId, stage.preparation.rightBlock, stage.preparation.rightFound,
          stage.preparation.rightShrinking, stage.preparation.rightElements⟩
  obtain ⟨id, block, found, shrinking, singleton⟩ := initialSingleton
  apply shrinkingSingleton_after_trace (stage.internal.chain.trace.append stage.boundary.trace) found shrinking singleton
  rw [stage.pairing_leaving]
  intro member
  obtain ⟨pairing, pairingMember, equal⟩ := List.mem_map.mp member
  exact (stage.endpoints_ne_boundary side pairingMember).2 equal

/-- The whole actual pairing stage leaves a transferable prefix on either
side when the isolated boundary has smaller rank than the other root children. -/
theorem exists_sideTransferGeometry (side : Side)
    (ranks :
      let selection := WholeSplayTemporaryBoundaryGeometry.KeyFocus.boundaryMinimumSelection snapshot before key
      let boundary := if side = .left then selection.left else selection.right
      ∀ element ∈ (canonicalHeapView snapshot before).topDown (valuePos key) side,
        element ≠ boundary → snapshot.rank boundary < snapshot.rank element) :
    let selection := WholeSplayTemporaryBoundaryGeometry.KeyFocus.boundaryMinimumSelection snapshot before key
    let boundary := if side = .left then selection.left else selection.right
    Nonempty (SideTransferGeometry stage.final.view (valuePos key) boundary side) := by
  let selection := WholeSplayTemporaryBoundaryGeometry.KeyFocus.boundaryMinimumSelection snapshot before key
  let boundary := if side = .left then selection.left else selection.right
  let front := (rootHeavyPathCanonicalChildOrder snapshot before key.isLt stage.rankZero).elements.filter
    (fun child => decide (canonicalSide snapshot before child = side))
  have root : stage.preparation.final.view.root = valuePos key := by
    rw [stage.preparation.represents.view_eq]
    exact canonicalRoot_eq_of_rank_eq_zero snapshot before stage.rankZero
  have decomposition : stage.preparation.final.view.topDown stage.preparation.final.view.root side = front ++ [boundary] := by
    rw [root, stage.preparation.represents.view_eq]
    cases side <;> simpa [front, boundary, selection] using
      canonicalTopDown_eq_proper_filter_append_boundary snapshot before key stage.rankZero _
  obtain ⟨afterView, viewEq⟩ := stage.exists_reparented
  have result := afterView.exists_sideTransferGeometry (fun pairing member => stage.matching_parents member) boundary side front decomposition
    (fun pairing member => stage.endpoints_ne_boundary side member) (by
      intro element member
      rw [stage.preparation.represents.view_eq]
      change snapshot.rank boundary < snapshot.rank element
      apply ranks element
      · rw [← stage.preparation.represents.view_eq, ← root, decomposition]
        exact List.mem_append_left _ member
      · intro equal
        have outside := boundary_not_mem_proper_order snapshot before key stage.rankZero side
        exact outside (equal ▸ (List.mem_filter.mp member).1)) (by
      rw [stage.preparation.represents.view_eq]
      exact canonicalHeapView_nestedChildOrder snapshot before)
  rw [viewEq, root] at result
  exact result

end ArticlePairingStage
end Splay.Accounting
