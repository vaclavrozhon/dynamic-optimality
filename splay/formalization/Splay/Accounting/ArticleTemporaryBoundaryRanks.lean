import Splay.Accounting.ArticleTemporaryPreparation

namespace Splay.Accounting.ArticleTemporaryPreparation

open Splay.Lazy Splay.Lazy.Canonical Splay.Rank Splay.Tree.BST

variable {n : ℕ} {params : Interface.Parameters} {snapshot : Snapshot n}
  {before : BST 0 n} {key : Fin n} {initial : Lazy.State n}
  (setup : ArticleTemporaryPreparation params snapshot before key initial)

theorem temporary_rank_zero : setup.temporarySnapshot.rank (valuePos key) = 0 := by
  let selection := WholeSplayTemporaryBoundaryGeometry.KeyFocus.boundaryMinimumSelection snapshot.withTruePriority before key
  have leftNe : valuePos key ≠ selection.left := ne_of_gt selection.ordered.1
  have rightNe : valuePos key ≠ selection.right := ne_of_lt selection.ordered.2
  change twoBoundaryTemporaryRank snapshot selection.left selection.right (valuePos key) = 0
  rw [twoBoundaryTemporaryRank_eq_truePriority _ _ _ _ ⟨leftNe, rightNe⟩, setup.rankZero]
  rfl

/-- The actual priority preparation preserves the full canonical child lists. -/
theorem canonical_topDown_eq (owner : Element n) (side : Side) :
    (canonicalHeapView setup.temporarySnapshot before).topDown owner side =
      (canonicalHeapView snapshot.withTruePriority before).topDown owner side := by
  have parents := setup.canonical_agreement.2.1
  have sides := setup.canonical_agreement.2.2
  change canonicalParent setup.temporarySnapshot before = setup.preparation.final.view.parent at parents
  change canonicalSide setup.temporarySnapshot before = setup.preparation.final.view.side at sides
  rw [setup.preparation.represents.view_eq] at parents sides
  change orderedChildren (canonicalParent setup.temporarySnapshot before) (canonicalSide setup.temporarySnapshot before) owner side = _
  rw [parents, sides]
  rfl

/-- The boundaries automatically selected under temporary priorities are
the very same two concrete vertices which the preparation isolated. -/
theorem boundary_selection_eq :
    let oldSelection := WholeSplayTemporaryBoundaryGeometry.KeyFocus.boundaryMinimumSelection snapshot.withTruePriority before key
    let newSelection := WholeSplayTemporaryBoundaryGeometry.KeyFocus.boundaryMinimumSelection setup.temporarySnapshot before key
    newSelection.left = oldSelection.left ∧ newSelection.right = oldSelection.right := by
  have zero : snapshot.withTruePriority.rank (valuePos key) = 0 := by simp [setup.rankZero]
  have leftEq := setup.canonical_topDown_eq (valuePos key) .left
  have rightEq := setup.canonical_topDown_eq (valuePos key) .right
  rw [canonicalTopDown_eq_proper_filter_append_boundary setup.temporarySnapshot before key setup.temporary_rank_zero,
    canonicalTopDown_eq_proper_filter_append_boundary snapshot.withTruePriority before key zero] at leftEq rightEq
  exact ⟨by simpa using congrArg List.getLast? leftEq, by simpa using congrArg List.getLast? rightEq⟩

/-- Every other child on the boundary's own side has strictly greater
artificial rank. This discharges the remaining numeric premise of transfer. -/
theorem boundary_rank_lt (side : Side) :
    let selection := WholeSplayTemporaryBoundaryGeometry.KeyFocus.boundaryMinimumSelection setup.temporarySnapshot before key
    let boundary := if side = .left then selection.left else selection.right
    ∀ element ∈ (canonicalHeapView setup.temporarySnapshot before).topDown (valuePos key) side,
      element ≠ boundary → setup.temporarySnapshot.rank boundary < setup.temporarySnapshot.rank element := by
  let oldSelection := WholeSplayTemporaryBoundaryGeometry.KeyFocus.boundaryMinimumSelection snapshot.withTruePriority before key
  let boundary := if side = .left then oldSelection.left else oldSelection.right
  have selectedEq := setup.boundary_selection_eq
  dsimp only at selectedEq ⊢
  rw [selectedEq.1, selectedEq.2]
  change ∀ element ∈ (canonicalHeapView setup.temporarySnapshot before).topDown (valuePos key) side,
    element ≠ boundary → setup.temporarySnapshot.rank boundary < setup.temporarySnapshot.rank element
  intro element member different
  have placement := (canonicalHeapView setup.temporarySnapshot before).mem_topDown_iff.mp member
  have order := (canonicalHeapView setup.temporarySnapshot before).side_order placement.1
  rw [placement.2] at order
  have ordinary : element ≠ oldSelection.left ∧ element ≠ oldSelection.right := by
    cases side with
    | left =>
        refine ⟨different, ?_⟩
        intro equal
        have rightOrder := oldSelection.ordered.2
        rw [equal] at order
        exact Nat.lt_asymm order rightOrder
    | right =>
        refine ⟨?_, different⟩
        intro equal
        have leftOrder := oldSelection.ordered.1
        rw [equal] at order
        exact Nat.lt_asymm order leftOrder
  have boundaryRank : setup.temporarySnapshot.rank boundary = 1 := by
    cases side <;> simp [boundary, temporarySnapshot, oldSelection]
  have elementRank : setup.temporarySnapshot.rank element = 2 * snapshot.rank element := by
    change twoBoundaryTemporaryRank snapshot oldSelection.left oldSelection.right element = _
    exact twoBoundaryTemporaryRank_eq_truePriority _ _ _ _ ordinary
  have positive : 0 < setup.temporarySnapshot.rank element := by
    have strict := canonicalHeapView_heapOrdered setup.temporarySnapshot before placement.1
    change setup.temporarySnapshot.rank (valuePos key) < setup.temporarySnapshot.rank element at strict
    rw [setup.temporary_rank_zero] at strict
    exact strict
  rw [boundaryRank, elementRank]
  rw [elementRank] at positive
  omega

end Splay.Accounting.ArticleTemporaryPreparation
