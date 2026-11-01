import Splay.Accounting.ArticlePairingStageHeapLinks
import Splay.Accounting.ArticlePairingStageBoundaryGeometry
import Splay.Accounting.WholeSplayUnpairedParent
import Splay.Lazy.TwoSideTransferParents

namespace Splay.Accounting

open Splay.Lazy Splay.Lazy.Canonical Splay.Rank Splay.Tree.BST
open WholeSplayTemporaryPriorityReduction WholeSplayTemporaryCoreGeometry WholeSplayTemporaryCoreClassification

/-- The parent map after the two actual whole-side transfers is exactly the
canonical parent map of the final splay tree under temporary priorities. -/
theorem ArticlePairingStage.transferBothSides_parent_eq_canonical {n : ℕ} {params : Interface.Parameters}
    (comparison : BST 0 n) (key : Fin n) (comparisonRoot : comparison.HasRoot key.val)
    (leftBoundary rightBoundary : External n)
    (ordered : leftBoundary < valuePos key ∧ valuePos key < rightBoundary)
    {before after : BST 0 n} {initial : Lazy.State n} {kinds : List SplayStepKind}
    (stage : ArticlePairingStage params
      (temporarySnapshot comparison key comparisonRoot leftBoundary rightBoundary ordered) before key kinds initial)
    {execution : SplayExecution key.val before after} {zig zigZig zigZag : ℕ}
    (transcript : SplayExecutionTranscript key.val execution kinds zig zigZig zigZag)
    (placement : BoundaryPlacementAt key leftBoundary rightBoundary before)
    (leftGeometry : SideTransferGeometry stage.final.view (valuePos key) leftBoundary .left)
    (rightGeometry : SideTransferGeometry stage.final.view (valuePos key) rightBoundary .right) :
    (stage.final.transferBothSides leftGeometry rightGeometry stage.stable.2.2.1).view.parent =
      canonicalParent (temporarySnapshot comparison key comparisonRoot leftBoundary rightBoundary ordered) after := by
  classical
  let snapshot := temporarySnapshot comparison key comparisonRoot leftBoundary rightBoundary ordered
  obtain ⟨reparented, viewEq⟩ := stage.exists_reparented
  have oldRoot : stage.preparation.final.view.root = valuePos key := by
    rw [stage.preparation.represents.view_eq]
    exact canonicalRoot_eq_of_rank_eq_zero snapshot before stage.rankZero
  have rootLink := transcript.final_root_heapLink_iff comparison key comparisonRoot leftBoundary rightBoundary ordered placement
  have boundaryParent : ∀ element, element = leftBoundary ∨ element = rightBoundary →
      canonicalParent snapshot after element = some (valuePos key) := by
    intro element boundary
    exact (mem_heapLinks_iff_parent snapshot after _ _).mp ((rootLink element).mpr boundary)
  funext element
  rw [State.transferBothSides_parent]
  by_cases paired : ∃ pairing ∈ stage.matching, element = pairing.loser
  · obtain ⟨pairing, member, equal⟩ := paired
    subst element
    have pairedParent : stage.final.view.parent pairing.loser = some pairing.winner := by
      rw [← viewEq]
      exact reparented.paired_parent pairing member
    have winnerNeRoot : pairing.winner ≠ valuePos key := by
      have winnerParent := (stage.matching_parents member).1
      rw [oldRoot] at winnerParent
      intro equal
      rw [equal, ← oldRoot, stage.preparation.final.view.root_parent] at winnerParent
      contradiction
    have notMoved : ∀ side boundary (geometry : SideTransferGeometry stage.final.view (valuePos key) boundary side),
        pairing.loser ∉ geometry.moved := by
      intro side boundary geometry moved
      have rootParent := (geometry.moved_parent_side moved).1
      exact winnerNeRoot (Option.some.inj (pairedParent.symm.trans rootParent))
    rw [if_neg (notMoved _ _ rightGeometry), if_neg (notMoved _ _ leftGeometry), pairedParent]
    exact (stage.pairing_final_canonicalParent comparison key comparisonRoot leftBoundary rightBoundary ordered
      transcript placement member).symm
  · have unpaired : ∀ pairing ∈ stage.matching, element ≠ pairing.loser := by
      intro pairing member equal
      exact paired ⟨pairing, member, equal⟩
    have oldParent : stage.final.view.parent element = canonicalParent snapshot before element := by
      rw [← viewEq, reparented.unpaired_parent element unpaired, stage.preparation.represents.view_eq]
      rfl
    have noLink : ∀ owner, (owner, element) ∉ transcriptPairingLinks snapshot transcript := by
      intro owner member
      rw [← stage.matchingHeapLinks_eq_transcript transcript] at member
      obtain ⟨pairing, member, equal⟩ := List.mem_map.mp (List.mem_toFinset.mp member)
      exact unpaired pairing member (congrArg Prod.snd equal).symm
    by_cases rootParent : canonicalParent snapshot before element = some (valuePos key)
    · have currentRootParent : stage.final.view.parent element = some (valuePos key) := oldParent.trans rootParent
      by_cases atLeft : element = leftBoundary
      · subst element
        have notRightMoved : leftBoundary ∉ rightGeometry.moved := by
          intro moved
          have sideEq := (rightGeometry.moved_parent_side moved).2
          rw [leftGeometry.boundary_parent_side.2] at sideEq
          contradiction
        rw [if_neg notRightMoved, if_neg leftGeometry.boundary_not_moved, currentRootParent,
          boundaryParent leftBoundary (Or.inl rfl)]
      · by_cases atRight : element = rightBoundary
        · subst element
          have notLeftMoved : rightBoundary ∉ leftGeometry.moved := by
            intro moved
            have sideEq := (leftGeometry.moved_parent_side moved).2
            rw [rightGeometry.boundary_parent_side.2] at sideEq
            contradiction
          rw [if_neg rightGeometry.boundary_not_moved, if_neg notLeftMoved, currentRootParent,
            boundaryParent rightBoundary (Or.inr rfl)]
        · have canonical := transcript.final_unpaired_parent comparison key comparisonRoot leftBoundary rightBoundary
            ordered placement element rootParent atLeft atRight noLink
          have sideOrder := stage.final.view.side_order currentRootParent
          cases sideEq : stage.final.view.side element with
          | left =>
              have leftMoved := (leftGeometry.mem_moved_iff element).mpr ⟨currentRootParent, sideEq, atLeft⟩
              have notRightMoved : element ∉ rightGeometry.moved := by
                intro moved
                have wrong := (rightGeometry.moved_parent_side moved).2
                rw [sideEq] at wrong
                contradiction
              have beforeKey : element < valuePos key := by simpa only [Fin.lt_def, sideEq] using sideOrder
              rw [if_neg notRightMoved, if_pos leftMoved, canonical, if_pos beforeKey]
          | right =>
              have rightMoved := (rightGeometry.mem_moved_iff element).mpr ⟨currentRootParent, sideEq, atRight⟩
              have notBeforeKey : ¬ element < valuePos key := by
                have greater : valuePos key < element := by simpa only [Fin.lt_def, sideEq] using sideOrder
                exact not_lt_of_gt greater
              rw [if_pos rightMoved, canonical, if_neg notBeforeKey]
    · have notMoved : ∀ side boundary (geometry : SideTransferGeometry stage.final.view (valuePos key) boundary side),
          element ∉ geometry.moved := by
        intro side boundary geometry moved
        exact rootParent (oldParent.symm.trans (geometry.moved_parent_side moved).1)
      rw [if_neg (notMoved _ _ rightGeometry), if_neg (notMoved _ _ leftGeometry), oldParent]
      cases parent : canonicalParent snapshot before element with
      | none =>
          have atRoot := (canonicalParent_eq_none_iff snapshot before element).mp parent
          rw [canonicalRoot_eq_of_rank_eq_zero snapshot before stage.rankZero] at atRoot
          have finalRoot := canonicalRoot_eq_of_rank_eq_zero snapshot after stage.rankZero
          rw [atRoot, ← finalRoot, canonicalParent_canonicalRoot]
      | some owner =>
          have otherOwner : owner ≠ valuePos key := by intro equal; exact rootParent (parent.trans (congrArg some equal))
          have originalLink := (mem_heapLinks_iff_parent snapshot before owner element).mpr parent
          have preserved := (transcript.final_heapLinks comparison key comparisonRoot leftBoundary rightBoundary ordered placement).1
            (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨originalLink, otherOwner⟩))
          exact ((mem_heapLinks_iff_parent snapshot after owner element).mp preserved).symm

end Splay.Accounting
