import Splay.Accounting.ArticleTransferCanonicalParents

namespace Splay.Accounting

open Splay.Lazy Splay.Lazy.Canonical Splay.Rank Splay.Tree.BST
open WholeSplayTemporaryPriorityReduction WholeSplayTemporaryCoreGeometry WholeSplayTemporaryCoreClassification

/-- Rank, root, parent and side data of the actual transfer endpoint agree
with the final canonical heap. Its independent level witness may differ. -/
theorem ArticlePairingStage.transferBothSides_canonical_agreement {n : ℕ} {params : Interface.Parameters}
    (comparison : BST 0 n) (key : Fin n) (comparisonRoot : comparison.HasRoot key.val)
    (leftBoundary rightBoundary : External n)
    (ordered : leftBoundary < valuePos key ∧ valuePos key < rightBoundary)
    {snapshot : Snapshot n}
    (snapshotEq : snapshot = temporarySnapshot comparison key comparisonRoot leftBoundary rightBoundary ordered)
    {before after : BST 0 n} {initial : Lazy.State n} {kinds : List SplayStepKind}
    (stage : ArticlePairingStage params snapshot before key kinds initial)
    {execution : SplayExecution key.val before after} {zig zigZig zigZag : ℕ}
    (transcript : SplayExecutionTranscript key.val execution kinds zig zigZig zigZag)
    (placement : BoundaryPlacementAt key leftBoundary rightBoundary before)
    (leftGeometry : SideTransferGeometry stage.final.view (valuePos key) leftBoundary .left)
    (rightGeometry : SideTransferGeometry stage.final.view (valuePos key) rightBoundary .right) :
    let final := stage.final.transferBothSides leftGeometry rightGeometry stage.stable.2.2.1
    let canonical := canonicalHeapView snapshot after
    final.view.rank = canonical.rank ∧ final.view.root = canonical.root ∧
      final.view.parent = canonical.parent ∧ final.view.side = canonical.side := by
  subst snapshot
  dsimp only
  let snapshot := temporarySnapshot comparison key comparisonRoot leftBoundary rightBoundary ordered
  let final := stage.final.transferBothSides leftGeometry rightGeometry stage.stable.2.2.1
  let canonical := canonicalHeapView snapshot after
  have parents : final.view.parent = canonical.parent := stage.transferBothSides_parent_eq_canonical comparison key
    comparisonRoot leftBoundary rightBoundary ordered transcript placement leftGeometry rightGeometry
  obtain ⟨reparented, viewEq⟩ := stage.exists_reparented
  have originalRoot : stage.preparation.final.view.root = valuePos key := by
    rw [stage.preparation.represents.view_eq]
    exact canonicalRoot_eq_of_rank_eq_zero snapshot before stage.rankZero
  have currentRoot : stage.final.view.root = valuePos key := by
    rw [← viewEq, reparented.root_eq, originalRoot]
  have rootUnpaired : ∀ pairing ∈ stage.matching, valuePos key ≠ pairing.loser := by
    intro pairing member equal
    have parent := (stage.matching_parents member).2
    rw [← equal, ← originalRoot, stage.preparation.final.view.root_parent] at parent
    contradiction
  have rootSide : stage.final.view.side stage.final.view.root = .left := by
    rw [currentRoot, ← viewEq, reparented.unpaired_side (valuePos key) rootUnpaired,
      stage.preparation.represents.view_eq]
    change canonicalSide snapshot before (valuePos key) = .left
    rw [← canonicalRoot_eq_of_rank_eq_zero snapshot before stage.rankZero]
    simp [canonicalSide]
  refine ⟨?_, final.view.root_eq_of_parent_eq canonical parents, parents, ?_⟩
  · change final.view.rank = snapshot.rank
    rw [State.transferBothSides_rank, ← viewEq, reparented.rank_eq, stage.preparation.represents.view_eq]
    rfl
  · apply final.view.side_eq_of_parent_eq canonical parents
    change final.view.side final.view.root = canonicalSide snapshot after (canonicalRoot snapshot after)
    rw [State.transferBothSides_root, State.transferBothSides_root_side, rootSide]
    simp [canonicalSide]

end Splay.Accounting
