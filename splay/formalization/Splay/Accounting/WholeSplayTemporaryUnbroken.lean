import Splay.Accounting.WholeSplayRootSourceUnbroken
import Splay.Accounting.CanonicalOffpathSubtree

namespace Splay.Accounting

open Splay.Rank Splay.Tree Splay.Tree.BST Splay.Lazy Splay.Lazy.Canonical
open WholeSplayTemporarySpineGeometry WholeSplayTemporaryFocusedSpines
open WholeSplayTemporaryPriorityReduction WholeSplayTemporaryCoreGeometry

/-- Under the actual temporary priorities, a block surviving from the
accessed owner and transferred to its selected boundary becomes unbroken
at the splay endpoint, including on its very first splay. -/
theorem temporary_transferred_block_unbroken {n : ℕ} (comparison : BST 0 n) (key : Fin n)
    (comparisonRoot : comparison.HasRoot key.val) (leftBoundary rightBoundary : External n)
    {before after : BST 0 n}
    (placement : BoundaryPlacementAt key leftBoundary rightBoundary before)
    (execution : SplayExecution key.val before after)
    (block : Block n)
    (oldParents : ∀ element ∈ block.elements,
      canonicalParent (temporarySnapshot comparison key comparisonRoot leftBoundary rightBoundary placement.ordered)
        before element = some (valuePos key))
    (parents : ∀ element ∈ block.elements,
      canonicalParent (temporarySnapshot comparison key comparisonRoot leftBoundary rightBoundary placement.ordered)
        after element = some block.owner)
    (sides : ∀ element ∈ block.elements,
      canonicalSide (temporarySnapshot comparison key comparisonRoot leftBoundary rightBoundary placement.ordered)
        after element = block.side)
    (owner : block.owner = match block.side with | .left => leftBoundary | .right => rightBoundary) :
    canonicalBlockCrossSideUnbroken
      (temporarySnapshot comparison key comparisonRoot leftBoundary rightBoundary placement.ordered) after block := by
  let snapshot := temporarySnapshot comparison key comparisonRoot leftBoundary rightBoundary placement.ordered
  obtain ⟨spines⟩ := FocusedSpines.nonempty_executionTwoSpines_ofBoundaryPlacement comparison key comparisonRoot
    leftBoundary rightBoundary placement execution
  have rankZero : snapshot.rank (valuePos key) = 0 := temporarySnapshot_rank_valuePos comparison key comparisonRoot
    leftBoundary rightBoundary placement.ordered
  have leftOwner : subtreeOwner snapshot spines.base.leftTree (Nat.le_of_lt key.isLt) = leftBoundary := by
    symm
    apply snapshot.intervalMin_unique
    apply left_isIntervalMin comparison key comparisonRoot leftBoundary rightBoundary _ _ placement.ordered
    · exact ⟨spines.base.left_lower_mem, spines.base.left_upper_mem⟩
    · change 2 * key.val < 2 * key.val + 1
      omega
  have rightOwner : subtreeOwner snapshot spines.base.rightTree spines.baseFocus.rightUpper_le_upper = rightBoundary := by
    symm
    apply snapshot.intervalMin_unique
    apply right_isIntervalMin comparison key comparisonRoot leftBoundary rightBoundary _ _ placement.ordered
    · exact ⟨spines.base.right_lower_mem, spines.base.right_upper_mem⟩
    · change 2 * key.val + 1 < 2 * (key.val + 1)
      omega
  cases side : block.side with
  | left =>
    apply Splay.Accounting.ExecutionTwoSpines.left_transferred_unbroken spines rankZero block
      (by rw [leftOwner]; simpa only [side] using owner) side oldParents parents sides
  | right =>
    apply Splay.Accounting.ExecutionTwoSpines.right_transferred_unbroken spines rankZero block
      (by rw [rightOwner]; simpa only [side] using owner) side oldParents parents sides

end Splay.Accounting
