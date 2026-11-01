import Splay.Accounting.ArticleTemporaryCanonicalEndpoint
import Splay.Accounting.ArticleTemporaryUnbroken
import Splay.Accounting.ArticlePairingBlockOrigins
import Splay.Accounting.WholeSplayTemporaryUnbroken
import Splay.Lazy.TwoSideTransferOrigins
import Splay.Lazy.GrowingPassCountZero

namespace Splay.Accounting

open Splay.Lazy Splay.Lazy.Canonical Splay.Rank Splay.Tree.BST
open WholeSplayTemporaryCoreGeometry WholeSplayTemporaryCoreClassification

namespace ArticleTemporaryTransferStage

variable {n : ℕ} {params : Interface.Parameters} {comparison : BST 0 n}
  {before : BST 0 n} {key : Fin n} {kinds : List SplayStepKind} {initial : Lazy.State n}
  (stage : ArticleTemporaryTransferStage params (Snapshot.ofTree comparison) before key kinds initial)

/-- An interval left at the accessed root is contained in its single
terminal child on that side, so it is unbroken automatically. -/
theorem root_block_unbroken (after : BST 0 n) {block : Block n}
    (member : block ∈ stage.final.blocks) (owner : block.owner = valuePos key) :
    canonicalBlockCrossSideUnbroken stage.setup.temporarySnapshot after block := by
  let selection := WholeSplayTemporaryBoundaryGeometry.KeyFocus.boundaryMinimumSelection stage.setup.temporarySnapshot before key
  let boundary := match block.side with | .left => selection.left | .right => selection.right
  let singleton := { block with elements := [boundary] }
  apply canonicalBlockCrossSideUnbroken_mono (after := block)
    (canonicalBlockCrossSideUnbroken_of_elements_singleton stage.setup.temporarySnapshot after singleton boundary rfl) rfl rfl
  intro element inside
  have attached := (stage.stable.valid.2 block member).isSegment.mem inside
  have top := (stage.final.view.mem_attachedTopDown_iff.mp attached).1
  rw [owner] at top
  cases side : block.side with
  | left =>
    rw [side, stage.source_topDown.1] at top
    simpa [singleton, boundary, selection, side] using top
  | right =>
    rw [side, stage.source_topDown.2] at top
    simpa [singleton, boundary, selection, side] using top

/-- The complete actual request prefix preserves the passed-block invariant.
For old non-root owners this uses literal off-path subtree persistence; for
the accessed owner's surviving sources it uses the first-splay spine proof. -/
theorem preservesUnbroken (comparisonRoot : comparison.HasRoot key.val)
    {after : BST 0 n} {execution : SplayExecution key.val before after} {zig zigZig zigZag : ℕ}
    (transcript : SplayExecutionTranscript key.val execution kinds zig zigZig zigZag)
    (zero : Interface.GrowingPassCountZero initial.toInterface)
    (unbroken : PassedBlocksUnbroken (Snapshot.ofTree comparison).withTruePriority before initial) :
    PassedBlocksUnbroken stage.setup.temporarySnapshot after (stage.canonicalFinal after) := by
  have preparedUnbroken := stage.pairing.preparation.preservesUnbroken (stage.setup.preservesUnbroken unbroken)
  have finalZero := stage.trace.growingPassCountZero zero
  have represented := stage.canonical_represents comparisonRoot transcript
  intro block member positive
  obtain ⟨id, found⟩ := List.mem_iff_getElem?.mp member
  have shrinking := State.shrinking_of_passCount_ne_zero finalZero found positive
  obtain ⟨current, currentFound, elements, side, mode, count, _, placement⟩ :=
    stage.pairing.final.transferBothSides_block_origin stage.leftGeometry stage.rightGeometry stage.pairing.stable.2.2.1 found
  obtain ⟨old, oldFound, oldShrinking, oldOwner, oldSide, _, sublist, _, counterFrame⟩ :=
    stage.pairing.shrinkingRefines id current currentFound (mode ▸ shrinking)
  have oldStructural := stage.pairing.preparation.represents.valid.2 old (List.mem_of_getElem? oldFound)
  have finalStructural := represented.valid.2 block member
  have oldParents : ∀ element ∈ block.elements,
      canonicalParent stage.setup.temporarySnapshot before element = some old.owner := by
    intro element inside
    have parent := oldStructural.parent_eq (sublist.mem (elements ▸ inside))
    rw [stage.pairing.preparation.represents.view_eq] at parent
    exact parent
  have parents : ∀ element ∈ block.elements,
      canonicalParent stage.setup.temporarySnapshot after element = some block.owner := by
    intro element inside
    exact finalStructural.parent_eq inside
  have sides : ∀ element ∈ block.elements,
      canonicalSide stage.setup.temporarySnapshot after element = block.side := by
    intro element inside
    exact finalStructural.side_eq inside
  by_cases accessed : old.owner = valuePos key
  · rcases placement with sameOwner | ⟨currentOwner, transferredOwner⟩
    · exact stage.root_block_unbroken after member (sameOwner.trans (oldOwner.trans accessed))
    · let selection := WholeSplayTemporaryBoundaryGeometry.KeyFocus.boundaryMinimumSelection stage.setup.temporarySnapshot before key
      have snapshotEq := stage.setup.temporarySnapshot_eq_comparison comparison key comparisonRoot
      have geometry := temporary_transferred_block_unbroken comparison key comparisonRoot selection.left selection.right
        (canonicalBoundaryPlacement stage.setup.temporarySnapshot before key) execution block
      rw [snapshotEq]
      apply geometry
      · intro element inside
        rw [← snapshotEq]
        exact (oldParents element inside).trans (congrArg some accessed)
      · intro element inside
        rw [← snapshotEq]
        exact parents element inside
      · intro element inside
        rw [← snapshotEq]
        exact sides element inside
      · exact transferredOwner
  · have ownerEq : block.owner = old.owner := by
      rcases placement with sameOwner | ⟨currentOwner, _⟩
      · exact sameOwner.trans oldOwner
      · exact (accessed (oldOwner.symm.trans currentOwner)).elim
    have oldPositive : old.passCount ≠ 0 := by
      rcases counterFrame with equal | active
      · rw [← equal, ← count]
        exact positive
      · exact (accessed active).elim
    have smaller := canonicalBlockCrossSideUnbroken_mono
      (preparedUnbroken old (List.mem_of_getElem? oldFound) oldPositive) ownerEq (side.trans oldSide)
      (fun _ inside => sublist.mem (elements ▸ inside))
    apply canonicalBlockCrossSideUnbroken_after_splay_of_owner_ne stage.setup.temporarySnapshot key execution
      stage.setup.temporary_rank_zero block (by rw [ownerEq]; exact accessed) _ smaller
    intro element inside
    rw [ownerEq]
    exact oldParents element inside

end ArticleTemporaryTransferStage
end Splay.Accounting
