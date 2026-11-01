import Splay.Accounting.WholeSplayTemporaryFocusedSpines
import Splay.Accounting.WholeSplayTemporaryFinalSpineAttachments

namespace Splay.Accounting.WholeSplayTemporaryFocusedTerminalAttachments

open Splay.Rank
open Splay.Tree.BST
open Splay.Accounting.LocalBendGeometry
open Splay.Accounting.WholeSplayTemporaryCoreGeometry
open Splay.Accounting.WholeSplayTemporaryCreationGeometry
open Splay.Accounting.WholeSplayTemporarySpineGeometry
open Splay.Accounting.WholeSplayTemporaryFocusedSpines
open Splay.Accounting.WholeSplayTemporaryFinalSpineAttachments

/--
A left-base attachment detected immediately after one chronological step
is the canonical slot-zero attachment of the terminal focused spines.

The only temporal premise is that the source left spine is already
nontrivial.  Its incoming edge is then unchanged by every suffix extension,
so the source delta is definitionally the terminal candidate delta.
-/
theorem leftBaseDelta_attachment_zero
    {n : ℕ} {snapshot : Snapshot n} {key : Fin n}
    {leftBoundary rightBoundary : External n}
    {base : SpineBase key leftBoundary rightBoundary}
    {sourceLower sourceUpper afterLower afterUpper : ℕ}
    {sourceTree : BST sourceLower sourceUpper}
    {sourceAfter : BST afterLower afterUpper}
    {sourceFocused :
      FocusedSpines snapshot key leftBoundary rightBoundary
        base sourceTree}
    (headResult : FocusedSpines.PrefixResult sourceFocused sourceAfter)
    {finalLeftTree : BST 0 key.val}
    {finalRightTree : BST (key.val + 1) n}
    (finalLeft :
      LeftSpine snapshot base.leftTree finalLeftTree)
    (finalRight :
      RightSpine snapshot base.rightTree finalRightTree)
    (suffix :
      FocusedSpines.IsPrefix headResult.focused
        (.atKey finalLeft finalRight))
    {globalBefore : BST 0 n}
    (identity :
      CreatedIdentity
        (before := globalBefore)
        (after := .node finalLeftTree finalRightTree) snapshot)
    (nontrivial :
      WholeSplayTemporaryFinalSpineBends.LeftSpine.incomingAtBase
        (FocusedSpines.spinePair headResult.focused).leftSpine ≠ none)
    (member :
      identity.val ∈
        (bendsFrom snapshot base.leftTree
            (FocusedSpines.spinePair
              headResult.focused).leftSpine.base_le_n
            (WholeSplayTemporaryFinalSpineBends.LeftSpine.incomingAtBase
              (FocusedSpines.spinePair
                headResult.focused).leftSpine) \
          bendsFrom snapshot base.leftTree
            (FocusedSpines.spinePair
              headResult.focused).leftSpine.base_le_n none)) :
    attachment finalLeft finalRight ⟨0, by omega⟩ =
      some identity := by
  apply attachment_zero_eq_some_of_mem_left finalLeft finalRight
  apply mem_leftCandidates_iff.mpr
  have incomingEq :=
    FocusedSpines.IsPrefix.left_incomingAtBase_eq_of_ne_none
      suffix nontrivial
  change
    WholeSplayTemporaryFinalSpineBends.LeftSpine.incomingAtBase
        finalLeft =
      WholeSplayTemporaryFinalSpineBends.LeftSpine.incomingAtBase
        (FocusedSpines.spinePair headResult.focused).leftSpine
    at incomingEq
  simpa only [incomingEq] using member

/--
The symmetric terminal transport: a right-base attachment detected after a
chronological step is the canonical slot-one attachment of the terminal
focused spines.
-/
theorem rightBaseDelta_attachment_one
    {n : ℕ} {snapshot : Snapshot n} {key : Fin n}
    {leftBoundary rightBoundary : External n}
    {base : SpineBase key leftBoundary rightBoundary}
    {sourceLower sourceUpper afterLower afterUpper : ℕ}
    {sourceTree : BST sourceLower sourceUpper}
    {sourceAfter : BST afterLower afterUpper}
    {sourceFocused :
      FocusedSpines snapshot key leftBoundary rightBoundary
        base sourceTree}
    (headResult : FocusedSpines.PrefixResult sourceFocused sourceAfter)
    {finalLeftTree : BST 0 key.val}
    {finalRightTree : BST (key.val + 1) n}
    (finalLeft :
      LeftSpine snapshot base.leftTree finalLeftTree)
    (finalRight :
      RightSpine snapshot base.rightTree finalRightTree)
    (suffix :
      FocusedSpines.IsPrefix headResult.focused
        (.atKey finalLeft finalRight))
    {globalBefore : BST 0 n}
    (identity :
      CreatedIdentity
        (before := globalBefore)
        (after := .node finalLeftTree finalRightTree) snapshot)
    (nontrivial :
      WholeSplayTemporaryFinalSpineBends.RightSpine.incomingAtBase
        (FocusedSpines.spinePair headResult.focused).rightSpine ≠ none)
    (member :
      identity.val ∈
        (bendsFrom snapshot base.rightTree
            (FocusedSpines.spinePair
              headResult.focused).rightSpine.base_le_n
            (WholeSplayTemporaryFinalSpineBends.RightSpine.incomingAtBase
              (FocusedSpines.spinePair
                headResult.focused).rightSpine) \
          bendsFrom snapshot base.rightTree
            (FocusedSpines.spinePair
              headResult.focused).rightSpine.base_le_n none)) :
    attachment finalLeft finalRight ⟨1, by omega⟩ =
      some identity := by
  apply attachment_one_eq_some_of_mem_right finalLeft finalRight
  apply mem_rightCandidates_iff.mpr
  have incomingEq :=
    FocusedSpines.IsPrefix.right_incomingAtBase_eq_of_ne_none
      suffix nontrivial
  change
    WholeSplayTemporaryFinalSpineBends.RightSpine.incomingAtBase
        finalRight =
      WholeSplayTemporaryFinalSpineBends.RightSpine.incomingAtBase
        (FocusedSpines.spinePair headResult.focused).rightSpine
    at incomingEq
  simpa only [incomingEq] using member

end Splay.Accounting.WholeSplayTemporaryFocusedTerminalAttachments
