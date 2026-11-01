import Splay.Accounting.WholeSplayTemporarySpineCreation

namespace Splay.Accounting.WholeSplayTemporaryFocusedTerminalHanging

open Splay.Rank
open Splay.Tree.BST
open Splay.Accounting.LocalBendGeometry
open Splay.Accounting.WholeSplayTemporarySpineGeometry
open Splay.Accounting.WholeSplayTemporaryFocusedSpines
open Splay.Accounting.WholeSplayTemporarySpineCreation

/--
Proof that the right component extracted from a focused state is one
specified grow.  Packaging the whole `SpinePair` makes the equality
homogeneous despite its dependent tree fields.
-/
structure RightGrowAt
    {n sourceLower sourceUpper : ℕ}
    {snapshot : Snapshot n} {key : Fin n}
    {leftBoundary rightBoundary : External n}
    {base : SpineBase key leftBoundary rightBoundary}
    {sourceTree : BST sourceLower sourceUpper}
    (focused :
      FocusedSpines snapshot key leftBoundary rightBoundary
        base sourceTree)
    {root upper : ℕ}
    {inner : BST (key.val + 1) root}
    (oldSpine : RightSpine snapshot base.rightTree inner)
    (hanging : BST (root + 1) upper)
    (bound : upper ≤ n)
    (heavy : _) : Type where
  leftLower : ℕ
  leftTree : BST leftLower key.val
  leftSpine : LeftSpine snapshot base.leftTree leftTree
  pair_eq :
    FocusedSpines.spinePair focused =
      { leftLower := leftLower
        leftTree := leftTree
        leftSpine := leftSpine
        rightUpper := upper
        rightTree := .node inner hanging
        rightSpine :=
          RightSpine.grow oldSpine hanging bound heavy }

/-- Symmetric focused-state certificate for one specified left grow. -/
structure LeftGrowAt
    {n sourceLower sourceUpper : ℕ}
    {snapshot : Snapshot n} {key : Fin n}
    {leftBoundary rightBoundary : External n}
    {base : SpineBase key leftBoundary rightBoundary}
    {sourceTree : BST sourceLower sourceUpper}
    (focused :
      FocusedSpines snapshot key leftBoundary rightBoundary
        base sourceTree)
    {lower root : ℕ}
    {inner : BST (root + 1) key.val}
    (oldSpine : LeftSpine snapshot base.leftTree inner)
    (hanging : BST lower root)
    (rootBound : root ≤ n)
    (bound : key.val ≤ n)
    (heavy : _) : Type where
  rightUpper : ℕ
  rightTree : BST (key.val + 1) rightUpper
  rightSpine : RightSpine snapshot base.rightTree rightTree
  pair_eq :
    FocusedSpines.spinePair focused =
      { leftLower := lower
        leftTree := .node hanging inner
        leftSpine :=
          LeftSpine.grow
            oldSpine hanging rootBound bound heavy
        rightUpper := rightUpper
        rightTree := rightTree
        rightSpine := rightSpine }

/--
The hanging subtree installed by a right-spine grow at one chronological
source remains in the terminal right spine.

Concrete rotation cases discharge `grown` with `pair_eq := rfl`; this lemma
performs the dependent terminal transport once and for all.
-/
theorem rightGrow_hangingBends_subset_terminal
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
    {root upper : ℕ}
    {inner : BST (key.val + 1) root}
    (oldSpine :
      RightSpine snapshot base.rightTree inner)
    (hanging : BST (root + 1) upper)
    (bound : upper ≤ n)
    (heavy : _)
    (grown :
      RightGrowAt headResult.focused
        oldSpine hanging bound heavy) :
    bendsFrom snapshot hanging bound none ⊆
      finalRight.hangingBends := by
  obtain ⟨leftLower, leftTree, leftSpine, pairEq⟩ := grown
  have extension := suffix.right
  rw [pairEq] at extension
  exact
    rightGrow_hangingBends_subset_of_prefix
      oldSpine hanging bound heavy rfl extension

/--
Mirror terminal transport for the hanging subtree installed by a left-spine
grow.
-/
theorem leftGrow_hangingBends_subset_terminal
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
    {lower root : ℕ}
    {inner : BST (root + 1) key.val}
    (oldSpine :
      LeftSpine snapshot base.leftTree inner)
    (hanging : BST lower root)
    (rootBound : root ≤ n)
    (bound : key.val ≤ n)
    (heavy : _)
    (grown :
      LeftGrowAt headResult.focused
        oldSpine hanging rootBound bound heavy) :
    bendsFrom snapshot hanging rootBound none ⊆
      finalLeft.hangingBends := by
  obtain ⟨rightUpper, rightTree, rightSpine, pairEq⟩ := grown
  have extension := suffix.left
  rw [pairEq] at extension
  exact
    leftGrow_hangingBends_subset_of_prefix
      oldSpine hanging rootBound bound heavy rfl extension

end Splay.Accounting.WholeSplayTemporaryFocusedTerminalHanging
