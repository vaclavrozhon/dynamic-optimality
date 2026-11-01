import Splay.Accounting.WholeSplayRootProtectedTransition

namespace Splay.Accounting

open Splay.Lazy Splay.Lazy.Canonical Splay.Rank Splay.Tree.BST
open WholeSplayTemporarySpineGeometry WholeSplayTemporaryFocusedSpines
open WholeSplayTemporaryPriorityReduction WholeSplayTemporaryFocusedSpines.FocusedSpines

private theorem nonempty_after_doubleRotationAt_withProtectedLinks_of_eq
    {n lower upper depth keyValue : ℕ}
    (comparison : BST 0 n) (key : Fin n)
    (comparisonRoot : comparison.HasRoot key.val)
    (leftBoundary rightBoundary : External n)
    (ordered :
      leftBoundary < valuePos key ∧ valuePos key < rightBoundary)
    (base : SpineBase key leftBoundary rightBoundary)
    {before after : BST lower upper}
    (focused :
      FocusedSpines
        (temporarySnapshot comparison key comparisonRoot
          leftBoundary rightBoundary ordered)
        key leftBoundary rightBoundary base before)
    (step : DoubleRotationAt depth keyValue before after)
    (key_eq : key.val = keyValue)
    (upper_le_n : upper ≤ n) :
    Nonempty (ProtectedPrefixResult focused after upper_le_n
      (stepPairingLinks (temporarySnapshot comparison key comparisonRoot leftBoundary rightBoundary ordered) depth key.val before after)) := by
  induction step generalizing key with
  | root rootStep =>
      rw [← key_eq] at rootStep
      exact
        nonempty_after_doubleRotation_withProtectedLinks
          comparison key comparisonRoot
          leftBoundary rightBoundary ordered base focused rootStep upper_le_n
  | @leftContext depth keyValue childLower pivot childUpper
      before after innerStep rightTree ih =>
      cases focused with
      | atKey leftSpine rightSpine =>
          have stepBounds := innerStep.key_bounds
          omega
      | leftContext innerFocused contextRight =>
          have pivot_le_n : pivot ≤ n := by
            have rightBounds := rightTree.lower_le_upper
            omega
          obtain ⟨result⟩ :=
            ih key comparisonRoot ordered base innerFocused
              key_eq pivot_le_n
          exact
            ⟨{
              focused := .leftContext result.focused rightTree
              protected_eq := by
                simp only [focusedProtectedLinks, stepPairingLinks_leftContext _ before after rightTree innerFocused.key_bounds.2]
                rw [result.protected_eq]
                ac_rfl
              isPrefix :=
                ⟨result.isPrefix.left, result.isPrefix.right⟩
            }⟩
      | rightContext contextLeft innerFocused =>
          have focusedBounds := key_bounds innerFocused
          have stepBounds := innerStep.key_bounds
          omega
  | @rightContext depth keyValue childLower pivot childUpper
      leftTree before after innerStep ih =>
      cases focused with
      | atKey leftSpine rightSpine =>
          have stepBounds := innerStep.key_bounds
          omega
      | leftContext innerFocused contextRight =>
          have focusedBounds := key_bounds innerFocused
          have stepBounds := innerStep.key_bounds
          omega
      | rightContext contextLeft innerFocused =>
          obtain ⟨result⟩ :=
            ih key comparisonRoot ordered base innerFocused
              key_eq upper_le_n
          exact
            ⟨{
              focused := .rightContext leftTree result.focused
              protected_eq := by
                simp only [focusedProtectedLinks, stepPairingLinks_rightContext (key := key.val) _ leftTree before after (by have := innerFocused.key_bounds; omega)]
                rw [result.protected_eq]
                ac_rfl
              isPrefix :=
                ⟨result.isPrefix.left, result.isPrefix.right⟩
            }⟩

/--
Public specialization of contextual preservation to the accessed finite key.
-/
theorem nonempty_after_doubleRotationAt_withProtectedLinks
    {n lower upper depth : ℕ} (comparison : BST 0 n) (key : Fin n)
    (comparisonRoot : comparison.HasRoot key.val)
    (leftBoundary rightBoundary : External n)
    (ordered :
      leftBoundary < valuePos key ∧ valuePos key < rightBoundary)
    (base : SpineBase key leftBoundary rightBoundary)
    {before after : BST lower upper}
    (focused :
      FocusedSpines
        (temporarySnapshot comparison key comparisonRoot
          leftBoundary rightBoundary ordered)
        key leftBoundary rightBoundary base before)
    (step : DoubleRotationAt depth key.val before after)
    (upper_le_n : upper ≤ n) :
    Nonempty (ProtectedPrefixResult focused after upper_le_n
      (stepPairingLinks (temporarySnapshot comparison key comparisonRoot leftBoundary rightBoundary ordered) depth key.val before after)) :=
  nonempty_after_doubleRotationAt_withProtectedLinks_of_eq
    comparison key comparisonRoot leftBoundary rightBoundary
    ordered base focused step rfl upper_le_n

end Splay.Accounting
