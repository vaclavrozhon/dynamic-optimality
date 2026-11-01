import Splay.Accounting.WholeSplayProtectedHeapLinks
import Splay.Accounting.WholeSplayStepPairingLinks

namespace Splay.Accounting

open Splay.Lazy Splay.Lazy.Canonical Splay.Rank Splay.Tree.BST
open WholeSplayTemporarySpineGeometry WholeSplayTemporaryFocusedSpines
open WholeSplayTemporaryPriorityReduction WholeSplayTemporaryFocusedSpines.FocusedSpines

/-- A constructed focused endpoint, its spine extension, and the exact change
in protected heap links. -/
structure ProtectedPrefixResult {n lower upper : ℕ} {snapshot : Snapshot n} {key : Fin n}
    {leftBoundary rightBoundary : External n} {base : SpineBase key leftBoundary rightBoundary}
    {before : BST lower upper}
    (first : FocusedSpines snapshot key leftBoundary rightBoundary base before)
    (after : BST lower upper) (bound : upper ≤ n) (added : Finset (External n × External n))
    extends PrefixResult first after where
  protected_eq : focusedProtectedLinks focused bound = focusedProtectedLinks first bound ∪ added

theorem nonempty_after_zig_withProtectedLinks
    {n lower upper : ℕ} (comparison : BST 0 n) (key : Fin n)
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
    (step : Zig key.val before after)
    (upper_le_n : upper ≤ n) :
    Nonempty (ProtectedPrefixResult focused after upper_le_n ∅) := by
  cases step with
  | @fromLeft lower promoted demoted upper a b c =>
      cases focused with
      | atKey leftSpine rightSpine =>
          have middleBounds := b.lower_le_upper
          omega
      | leftContext innerFocused rightTree =>
          cases innerFocused with
          | atKey leftSpine rightSpine =>
              let finalRight :=
                RightSpine.grow_temporarySnapshot
                  comparison key comparisonRoot
                  leftBoundary rightBoundary ordered base
                  rightSpine c upper_le_n
              exact
                ⟨{
                  focused := .atKey leftSpine finalRight
                  protected_eq := by
                    simp only [finalRight, focusedProtectedLinks, RightSpine.grow_temporarySnapshot,
                      rightPersistentLinks, Finset.union_empty]
                    ac_rfl
                  isPrefix :=
                    ⟨.refl,
                      RightSpine.IsPrefix.of_grow_temporarySnapshot
                        comparison key comparisonRoot
                        leftBoundary rightBoundary ordered base
                        rightSpine c upper_le_n⟩
                }⟩
          | leftContext focused rightTree =>
              have bounds := key_bounds focused
              omega
          | rightContext leftTree focused =>
              have bounds := key_bounds focused
              omega
      | rightContext leftTree innerFocused =>
          have bounds := key_bounds innerFocused
          have middleBounds := b.lower_le_upper
          omega
  | @fromRight lower demoted promoted upper a b c =>
      cases focused with
      | atKey leftSpine rightSpine =>
          have middleBounds := b.lower_le_upper
          omega
      | leftContext innerFocused rightTree =>
          have bounds := key_bounds innerFocused
          have middleBounds := b.lower_le_upper
          omega
      | rightContext leftTree innerFocused =>
          cases innerFocused with
          | atKey leftSpine rightSpine =>
              have root_le_n : demoted ≤ n := by
                have aBounds := a.lower_le_upper
                have middleBounds := b.lower_le_upper
                have keyBound := key.isLt
                omega
              let finalLeft :=
                LeftSpine.grow_temporarySnapshot
                  comparison key comparisonRoot
                  leftBoundary rightBoundary ordered base
                  leftSpine a root_le_n
              exact
                ⟨{
                  focused := .atKey finalLeft rightSpine
                  protected_eq := by
                    simp only [finalLeft, focusedProtectedLinks, LeftSpine.grow_temporarySnapshot,
                      leftPersistentLinks, Finset.union_empty]
                    ac_rfl
                  isPrefix :=
                    ⟨LeftSpine.IsPrefix.of_grow_temporarySnapshot
                        comparison key comparisonRoot
                        leftBoundary rightBoundary ordered base
                        leftSpine a root_le_n,
                      .refl⟩
                }⟩
          | leftContext focused rightTree =>
              have bounds := key_bounds focused
              omega
          | rightContext leftTree focused =>
              have bounds := key_bounds focused
              omega

theorem nonempty_after_doubleRotation_withProtectedLinks
    {n lower upper : ℕ} (comparison : BST 0 n) (key : Fin n)
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
    (step : DoubleRotation key.val before after)
    (upper_le_n : upper ≤ n) :
    Nonempty (ProtectedPrefixResult focused after upper_le_n (stepPairingLinks (temporarySnapshot comparison key comparisonRoot leftBoundary rightBoundary ordered) 0 key.val before after)) := by
  cases step with
  | @zigZigLeft lower first second third upper a b c d =>
      cases focused with
      | atKey leftSpine rightSpine =>
          have bBounds := b.lower_le_upper
          have cBounds := c.lower_le_upper
          omega
      | leftContext firstFocused d =>
          cases firstFocused with
          | atKey leftSpine rightSpine =>
              have bBounds := b.lower_le_upper
              omega
          | leftContext keyFocused c =>
              cases keyFocused with
              | atKey leftSpine rightSpine =>
                  let finalRight :=
                    RightSpine.grow_temporarySnapshot
                      comparison key comparisonRoot
                      leftBoundary rightBoundary ordered base
                      rightSpine (.node c d) upper_le_n
                  exact
                    ⟨{
                      focused := .atKey leftSpine finalRight
                      protected_eq := by
                        simp only [finalRight, focusedProtectedLinks, RightSpine.grow_temporarySnapshot,
                          rightPersistentLinks, stepPairingLinks_zigZigLeft _ _ _ _ _ upper_le_n, heapLinks_node]
                        ac_rfl
                      isPrefix :=
                        ⟨.refl,
                          RightSpine.IsPrefix.of_grow_temporarySnapshot
                            comparison key comparisonRoot
                            leftBoundary rightBoundary ordered base
                            rightSpine (.node c d) upper_le_n⟩
                    }⟩
              | leftContext focused b =>
                  have bounds := key_bounds focused
                  omega
              | rightContext a focused =>
                  have bounds := key_bounds focused
                  omega
          | rightContext leftTree focused =>
              have bounds := key_bounds focused
              have bBounds := b.lower_le_upper
              omega
      | rightContext leftTree focused =>
          have bounds := key_bounds focused
          have bBounds := b.lower_le_upper
          have cBounds := c.lower_le_upper
          omega
  | @zigZigRight lower first second third upper a b c d =>
      cases focused with
      | atKey leftSpine rightSpine =>
          have bBounds := b.lower_le_upper
          have cBounds := c.lower_le_upper
          omega
      | leftContext focused rightTree =>
          have bounds := key_bounds focused
          have bBounds := b.lower_le_upper
          have cBounds := c.lower_le_upper
          omega
      | rightContext a thirdFocused =>
          cases thirdFocused with
          | atKey leftSpine rightSpine =>
              have cBounds := c.lower_le_upper
              omega
          | leftContext focused rightTree =>
              have bounds := key_bounds focused
              have cBounds := c.lower_le_upper
              omega
          | rightContext b keyFocused =>
              cases keyFocused with
              | atKey leftSpine rightSpine =>
                  have root_le_n : second ≤ n := by
                    have bBounds := b.lower_le_upper
                    have cBounds := c.lower_le_upper
                    have dBounds := d.lower_le_upper
                    have keyBound := key.isLt
                    omega
                  let finalLeft :=
                    LeftSpine.grow_temporarySnapshot
                      comparison key comparisonRoot
                      leftBoundary rightBoundary ordered base
                      leftSpine (.node a b) root_le_n
                  exact
                    ⟨{
                      focused := .atKey finalLeft rightSpine
                      protected_eq := by
                        simp only [finalLeft, focusedProtectedLinks, LeftSpine.grow_temporarySnapshot,
                          leftPersistentLinks, stepPairingLinks_zigZigRight _ _ _ _ _ upper_le_n root_le_n,
                          heapLinks_node]
                        ac_rfl
                      isPrefix :=
                        ⟨LeftSpine.IsPrefix.of_grow_temporarySnapshot
                            comparison key comparisonRoot
                            leftBoundary rightBoundary ordered base
                            leftSpine (.node a b) root_le_n,
                          .refl⟩
                    }⟩
              | leftContext focused d =>
                  have bounds := key_bounds focused
                  omega
              | rightContext leftTree focused =>
                  have bounds := key_bounds focused
                  omega
  | @zigZagLeftRight lower first second third upper a b c d =>
      cases focused with
      | atKey leftSpine rightSpine =>
          have cBounds := c.lower_le_upper
          omega
      | leftContext secondFocused d =>
          cases secondFocused with
          | atKey leftSpine rightSpine =>
              have bBounds := b.lower_le_upper
              omega
          | leftContext focused rightTree =>
              have bounds := key_bounds focused
              have bBounds := b.lower_le_upper
              omega
          | rightContext a keyFocused =>
              cases keyFocused with
              | atKey leftSpine rightSpine =>
                  have root_le_n : first ≤ n := by
                    have bBounds := b.lower_le_upper
                    have keyBound := key.isLt
                    omega
                  let finalLeft :=
                    LeftSpine.grow_temporarySnapshot
                      comparison key comparisonRoot
                      leftBoundary rightBoundary ordered base
                      leftSpine a root_le_n
                  let finalRight :=
                    RightSpine.grow_temporarySnapshot
                      comparison key comparisonRoot
                      leftBoundary rightBoundary ordered base
                      rightSpine d upper_le_n
                  exact
                    ⟨{
                      focused := .atKey finalLeft finalRight
                      protected_eq := by
                        simp only [finalLeft, finalRight, focusedProtectedLinks, RightSpine.grow_temporarySnapshot,
                          LeftSpine.grow_temporarySnapshot, rightPersistentLinks, leftPersistentLinks,
                          stepPairingLinks_zigZagLeftRight, Finset.union_empty]
                        ac_rfl
                      isPrefix :=
                        ⟨LeftSpine.IsPrefix.of_grow_temporarySnapshot
                            comparison key comparisonRoot
                            leftBoundary rightBoundary ordered base
                            leftSpine a root_le_n,
                          RightSpine.IsPrefix.of_grow_temporarySnapshot
                            comparison key comparisonRoot
                            leftBoundary rightBoundary ordered base
                            rightSpine d upper_le_n⟩
                    }⟩
              | leftContext focused rightTree =>
                  have bounds := key_bounds focused
                  omega
              | rightContext leftTree focused =>
                  have bounds := key_bounds focused
                  omega
      | rightContext leftTree focused =>
          have bounds := key_bounds focused
          have cBounds := c.lower_le_upper
          omega
  | @zigZagRightLeft lower first second third upper a b c d =>
      cases focused with
      | atKey leftSpine rightSpine =>
          have bBounds := b.lower_le_upper
          omega
      | leftContext focused rightTree =>
          have bounds := key_bounds focused
          have bBounds := b.lower_le_upper
          omega
      | rightContext a secondFocused =>
          cases secondFocused with
          | atKey leftSpine rightSpine =>
              have cBounds := c.lower_le_upper
              omega
          | leftContext keyFocused d =>
              cases keyFocused with
              | atKey leftSpine rightSpine =>
                  have root_le_n : first ≤ n := by
                    have bBounds := b.lower_le_upper
                    have keyBound := key.isLt
                    omega
                  let finalLeft :=
                    LeftSpine.grow_temporarySnapshot
                      comparison key comparisonRoot
                      leftBoundary rightBoundary ordered base
                      leftSpine a root_le_n
                  let finalRight :=
                    RightSpine.grow_temporarySnapshot
                      comparison key comparisonRoot
                      leftBoundary rightBoundary ordered base
                      rightSpine d upper_le_n
                  exact
                    ⟨{
                      focused := .atKey finalLeft finalRight
                      protected_eq := by
                        simp only [finalLeft, finalRight, focusedProtectedLinks, RightSpine.grow_temporarySnapshot,
                          LeftSpine.grow_temporarySnapshot, rightPersistentLinks, leftPersistentLinks,
                          stepPairingLinks_zigZagRightLeft, Finset.union_empty]
                        ac_rfl
                      isPrefix :=
                        ⟨LeftSpine.IsPrefix.of_grow_temporarySnapshot
                            comparison key comparisonRoot
                            leftBoundary rightBoundary ordered base
                            leftSpine a root_le_n,
                          RightSpine.IsPrefix.of_grow_temporarySnapshot
                            comparison key comparisonRoot
                            leftBoundary rightBoundary ordered base
                            rightSpine d upper_le_n⟩
                    }⟩
              | leftContext focused rightTree =>
                  have bounds := key_bounds focused
                  omega
              | rightContext leftTree focused =>
                  have bounds := key_bounds focused
                  omega
          | rightContext leftTree focused =>
              have bounds := key_bounds focused
              have cBounds := c.lower_le_upper
              omega


end Splay.Accounting
