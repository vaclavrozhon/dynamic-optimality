import Splay.Accounting.WholeSplayTemporaryFocusedSpines

namespace Splay.Accounting.WholeSplayTemporaryFocusedStepNontriviality

open Splay.Rank
open Splay.Tree.BST
open Splay.Lazy.Canonical
open Splay.Accounting.WholeSplayTemporarySpineGeometry
open Splay.Accounting.WholeSplayTemporaryFocusedSpines

/-!
Structural post-step facts for the focused-spine chronology.

The statements in this module do not depend on the creation-persistence
development.  They record only which terminal spine has necessarily become
nontrivial after each exact splay-step orientation.
-/

/--
The four exact root shapes hidden by the Boolean index of
`DoubleOrientationAt`.
-/
inductive DoubleStepShape
  | zigZigLeft
  | zigZigRight
  | zigZagLeftRight
  | zigZagRightLeft

set_option linter.unusedVariables false in
/--
An exact double-rotation orientation propagated through an arbitrary
unchanged context.

`DoubleOrientationAt` deliberately remembers only whether a step is
zig-zig or zig-zag in its Boolean index.  This refinement also remembers
which of the two mirror root shapes occurred.
-/
inductive ExactDoubleOrientationAt :
    DoubleStepShape → {depth key lower upper : ℕ} →
      BST lower upper → BST lower upper → Prop
  | zigZigLeft
      {lower first second third upper : ℕ}
      (a : BST lower first)
      (b : BST (first + 1) second)
      (c : BST (second + 1) third)
      (d : BST (third + 1) upper) :
      ExactDoubleOrientationAt .zigZigLeft
        (depth := 0) (key := first)
        (.node (.node (.node a b) c) d)
        (.node a (.node b (.node c d)))
  | zigZigRight
      {lower first second third upper : ℕ}
      (a : BST lower first)
      (b : BST (first + 1) second)
      (c : BST (second + 1) third)
      (d : BST (third + 1) upper) :
      ExactDoubleOrientationAt .zigZigRight
        (depth := 0) (key := third)
        (.node a (.node b (.node c d)))
        (.node (.node (.node a b) c) d)
  | zigZagLeftRight
      {lower first second third upper : ℕ}
      (a : BST lower first)
      (b : BST (first + 1) second)
      (c : BST (second + 1) third)
      (d : BST (third + 1) upper) :
      ExactDoubleOrientationAt .zigZagLeftRight
        (depth := 0) (key := second)
        (.node (.node a (.node b c)) d)
        (.node (.node a b) (.node c d))
  | zigZagRightLeft
      {lower first second third upper : ℕ}
      (a : BST lower first)
      (b : BST (first + 1) second)
      (c : BST (second + 1) third)
      (d : BST (third + 1) upper) :
      ExactDoubleOrientationAt .zigZagRightLeft
        (depth := 0) (key := second)
        (.node a (.node (.node b c) d))
        (.node (.node a b) (.node c d))
  | leftContext
      {shape : DoubleStepShape}
      {depth key lower root upper : ℕ}
      {before after : BST lower root}
      (orientation :
        ExactDoubleOrientationAt shape
          (depth := depth) (key := key) before after)
      (right : BST (root + 1) upper) :
      ExactDoubleOrientationAt shape
        (depth := depth.succ) (key := key)
        (.node before right) (.node after right)
  | rightContext
      {shape : DoubleStepShape}
      {depth key lower root upper : ℕ}
      (left : BST lower root)
      {before after : BST (root + 1) upper}
      (orientation :
        ExactDoubleOrientationAt shape
          (depth := depth) (key := key) before after) :
      ExactDoubleOrientationAt shape
        (depth := depth.succ) (key := key)
        (.node left before) (.node left after)

namespace ExactDoubleOrientationAt

/-- The promoted key lies in the indexed interval of every exact shape. -/
theorem key_bounds
    {shape : DoubleStepShape}
    {depth key lower upper : ℕ}
    {before after : BST lower upper}
    (orientation :
      ExactDoubleOrientationAt shape
        (depth := depth) (key := key) before after) :
    lower ≤ key ∧ key < upper := by
  induction orientation with
  | zigZigLeft a b c d =>
      have aBounds := a.lower_le_upper
      have bBounds := b.lower_le_upper
      have cBounds := c.lower_le_upper
      have dBounds := d.lower_le_upper
      omega
  | zigZigRight a b c d =>
      have aBounds := a.lower_le_upper
      have bBounds := b.lower_le_upper
      have cBounds := c.lower_le_upper
      have dBounds := d.lower_le_upper
      omega
  | zigZagLeftRight a b c d =>
      have aBounds := a.lower_le_upper
      have bBounds := b.lower_le_upper
      have cBounds := c.lower_le_upper
      have dBounds := d.lower_le_upper
      omega
  | zigZagRightLeft a b c d =>
      have aBounds := a.lower_le_upper
      have bBounds := b.lower_le_upper
      have cBounds := c.lower_le_upper
      have dBounds := d.lower_le_upper
      omega
  | leftContext orientation right ih =>
      have rightBounds := right.lower_le_upper
      omega
  | rightContext left orientation ih =>
      have leftBounds := left.lower_le_upper
      omega

/--
Refine the Boolean zig-zig orientation into its exact left-left or
right-right contextual shape.
-/
theorem zigZig_cases_of_doubleOrientationAt
    {depth key lower upper : ℕ}
    {before after : BST lower upper}
    (orientation :
      DoubleOrientationAt true
        (depth := depth) (key := key) before after) :
    ExactDoubleOrientationAt .zigZigLeft
          (depth := depth) (key := key) before after ∨
      ExactDoubleOrientationAt .zigZigRight
          (depth := depth) (key := key) before after := by
  cases orientation with
  | zigZigLeft a b c d =>
      exact Or.inl (.zigZigLeft a b c d)
  | zigZigRight a b c d =>
      exact Or.inr (.zigZigRight a b c d)
  | leftContext innerOrientation right =>
      rcases
          zigZig_cases_of_doubleOrientationAt innerOrientation with
        exactLeft | exactRight
      · exact Or.inl (.leftContext exactLeft right)
      · exact Or.inr (.leftContext exactRight right)
  | rightContext left innerOrientation =>
      rcases
          zigZig_cases_of_doubleOrientationAt innerOrientation with
        exactLeft | exactRight
      · exact Or.inl (.rightContext left exactLeft)
      · exact Or.inr (.rightContext left exactRight)
termination_by depth

/--
Refine the Boolean zig-zag orientation into its exact left-right or
right-left contextual shape.
-/
theorem zigZag_cases_of_doubleOrientationAt
    {depth key lower upper : ℕ}
    {before after : BST lower upper}
    (orientation :
      DoubleOrientationAt false
        (depth := depth) (key := key) before after) :
    ExactDoubleOrientationAt .zigZagLeftRight
          (depth := depth) (key := key) before after ∨
      ExactDoubleOrientationAt .zigZagRightLeft
          (depth := depth) (key := key) before after := by
  cases orientation with
  | zigZagLeftRight a b c d =>
      exact Or.inl (.zigZagLeftRight a b c d)
  | zigZagRightLeft a b c d =>
      exact Or.inr (.zigZagRightLeft a b c d)
  | leftContext innerOrientation right =>
      rcases
          zigZag_cases_of_doubleOrientationAt innerOrientation with
        exactLeftRight | exactRightLeft
      · exact Or.inl (.leftContext exactLeftRight right)
      · exact Or.inr (.leftContext exactRightLeft right)
  | rightContext left innerOrientation =>
      rcases
          zigZag_cases_of_doubleOrientationAt innerOrientation with
        exactLeftRight | exactRightLeft
      · exact Or.inl (.rightContext left exactLeftRight)
      · exact Or.inr (.rightContext left exactRightLeft)
termination_by depth

end ExactDoubleOrientationAt

/-- The endpoint growth forced by one exact double-rotation shape. -/
def PostStepSpineStrict
    {n firstLower firstUpper finalLower finalUpper : ℕ}
    {snapshot : Snapshot n} {key : Fin n}
    {leftBoundary rightBoundary : External n}
    {base : SpineBase key leftBoundary rightBoundary}
    {firstTree : BST firstLower firstUpper}
    {finalTree : BST finalLower finalUpper}
    (shape : DoubleStepShape)
    (first :
      FocusedSpines snapshot key leftBoundary rightBoundary base firstTree)
    (final :
      FocusedSpines snapshot key leftBoundary rightBoundary base finalTree) :
    Prop :=
  match shape with
  | .zigZigLeft =>
      (FocusedSpines.spinePair first).rightUpper <
        (FocusedSpines.spinePair final).rightUpper
  | .zigZigRight =>
      (FocusedSpines.spinePair final).leftLower <
        (FocusedSpines.spinePair first).leftLower
  | .zigZagLeftRight
  | .zigZagRightLeft =>
      (FocusedSpines.spinePair final).leftLower <
          (FocusedSpines.spinePair first).leftLower ∧
        (FocusedSpines.spinePair first).rightUpper <
          (FocusedSpines.spinePair final).rightUpper

namespace ExactDoubleOrientationAt

/--
Every exact contextual double rotation strictly extends precisely the
terminal spine or spines named by its root shape.
-/
private theorem postStepSpineStrict_of_key_eq
    {shape : DoubleStepShape}
    {n lower upper depth keyValue : ℕ}
    {snapshot : Snapshot n} {key : Fin n}
    {leftBoundary rightBoundary : External n}
    {base : SpineBase key leftBoundary rightBoundary}
    {before after : BST lower upper}
    (orientation :
      ExactDoubleOrientationAt shape
        (depth := depth) (key := keyValue) before after)
    (keyEq : keyValue = key.val)
    (focused :
      FocusedSpines snapshot key leftBoundary rightBoundary base before)
    (headResult : FocusedSpines.PrefixResult focused after) :
    PostStepSpineStrict shape focused headResult.focused := by
  induction orientation generalizing key with
  | @zigZigLeft lower first second third upper a b c d =>
      subst first
      cases focused with
      | atKey leftSpine rightSpine =>
          have bBounds := b.lower_le_upper
          have cBounds := c.lower_le_upper
          omega
      | leftContext firstFocused contextRight =>
          cases firstFocused with
          | atKey leftSpine rightSpine =>
              have bBounds := b.lower_le_upper
              omega
          | leftContext keyFocused contextRight =>
              cases keyFocused with
              | atKey leftSpine rightSpine =>
                  cases headResult.focused with
                  | atKey finalLeftSpine finalRightSpine =>
                      simp only [PostStepSpineStrict,
                        FocusedSpines.spinePair]
                      have bBounds := b.lower_le_upper
                      have cBounds := c.lower_le_upper
                      have dBounds := d.lower_le_upper
                      omega
                  | leftContext finalFocused finalRight =>
                      have bounds := FocusedSpines.key_bounds finalFocused
                      omega
                  | rightContext finalLeft finalFocused =>
                      have bounds := FocusedSpines.key_bounds finalFocused
                      omega
              | leftContext nestedFocused nestedRight =>
                  have bounds := FocusedSpines.key_bounds nestedFocused
                  omega
              | rightContext nestedLeft nestedFocused =>
                  have bounds := FocusedSpines.key_bounds nestedFocused
                  omega
          | rightContext contextLeft keyFocused =>
              have bounds := FocusedSpines.key_bounds keyFocused
              have bBounds := b.lower_le_upper
              omega
      | rightContext contextLeft keyFocused =>
          have bounds := FocusedSpines.key_bounds keyFocused
          have bBounds := b.lower_le_upper
          have cBounds := c.lower_le_upper
          omega
  | @zigZigRight lower first second third upper a b c d =>
      subst third
      cases focused with
      | atKey leftSpine rightSpine =>
          have bBounds := b.lower_le_upper
          have cBounds := c.lower_le_upper
          omega
      | leftContext keyFocused contextRight =>
          have bounds := FocusedSpines.key_bounds keyFocused
          have bBounds := b.lower_le_upper
          have cBounds := c.lower_le_upper
          omega
      | rightContext contextLeft thirdFocused =>
          cases thirdFocused with
          | atKey leftSpine rightSpine =>
              have cBounds := c.lower_le_upper
              omega
          | leftContext keyFocused contextRight =>
              have bounds := FocusedSpines.key_bounds keyFocused
              have cBounds := c.lower_le_upper
              omega
          | rightContext contextLeft keyFocused =>
              cases keyFocused with
              | atKey leftSpine rightSpine =>
                  cases headResult.focused with
                  | atKey finalLeftSpine finalRightSpine =>
                      simp only [PostStepSpineStrict,
                        FocusedSpines.spinePair]
                      have aBounds := a.lower_le_upper
                      have bBounds := b.lower_le_upper
                      have cBounds := c.lower_le_upper
                      omega
                  | leftContext finalFocused finalRight =>
                      have bounds := FocusedSpines.key_bounds finalFocused
                      omega
                  | rightContext finalLeft finalFocused =>
                      have bounds := FocusedSpines.key_bounds finalFocused
                      omega
              | leftContext nestedFocused nestedRight =>
                  have bounds := FocusedSpines.key_bounds nestedFocused
                  omega
              | rightContext nestedLeft nestedFocused =>
                  have bounds := FocusedSpines.key_bounds nestedFocused
                  omega
  | @zigZagLeftRight lower first second third upper a b c d =>
      subst second
      cases focused with
      | atKey leftSpine rightSpine =>
          have cBounds := c.lower_le_upper
          omega
      | leftContext secondFocused contextRight =>
          cases secondFocused with
          | atKey leftSpine rightSpine =>
              have bBounds := b.lower_le_upper
              omega
          | leftContext keyFocused contextRight =>
              have bounds := FocusedSpines.key_bounds keyFocused
              have bBounds := b.lower_le_upper
              omega
          | rightContext contextLeft keyFocused =>
              cases keyFocused with
              | atKey leftSpine rightSpine =>
                  cases headResult.focused with
                  | atKey finalLeftSpine finalRightSpine =>
                      simp only [PostStepSpineStrict,
                        FocusedSpines.spinePair]
                      have aBounds := a.lower_le_upper
                      have bBounds := b.lower_le_upper
                      have cBounds := c.lower_le_upper
                      have dBounds := d.lower_le_upper
                      omega
                  | leftContext finalFocused finalRight =>
                      have bounds := FocusedSpines.key_bounds finalFocused
                      omega
                  | rightContext finalLeft finalFocused =>
                      have bounds := FocusedSpines.key_bounds finalFocused
                      omega
              | leftContext nestedFocused nestedRight =>
                  have bounds := FocusedSpines.key_bounds nestedFocused
                  omega
              | rightContext nestedLeft nestedFocused =>
                  have bounds := FocusedSpines.key_bounds nestedFocused
                  omega
      | rightContext contextLeft keyFocused =>
          have bounds := FocusedSpines.key_bounds keyFocused
          have cBounds := c.lower_le_upper
          omega
  | @zigZagRightLeft lower first second third upper a b c d =>
      subst second
      cases focused with
      | atKey leftSpine rightSpine =>
          have bBounds := b.lower_le_upper
          omega
      | leftContext keyFocused contextRight =>
          have bounds := FocusedSpines.key_bounds keyFocused
          have bBounds := b.lower_le_upper
          omega
      | rightContext contextLeft secondFocused =>
          cases secondFocused with
          | atKey leftSpine rightSpine =>
              have cBounds := c.lower_le_upper
              omega
          | leftContext keyFocused contextRight =>
              cases keyFocused with
              | atKey leftSpine rightSpine =>
                  cases headResult.focused with
                  | atKey finalLeftSpine finalRightSpine =>
                      simp only [PostStepSpineStrict,
                        FocusedSpines.spinePair]
                      have aBounds := a.lower_le_upper
                      have bBounds := b.lower_le_upper
                      have cBounds := c.lower_le_upper
                      have dBounds := d.lower_le_upper
                      omega
                  | leftContext finalFocused finalRight =>
                      have bounds := FocusedSpines.key_bounds finalFocused
                      omega
                  | rightContext finalLeft finalFocused =>
                      have bounds := FocusedSpines.key_bounds finalFocused
                      omega
              | leftContext nestedFocused nestedRight =>
                  have bounds := FocusedSpines.key_bounds nestedFocused
                  omega
              | rightContext nestedLeft nestedFocused =>
                  have bounds := FocusedSpines.key_bounds nestedFocused
                  omega
          | rightContext contextLeft keyFocused =>
              have bounds := FocusedSpines.key_bounds keyFocused
              have cBounds := c.lower_le_upper
              omega
  | @leftContext shape depth keyValue lower pivot upper
      before after innerOrientation contextRight ih =>
      cases focused with
      | atKey leftSpine rightSpine =>
          have stepBounds := innerOrientation.key_bounds
          omega
      | leftContext innerFocused finalRight =>
          cases headResult with
          | mk resultFocused resultPrefix =>
              cases resultFocused with
              | atKey finalLeftSpine finalRightSpine =>
                  have stepBounds := innerOrientation.key_bounds
                  omega
              | leftContext finalFocused contextRight =>
                  let innerResult :
                      FocusedSpines.PrefixResult innerFocused after := {
                    focused := finalFocused
                    isPrefix :=
                      ⟨by
                          simpa only [FocusedSpines.spinePair] using
                            resultPrefix.left,
                        by
                          simpa only [FocusedSpines.spinePair] using
                            resultPrefix.right⟩
                  }
                  simpa only [PostStepSpineStrict,
                    FocusedSpines.spinePair] using
                    ih keyEq innerFocused innerResult
              | rightContext finalLeft finalFocused =>
                  have focusedBounds :=
                    FocusedSpines.key_bounds finalFocused
                  have stepBounds := innerOrientation.key_bounds
                  omega
      | rightContext finalLeft innerFocused =>
          have focusedBounds := FocusedSpines.key_bounds innerFocused
          have stepBounds := innerOrientation.key_bounds
          omega
  | @rightContext shape depth keyValue lower pivot upper
      contextLeft before after innerOrientation ih =>
      cases focused with
      | atKey leftSpine rightSpine =>
          have stepBounds := innerOrientation.key_bounds
          omega
      | leftContext innerFocused finalRight =>
          have focusedBounds := FocusedSpines.key_bounds innerFocused
          have stepBounds := innerOrientation.key_bounds
          omega
      | rightContext finalLeft innerFocused =>
          cases headResult with
          | mk resultFocused resultPrefix =>
              cases resultFocused with
              | atKey finalLeftSpine finalRightSpine =>
                  have stepBounds := innerOrientation.key_bounds
                  omega
              | leftContext finalFocused contextRight =>
                  have focusedBounds :=
                    FocusedSpines.key_bounds finalFocused
                  have stepBounds := innerOrientation.key_bounds
                  omega
              | rightContext contextLeft finalFocused =>
                  let innerResult :
                      FocusedSpines.PrefixResult innerFocused after := {
                    focused := finalFocused
                    isPrefix :=
                      ⟨by
                          simpa only [FocusedSpines.spinePair] using
                            resultPrefix.left,
                        by
                          simpa only [FocusedSpines.spinePair] using
                            resultPrefix.right⟩
                  }
                  simpa only [PostStepSpineStrict,
                    FocusedSpines.spinePair] using
                    ih keyEq innerFocused innerResult

/--
Every exact contextual double rotation strictly extends precisely the
terminal spine or spines named by its root shape.
-/
theorem postStepSpineStrict
    {shape : DoubleStepShape}
    {n lower upper depth : ℕ}
    {snapshot : Snapshot n} {key : Fin n}
    {leftBoundary rightBoundary : External n}
    {base : SpineBase key leftBoundary rightBoundary}
    {before after : BST lower upper}
    (orientation :
      ExactDoubleOrientationAt shape
        (depth := depth) (key := key.val) before after)
    (focused :
      FocusedSpines snapshot key leftBoundary rightBoundary base before)
    (headResult : FocusedSpines.PrefixResult focused after) :
    PostStepSpineStrict shape focused headResult.focused :=
  postStepSpineStrict_of_key_eq orientation rfl focused headResult

end ExactDoubleOrientationAt

private theorem right_incomingAtBase_ne_none_of_upper_lt
    {n key baseUpper firstUpper finalUpper : ℕ}
    {snapshot : Snapshot n}
    {base : BST (key + 1) baseUpper}
    {firstTree : BST (key + 1) firstUpper}
    {finalTree : BST (key + 1) finalUpper}
    (firstSpine : RightSpine snapshot base firstTree)
    (finalSpine : RightSpine snapshot base finalTree)
    (strict : firstUpper < finalUpper) :
    Splay.Accounting.WholeSplayTemporaryFinalSpineBends.RightSpine.incomingAtBase
        finalSpine ≠ none := by
  cases finalSpine with
  | base finalBound =>
      have base_le_first :=
        RightSpine.baseUpper_le_upper firstSpine
      simp only [
        Splay.Accounting.WholeSplayTemporaryFinalSpineBends.RightSpine.incomingAtBase]
      omega
  | grow innerSpine hanging upperBound heavy =>
      simp [
        Splay.Accounting.WholeSplayTemporaryFinalSpineBends.RightSpine.incomingAtBase]

private theorem left_incomingAtBase_ne_none_of_lower_lt
    {n key baseLower firstLower finalLower : ℕ}
    {snapshot : Snapshot n}
    {base : BST baseLower key}
    {firstTree : BST firstLower key}
    {finalTree : BST finalLower key}
    (firstSpine : LeftSpine snapshot base firstTree)
    (finalSpine : LeftSpine snapshot base finalTree)
    (strict : finalLower < firstLower) :
    Splay.Accounting.WholeSplayTemporaryFinalSpineBends.LeftSpine.incomingAtBase
        finalSpine ≠ none := by
  cases finalSpine with
  | base finalBound =>
      have first_le_base :=
        LeftSpine.lower_le_baseLower firstSpine
      simp only [
        Splay.Accounting.WholeSplayTemporaryFinalSpineBends.LeftSpine.incomingAtBase]
      omega
  | grow innerSpine hanging rootBound keyBound heavy =>
      simp [
        Splay.Accounting.WholeSplayTemporaryFinalSpineBends.LeftSpine.incomingAtBase]

/-- A left final zig necessarily makes the terminal right spine nontrivial. -/
theorem zigFromLeft_right_incomingAtBase_ne_none
    {n lower demoted upper : ℕ}
    {snapshot : Snapshot n} {key : Fin n}
    {leftBoundary rightBoundary : External n}
    {base : SpineBase key leftBoundary rightBoundary}
    (a : BST lower key.val)
    (b : BST (key.val + 1) demoted)
    (c : BST (demoted + 1) upper)
    (focused :
      FocusedSpines snapshot key leftBoundary rightBoundary base
        (.node (.node a b) c))
    (_step :
      Zig key.val
        (.node (.node a b) c)
        (.node a (.node b c)))
    (headResult :
      FocusedSpines.PrefixResult focused
        (.node a (.node b c))) :
    Splay.Accounting.WholeSplayTemporaryFinalSpineBends.RightSpine.incomingAtBase
        (FocusedSpines.spinePair headResult.focused).rightSpine ≠ none := by
  apply
    right_incomingAtBase_ne_none_of_upper_lt
      (FocusedSpines.spinePair focused).rightSpine
      (FocusedSpines.spinePair headResult.focused).rightSpine
  cases focused with
  | atKey leftSpine rightSpine =>
      have bBounds := b.lower_le_upper
      omega
  | leftContext innerFocused contextRight =>
      cases innerFocused with
      | atKey leftSpine rightSpine =>
          cases headResult.focused with
          | atKey finalLeftSpine finalRightSpine =>
              simp only [FocusedSpines.spinePair]
              have cBounds := c.lower_le_upper
              omega
          | leftContext finalFocused finalRight =>
              have bounds := FocusedSpines.key_bounds finalFocused
              omega
          | rightContext finalLeft finalFocused =>
              have bounds := FocusedSpines.key_bounds finalFocused
              omega
      | leftContext nestedFocused nestedRight =>
          have bounds := FocusedSpines.key_bounds nestedFocused
          omega
      | rightContext nestedLeft nestedFocused =>
          have bounds := FocusedSpines.key_bounds nestedFocused
          omega
  | rightContext contextLeft innerFocused =>
      have bounds := FocusedSpines.key_bounds innerFocused
      have bBounds := b.lower_le_upper
      omega

/-- A right final zig necessarily makes the terminal left spine nontrivial. -/
theorem zigFromRight_left_incomingAtBase_ne_none
    {n lower demoted upper : ℕ}
    {snapshot : Snapshot n} {key : Fin n}
    {leftBoundary rightBoundary : External n}
    {base : SpineBase key leftBoundary rightBoundary}
    (a : BST lower demoted)
    (b : BST (demoted + 1) key.val)
    (c : BST (key.val + 1) upper)
    (focused :
      FocusedSpines snapshot key leftBoundary rightBoundary base
        (.node a (.node b c)))
    (_step :
      Zig key.val
        (.node a (.node b c))
        (.node (.node a b) c))
    (headResult :
      FocusedSpines.PrefixResult focused
        (.node (.node a b) c)) :
    Splay.Accounting.WholeSplayTemporaryFinalSpineBends.LeftSpine.incomingAtBase
        (FocusedSpines.spinePair headResult.focused).leftSpine ≠ none := by
  apply
    left_incomingAtBase_ne_none_of_lower_lt
      (FocusedSpines.spinePair focused).leftSpine
      (FocusedSpines.spinePair headResult.focused).leftSpine
  cases focused with
  | atKey leftSpine rightSpine =>
      have bBounds := b.lower_le_upper
      omega
  | leftContext innerFocused contextRight =>
      have bounds := FocusedSpines.key_bounds innerFocused
      have bBounds := b.lower_le_upper
      omega
  | rightContext contextLeft innerFocused =>
      cases innerFocused with
      | atKey leftSpine rightSpine =>
          cases headResult.focused with
          | atKey finalLeftSpine finalRightSpine =>
              simp only [FocusedSpines.spinePair]
              have aBounds := a.lower_le_upper
              omega
          | leftContext finalFocused finalRight =>
              have bounds := FocusedSpines.key_bounds finalFocused
              omega
          | rightContext finalLeft finalFocused =>
              have bounds := FocusedSpines.key_bounds finalFocused
              omega
      | leftContext nestedFocused nestedRight =>
          have bounds := FocusedSpines.key_bounds nestedFocused
          omega
      | rightContext nestedLeft nestedFocused =>
          have bounds := FocusedSpines.key_bounds nestedFocused
          omega

/--
An exact contextual left-left zig-zig necessarily makes the terminal right
spine nontrivial.
-/
theorem zigZigLeft_right_incomingAtBase_ne_none
    {n lower upper depth : ℕ}
    {snapshot : Snapshot n} {key : Fin n}
    {leftBoundary rightBoundary : External n}
    {base : SpineBase key leftBoundary rightBoundary}
    {before after : BST lower upper}
    (orientation :
      ExactDoubleOrientationAt .zigZigLeft
        (depth := depth) (key := key.val) before after)
    (focused :
      FocusedSpines snapshot key leftBoundary rightBoundary base before)
    (headResult : FocusedSpines.PrefixResult focused after) :
    Splay.Accounting.WholeSplayTemporaryFinalSpineBends.RightSpine.incomingAtBase
        (FocusedSpines.spinePair headResult.focused).rightSpine ≠ none := by
  apply
    right_incomingAtBase_ne_none_of_upper_lt
      (FocusedSpines.spinePair focused).rightSpine
      (FocusedSpines.spinePair headResult.focused).rightSpine
  simpa only [PostStepSpineStrict] using
    orientation.postStepSpineStrict focused headResult

/--
An exact contextual right-right zig-zig necessarily makes the terminal left
spine nontrivial.
-/
theorem zigZigRight_left_incomingAtBase_ne_none
    {n lower upper depth : ℕ}
    {snapshot : Snapshot n} {key : Fin n}
    {leftBoundary rightBoundary : External n}
    {base : SpineBase key leftBoundary rightBoundary}
    {before after : BST lower upper}
    (orientation :
      ExactDoubleOrientationAt .zigZigRight
        (depth := depth) (key := key.val) before after)
    (focused :
      FocusedSpines snapshot key leftBoundary rightBoundary base before)
    (headResult : FocusedSpines.PrefixResult focused after) :
    Splay.Accounting.WholeSplayTemporaryFinalSpineBends.LeftSpine.incomingAtBase
        (FocusedSpines.spinePair headResult.focused).leftSpine ≠ none := by
  apply
    left_incomingAtBase_ne_none_of_lower_lt
      (FocusedSpines.spinePair focused).leftSpine
      (FocusedSpines.spinePair headResult.focused).leftSpine
  simpa only [PostStepSpineStrict] using
    orientation.postStepSpineStrict focused headResult

/--
An exact contextual left-right zig-zag necessarily makes both terminal
spines nontrivial.
-/
theorem zigZagLeftRight_both_incomingAtBase_ne_none
    {n lower upper depth : ℕ}
    {snapshot : Snapshot n} {key : Fin n}
    {leftBoundary rightBoundary : External n}
    {base : SpineBase key leftBoundary rightBoundary}
    {before after : BST lower upper}
    (orientation :
      ExactDoubleOrientationAt .zigZagLeftRight
        (depth := depth) (key := key.val) before after)
    (focused :
      FocusedSpines snapshot key leftBoundary rightBoundary base before)
    (headResult : FocusedSpines.PrefixResult focused after) :
    (Splay.Accounting.WholeSplayTemporaryFinalSpineBends.LeftSpine.incomingAtBase
        (FocusedSpines.spinePair headResult.focused).leftSpine ≠ none) ∧
      (Splay.Accounting.WholeSplayTemporaryFinalSpineBends.RightSpine.incomingAtBase
        (FocusedSpines.spinePair headResult.focused).rightSpine ≠ none) := by
  have strict :=
    orientation.postStepSpineStrict focused headResult
  constructor
  · apply
      left_incomingAtBase_ne_none_of_lower_lt
        (FocusedSpines.spinePair focused).leftSpine
        (FocusedSpines.spinePair headResult.focused).leftSpine
    simpa only [PostStepSpineStrict] using strict.1
  · apply
      right_incomingAtBase_ne_none_of_upper_lt
        (FocusedSpines.spinePair focused).rightSpine
        (FocusedSpines.spinePair headResult.focused).rightSpine
    simpa only [PostStepSpineStrict] using strict.2

/--
An exact contextual right-left zig-zag necessarily makes both terminal
spines nontrivial.
-/
theorem zigZagRightLeft_both_incomingAtBase_ne_none
    {n lower upper depth : ℕ}
    {snapshot : Snapshot n} {key : Fin n}
    {leftBoundary rightBoundary : External n}
    {base : SpineBase key leftBoundary rightBoundary}
    {before after : BST lower upper}
    (orientation :
      ExactDoubleOrientationAt .zigZagRightLeft
        (depth := depth) (key := key.val) before after)
    (focused :
      FocusedSpines snapshot key leftBoundary rightBoundary base before)
    (headResult : FocusedSpines.PrefixResult focused after) :
    (Splay.Accounting.WholeSplayTemporaryFinalSpineBends.LeftSpine.incomingAtBase
        (FocusedSpines.spinePair headResult.focused).leftSpine ≠ none) ∧
      (Splay.Accounting.WholeSplayTemporaryFinalSpineBends.RightSpine.incomingAtBase
        (FocusedSpines.spinePair headResult.focused).rightSpine ≠ none) := by
  have strict :=
    orientation.postStepSpineStrict focused headResult
  constructor
  · apply
      left_incomingAtBase_ne_none_of_lower_lt
        (FocusedSpines.spinePair focused).leftSpine
        (FocusedSpines.spinePair headResult.focused).leftSpine
    simpa only [PostStepSpineStrict] using strict.1
  · apply
      right_incomingAtBase_ne_none_of_upper_lt
        (FocusedSpines.spinePair focused).rightSpine
        (FocusedSpines.spinePair headResult.focused).rightSpine
    simpa only [PostStepSpineStrict] using strict.2

end Splay.Accounting.WholeSplayTemporaryFocusedStepNontriviality
