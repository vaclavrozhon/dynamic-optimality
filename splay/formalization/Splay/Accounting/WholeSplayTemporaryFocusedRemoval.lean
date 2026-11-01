import Splay.Accounting.WholeSplayTemporarySpineRemoval
import Splay.Accounting.WholeSplayTemporaryRemovalGeometry

namespace Splay.Accounting.WholeSplayTemporaryFocusedRemoval

open Splay.Rank
open Splay.Tree
open Splay.Tree.BST
open Splay.Accounting.LocalBendGeometry
open Splay.Accounting.WholeSplayTemporaryPriorityReduction
open Splay.Accounting.WholeSplayTemporaryCoreGeometry
open Splay.Accounting.WholeSplayTemporaryFocusedSpines
open Splay.Accounting.WholeSplayTemporarySpineGeometry
open Splay.Accounting.WholeSplayTemporarySpineRemoval
open Splay.Accounting.WholeSplayTemporaryRemovalGeometry

/-!
The removal invariant is most naturally stated for every strict ancestor of
the accessed key, not just for ancestors at which the search direction
changes.  Each bottom-up splay step removes one or two such ancestors.
The proof-relevant focused-spine construction records those exact keys as
inward spine roots or roots of light hanging subtrees.
-/

/-- All strict ancestors encountered while searching for `key`. -/
noncomputable def searchPathKeys
    {n lower upper : ℕ} (tree : BST lower upper)
    (upper_le_n : upper ≤ n) (key : ℕ) : Finset (Fin n) :=
  match tree with
  | .empty _ => ∅
  | .node (root := root) left right =>
      let rootKey : Fin n := ⟨root, by
        have rightBounds := right.lower_le_upper
        omega⟩
      if key = root then
        ∅
      else if key < root then
        insert rootKey
          (searchPathKeys left (by
            have rightBounds := right.lower_le_upper
            omega) key)
      else
        insert rootKey (searchPathKeys right upper_le_n key)
termination_by tree.size
decreasing_by
  all_goals simp [_root_.Splay.Tree.BST.size] <;> omega

/-- Every initial search turn is, in particular, a strict search ancestor. -/
theorem searchTurnKeysFrom_subset_searchPathKeys
    {n lower upper : ℕ} (incoming : Option TernaryBranch)
    (tree : BST lower upper) (upper_le_n : upper ≤ n) (key : ℕ) :
    searchTurnKeysFrom incoming tree upper_le_n key ⊆
      searchPathKeys tree upper_le_n key := by
  induction tree generalizing incoming key with
  | empty =>
      simp [searchTurnKeysFrom, searchPathKeys]
  | @node lower root upper left right leftIH rightIH =>
      have leftBounds := left.lower_le_upper
      have rightBounds := right.lower_le_upper
      simp only [searchTurnKeysFrom, searchPathKeys]
      split
      · simp
      · split
        · split
          · intro identity member
            simp only [Finset.mem_insert] at member ⊢
            exact member.imp_right
              (fun tailMember =>
                leftIH (some .left) (by omega) key tailMember)
          · intro identity member
            exact Finset.mem_insert_of_mem
              (leftIH (some .left) (by omega) key member)
        · split
          · intro identity member
            simp only [Finset.mem_insert] at member ⊢
            exact member.imp_right
              (fun tailMember =>
                rightIH (some .right) upper_le_n key tailMember)
          · intro identity member
            exact Finset.mem_insert_of_mem
              (rightIH (some .right) upper_le_n key member)

/-- The union of all keys already retired into the two focused spines. -/
noncomputable def focusedSilentKeys
    {n lower upper : ℕ} {snapshot : Snapshot n} {key : Fin n}
    {leftBoundary rightBoundary : External n}
    {base : SpineBase key leftBoundary rightBoundary}
    {tree : BST lower upper}
    (focused :
      FocusedSpines snapshot key leftBoundary rightBoundary base tree) :
    Finset (Fin n) :=
  WholeSplayTemporarySpineRemoval.LeftSpine.silentKeys
      (FocusedSpines.spinePair focused).leftSpine ∪
    WholeSplayTemporarySpineRemoval.RightSpine.silentKeys
      (FocusedSpines.spinePair focused).rightSpine

namespace RightSpine.IsPrefix

/-- Silent keys persist under right-spine extension. -/
theorem silentKeys_subset
    {n key baseUpper oldUpper finalUpper : ℕ}
    {snapshot : Snapshot n}
    {base : BST (key + 1) baseUpper}
    {oldTree : BST (key + 1) oldUpper}
    {finalTree : BST (key + 1) finalUpper}
    {oldSpine : RightSpine snapshot base oldTree}
    {finalSpine : RightSpine snapshot base finalTree}
    (extension : RightSpine.IsPrefix oldSpine finalSpine) :
    WholeSplayTemporarySpineRemoval.RightSpine.silentKeys oldSpine ⊆
      WholeSplayTemporarySpineRemoval.RightSpine.silentKeys finalSpine := by
  induction extension with
  | refl =>
      exact Finset.Subset.rfl
  | grow prior hanging upper_le_n heavy ih =>
      intro identity member
      simp only [
        WholeSplayTemporarySpineRemoval.RightSpine.silentKeys,
        Finset.mem_insert, Finset.mem_union]
      exact Or.inr (Or.inl (ih member))

end RightSpine.IsPrefix

namespace LeftSpine.IsPrefix

/-- Silent keys persist under left-spine extension. -/
theorem silentKeys_subset
    {n key baseLower oldLower finalLower : ℕ}
    {snapshot : Snapshot n}
    {base : BST baseLower key}
    {oldTree : BST oldLower key}
    {finalTree : BST finalLower key}
    {oldSpine : LeftSpine snapshot base oldTree}
    {finalSpine : LeftSpine snapshot base finalTree}
    (extension : LeftSpine.IsPrefix oldSpine finalSpine) :
    WholeSplayTemporarySpineRemoval.LeftSpine.silentKeys oldSpine ⊆
      WholeSplayTemporarySpineRemoval.LeftSpine.silentKeys finalSpine := by
  induction extension with
  | refl =>
      exact Finset.Subset.rfl
  | grow prior hanging root_le_n key_le_n heavy ih =>
      intro identity member
      simp only [
        WholeSplayTemporarySpineRemoval.LeftSpine.silentKeys,
        Finset.mem_insert, Finset.mem_union]
      exact Or.inr (Or.inr (ih member))

end LeftSpine.IsPrefix

namespace FocusedSpines.IsPrefix

/-- The accumulated focused silent set is monotone along a run. -/
theorem silentKeys_subset
    {n firstLower firstUpper finalLower finalUpper : ℕ}
    {snapshot : Snapshot n} {key : Fin n}
    {leftBoundary rightBoundary : External n}
    {base : SpineBase key leftBoundary rightBoundary}
    {firstTree : BST firstLower firstUpper}
    {finalTree : BST finalLower finalUpper}
    {first :
      FocusedSpines snapshot key leftBoundary rightBoundary base firstTree}
    {final :
      FocusedSpines snapshot key leftBoundary rightBoundary base finalTree}
    (extension : FocusedSpines.IsPrefix first final) :
    focusedSilentKeys first ⊆ focusedSilentKeys final := by
  intro identity member
  simp only [focusedSilentKeys, Finset.mem_union] at member ⊢
  exact member.imp
    (fun leftMember =>
      LeftSpine.IsPrefix.silentKeys_subset extension.left leftMember)
    (fun rightMember =>
      RightSpine.IsPrefix.silentKeys_subset extension.right rightMember)

end FocusedSpines.IsPrefix

/--
A focused step result strengthened by the exact search-path keys retired by
that step.
-/
structure PathPrefixResult
    {n lower upper : ℕ} {snapshot : Snapshot n} {key : Fin n}
    {leftBoundary rightBoundary : External n}
    {base : SpineBase key leftBoundary rightBoundary}
    {firstTree : BST lower upper}
    (first :
      FocusedSpines snapshot key leftBoundary rightBoundary base firstTree)
    (finalTree : BST lower upper) (upper_le_n : upper ≤ n) : Type where
  focused :
    FocusedSpines snapshot key leftBoundary rightBoundary base finalTree
  isPrefix : FocusedSpines.IsPrefix first focused
  path_subset :
    searchPathKeys firstTree upper_le_n key.val ⊆
      searchPathKeys finalTree upper_le_n key.val ∪
        focusedSilentKeys focused

/--
A final zig retires its unique former search-path parent into the matching
focused spine.
-/
theorem nonempty_after_zig_withPath
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
    Nonempty (PathPrefixResult focused after upper_le_n) := by
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
                  isPrefix :=
                    ⟨.refl,
                      RightSpine.IsPrefix.of_grow_temporarySnapshot
                        comparison key comparisonRoot
                        leftBoundary rightBoundary ordered base
                        rightSpine c upper_le_n⟩
                  path_subset := by
                    have aBounds := a.lower_le_upper
                    have bBounds := b.lower_le_upper
                    have cBounds := c.lower_le_upper
                    have keyToRoot : key.val < demoted := by omega
                    intro identity member
                    simp [
                      searchPathKeys, focusedSilentKeys,
                      FocusedSpines.spinePair, finalRight,
                      RightSpine.grow_temporarySnapshot,
                      WholeSplayTemporarySpineRemoval.RightSpine.silentKeys,
                      keyToRoot, ne_of_lt keyToRoot]
                      at member ⊢
                    exact Or.inl member
                }⟩
          | leftContext focused rightTree =>
              have bounds := FocusedSpines.key_bounds focused
              omega
          | rightContext leftTree focused =>
              have bounds := FocusedSpines.key_bounds focused
              omega
      | rightContext leftTree innerFocused =>
          have bounds := FocusedSpines.key_bounds innerFocused
          have middleBounds := b.lower_le_upper
          omega
  | @fromRight lower demoted promoted upper a b c =>
      cases focused with
      | atKey leftSpine rightSpine =>
          have middleBounds := b.lower_le_upper
          omega
      | leftContext innerFocused rightTree =>
          have bounds := FocusedSpines.key_bounds innerFocused
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
                  isPrefix :=
                    ⟨LeftSpine.IsPrefix.of_grow_temporarySnapshot
                        comparison key comparisonRoot
                        leftBoundary rightBoundary ordered base
                        leftSpine a root_le_n,
                      .refl⟩
                  path_subset := by
                    have aBounds := a.lower_le_upper
                    have bBounds := b.lower_le_upper
                    have cBounds := c.lower_le_upper
                    have rootToKey : demoted < key.val := by omega
                    intro identity member
                    simp [
                      searchPathKeys, focusedSilentKeys,
                      FocusedSpines.spinePair, finalLeft,
                      LeftSpine.grow_temporarySnapshot,
                      WholeSplayTemporarySpineRemoval.LeftSpine.silentKeys,
                      Nat.not_lt_of_ge (Nat.le_of_lt rootToKey),
                      ne_of_gt rootToKey]
                      at member ⊢
                    exact Or.inl member
                }⟩
          | leftContext focused rightTree =>
              have bounds := FocusedSpines.key_bounds focused
              omega
          | rightContext leftTree focused =>
              have bounds := FocusedSpines.key_bounds focused
              omega

/--
A root double rotation retires both former search-path ancestors.  In a
same-direction step the outer one is exactly the root of the new hanging
subtree; in a zig-zag the two roots enter opposite spines.
-/
theorem nonempty_after_doubleRotation_withPath
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
    Nonempty (PathPrefixResult focused after upper_le_n) := by
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
                      isPrefix :=
                        ⟨.refl,
                          RightSpine.IsPrefix.of_grow_temporarySnapshot
                            comparison key comparisonRoot
                            leftBoundary rightBoundary ordered base
                            rightSpine (.node c d) upper_le_n⟩
                      path_subset := by
                        have aBounds := a.lower_le_upper
                        have bBounds := b.lower_le_upper
                        have cBounds := c.lower_le_upper
                        have dBounds := d.lower_le_upper
                        have keyToSecond : key.val < second := by omega
                        have keyToThird : key.val < third := by omega
                        intro identity member
                        simp [
                          searchPathKeys, focusedSilentKeys,
                          FocusedSpines.spinePair, finalRight,
                          RightSpine.grow_temporarySnapshot,
                          WholeSplayTemporarySpineRemoval.RightSpine.silentKeys,
                          WholeSplayTemporarySpineRemoval.rootKeySet,
                          keyToSecond, keyToThird,
                          ne_of_lt keyToSecond, ne_of_lt keyToThird]
                          at member ⊢
                        rcases member with atThird | atSecond
                        · exact Or.inr (Or.inl atThird)
                        · exact Or.inl atSecond
                    }⟩
              | leftContext focused b =>
                  have bounds := FocusedSpines.key_bounds focused
                  omega
              | rightContext a focused =>
                  have bounds := FocusedSpines.key_bounds focused
                  omega
          | rightContext leftTree focused =>
              have bounds := FocusedSpines.key_bounds focused
              have bBounds := b.lower_le_upper
              omega
      | rightContext leftTree focused =>
          have bounds := FocusedSpines.key_bounds focused
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
          have bounds := FocusedSpines.key_bounds focused
          have bBounds := b.lower_le_upper
          have cBounds := c.lower_le_upper
          omega
      | rightContext a thirdFocused =>
          cases thirdFocused with
          | atKey leftSpine rightSpine =>
              have cBounds := c.lower_le_upper
              omega
          | leftContext focused rightTree =>
              have bounds := FocusedSpines.key_bounds focused
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
                      isPrefix :=
                        ⟨LeftSpine.IsPrefix.of_grow_temporarySnapshot
                            comparison key comparisonRoot
                            leftBoundary rightBoundary ordered base
                            leftSpine (.node a b) root_le_n,
                          .refl⟩
                      path_subset := by
                        have aBounds := a.lower_le_upper
                        have bBounds := b.lower_le_upper
                        have cBounds := c.lower_le_upper
                        have dBounds := d.lower_le_upper
                        have firstToKey : first < key.val := by omega
                        have secondToKey : second < key.val := by omega
                        intro identity member
                        simp [
                          searchPathKeys, focusedSilentKeys,
                          FocusedSpines.spinePair, finalLeft,
                          LeftSpine.grow_temporarySnapshot,
                          WholeSplayTemporarySpineRemoval.LeftSpine.silentKeys,
                          WholeSplayTemporarySpineRemoval.rootKeySet,
                          Nat.not_lt_of_ge (Nat.le_of_lt firstToKey),
                          Nat.not_lt_of_ge (Nat.le_of_lt secondToKey),
                          ne_of_gt firstToKey, ne_of_gt secondToKey]
                          at member ⊢
                        rcases member with atFirst | atSecond
                        · exact Or.inr (Or.inl atFirst)
                        · exact Or.inl atSecond
                    }⟩
              | leftContext focused d =>
                  have bounds := FocusedSpines.key_bounds focused
                  omega
              | rightContext leftTree focused =>
                  have bounds := FocusedSpines.key_bounds focused
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
              have bounds := FocusedSpines.key_bounds focused
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
                      isPrefix :=
                        ⟨LeftSpine.IsPrefix.of_grow_temporarySnapshot
                            comparison key comparisonRoot
                            leftBoundary rightBoundary ordered base
                            leftSpine a root_le_n,
                          RightSpine.IsPrefix.of_grow_temporarySnapshot
                            comparison key comparisonRoot
                            leftBoundary rightBoundary ordered base
                            rightSpine d upper_le_n⟩
                      path_subset := by
                        have aBounds := a.lower_le_upper
                        have bBounds := b.lower_le_upper
                        have cBounds := c.lower_le_upper
                        have dBounds := d.lower_le_upper
                        have firstToKey : first < key.val := by omega
                        have keyToThird : key.val < third := by omega
                        intro identity member
                        simp [
                          searchPathKeys, focusedSilentKeys,
                          FocusedSpines.spinePair, finalLeft, finalRight,
                          LeftSpine.grow_temporarySnapshot,
                          RightSpine.grow_temporarySnapshot,
                          WholeSplayTemporarySpineRemoval.LeftSpine.silentKeys,
                          WholeSplayTemporarySpineRemoval.RightSpine.silentKeys,
                          Nat.not_lt_of_ge (Nat.le_of_lt firstToKey),
                          ne_of_gt firstToKey,
                          keyToThird, ne_of_lt keyToThird]
                          at member ⊢
                        rcases member with atThird | atFirst
                        · exact Or.inl atThird
                        · exact Or.inr (Or.inl atFirst)
                    }⟩
              | leftContext focused rightTree =>
                  have bounds := FocusedSpines.key_bounds focused
                  omega
              | rightContext leftTree focused =>
                  have bounds := FocusedSpines.key_bounds focused
                  omega
      | rightContext leftTree focused =>
          have bounds := FocusedSpines.key_bounds focused
          have cBounds := c.lower_le_upper
          omega
  | @zigZagRightLeft lower first second third upper a b c d =>
      cases focused with
      | atKey leftSpine rightSpine =>
          have bBounds := b.lower_le_upper
          omega
      | leftContext focused rightTree =>
          have bounds := FocusedSpines.key_bounds focused
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
                      isPrefix :=
                        ⟨LeftSpine.IsPrefix.of_grow_temporarySnapshot
                            comparison key comparisonRoot
                            leftBoundary rightBoundary ordered base
                            leftSpine a root_le_n,
                          RightSpine.IsPrefix.of_grow_temporarySnapshot
                            comparison key comparisonRoot
                            leftBoundary rightBoundary ordered base
                            rightSpine d upper_le_n⟩
                      path_subset := by
                        have aBounds := a.lower_le_upper
                        have bBounds := b.lower_le_upper
                        have cBounds := c.lower_le_upper
                        have dBounds := d.lower_le_upper
                        have firstToKey : first < key.val := by omega
                        have keyToThird : key.val < third := by omega
                        intro identity member
                        simp [
                          searchPathKeys, focusedSilentKeys,
                          FocusedSpines.spinePair, finalLeft, finalRight,
                          LeftSpine.grow_temporarySnapshot,
                          RightSpine.grow_temporarySnapshot,
                          WholeSplayTemporarySpineRemoval.LeftSpine.silentKeys,
                          WholeSplayTemporarySpineRemoval.RightSpine.silentKeys,
                          Nat.not_lt_of_ge (Nat.le_of_lt firstToKey),
                          ne_of_gt firstToKey,
                          keyToThird, ne_of_lt keyToThird]
                          at member ⊢
                        rcases member with atFirst | atThird
                        · exact Or.inr (Or.inl atFirst)
                        · exact Or.inl atThird
                    }⟩
              | leftContext focused rightTree =>
                  have bounds := FocusedSpines.key_bounds focused
                  omega
              | rightContext leftTree focused =>
                  have bounds := FocusedSpines.key_bounds focused
                  omega
          | rightContext leftTree focused =>
              have bounds := FocusedSpines.key_bounds focused
              have cBounds := c.lower_le_upper
              omega

/-- Contextual lifting of the root double-rotation path invariant. -/
private theorem nonempty_after_doubleRotationAt_withPath_of_eq
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
    Nonempty (PathPrefixResult focused after upper_le_n) := by
  induction step generalizing key with
  | root rootStep =>
      rw [← key_eq] at rootStep
      exact
        nonempty_after_doubleRotation_withPath
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
              isPrefix :=
                ⟨result.isPrefix.left, result.isPrefix.right⟩
              path_subset := by
                have stepBounds := innerStep.key_bounds
                have rightBounds := rightTree.lower_le_upper
                have keyToPivot : key.val < pivot := by omega
                intro identity member
                simp only [searchPathKeys]
                  at member ⊢
                simp [keyToPivot, ne_of_lt keyToPivot] at member ⊢
                rcases member with atRoot | innerMember
                · exact Or.inl atRoot
                · have nested := result.path_subset innerMember
                  simp only [Finset.mem_union] at nested
                  rcases nested with inPath | silent
                  · exact Or.inr (Or.inl inPath)
                  · exact Or.inr (Or.inr silent)
            }⟩
      | rightContext contextLeft innerFocused =>
          have focusedBounds := FocusedSpines.key_bounds innerFocused
          have stepBounds := innerStep.key_bounds
          omega
  | @rightContext depth keyValue childLower pivot childUpper
      leftTree before after innerStep ih =>
      cases focused with
      | atKey leftSpine rightSpine =>
          have stepBounds := innerStep.key_bounds
          omega
      | leftContext innerFocused contextRight =>
          have focusedBounds := FocusedSpines.key_bounds innerFocused
          have stepBounds := innerStep.key_bounds
          omega
      | rightContext contextLeft innerFocused =>
          obtain ⟨result⟩ :=
            ih key comparisonRoot ordered base innerFocused
              key_eq upper_le_n
          exact
            ⟨{
              focused := .rightContext leftTree result.focused
              isPrefix :=
                ⟨result.isPrefix.left, result.isPrefix.right⟩
              path_subset := by
                have stepBounds := innerStep.key_bounds
                have leftBounds := leftTree.lower_le_upper
                have pivotToKey : pivot < key.val := by omega
                intro identity member
                simp only [searchPathKeys]
                  at member ⊢
                simp [
                  Nat.not_lt_of_ge (Nat.le_of_lt pivotToKey),
                  ne_of_gt pivotToKey] at member ⊢
                rcases member with atRoot | innerMember
                · exact Or.inl atRoot
                · have nested := result.path_subset innerMember
                  simp only [Finset.mem_union] at nested
                  rcases nested with inPath | silent
                  · exact Or.inr (Or.inl inPath)
                  · exact Or.inr (Or.inr silent)
            }⟩

/-- Public finite-key specialization of contextual path retirement. -/
theorem nonempty_after_doubleRotationAt_withPath
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
    Nonempty (PathPrefixResult focused after upper_le_n) :=
  nonempty_after_doubleRotationAt_withPath_of_eq
    comparison key comparisonRoot leftBoundary rightBoundary
    ordered base focused step rfl upper_le_n

/-- One complete bottom-up splay step preserves the path/silent invariant. -/
theorem nonempty_after_splayStep_withPath
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
    (step : SplayStep key.val before after)
    (upper_le_n : upper ≤ n) :
    Nonempty (PathPrefixResult focused after upper_le_n) := by
  cases step with
  | zig zigStep =>
      exact
        nonempty_after_zig_withPath comparison key comparisonRoot
          leftBoundary rightBoundary ordered base focused zigStep upper_le_n
  | double doubleStep =>
      exact
        nonempty_after_doubleRotationAt_withPath
          comparison key comparisonRoot leftBoundary rightBoundary
          ordered base focused doubleStep upper_le_n

/-- Composition of the strengthened path invariant over an execution. -/
private theorem nonempty_after_execution_withPath_of_eq
    {n lower upper keyValue : ℕ}
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
    (execution : SplayExecution keyValue before after)
    (key_eq : key.val = keyValue)
    (upper_le_n : upper ≤ n) :
    Nonempty (PathPrefixResult focused after upper_le_n) := by
  induction execution generalizing key with
  | done root =>
      exact
        ⟨{
          focused := focused
          isPrefix := FocusedSpines.IsPrefix.refl focused
          path_subset := Finset.subset_union_left
        }⟩
  | next head tail ih =>
      rw [← key_eq] at head
      obtain ⟨headResult⟩ :=
        nonempty_after_splayStep_withPath
          comparison key comparisonRoot
          leftBoundary rightBoundary ordered base focused head upper_le_n
      obtain ⟨tailResult⟩ :=
        ih key comparisonRoot ordered base headResult.focused key_eq
      exact
        ⟨{
          focused := tailResult.focused
          isPrefix :=
            FocusedSpines.IsPrefix.trans
              headResult.isPrefix tailResult.isPrefix
          path_subset := by
            intro identity initialPath
            have headCases := headResult.path_subset initialPath
            simp only [Finset.mem_union] at headCases ⊢
            rcases headCases with middlePath | headSilent
            · have tailCases := tailResult.path_subset middlePath
              simpa only [Finset.mem_union] using tailCases
            · exact
                Or.inr
                  (FocusedSpines.IsPrefix.silentKeys_subset
                    tailResult.isPrefix headSilent)
        }⟩

/-- Public execution form of the accumulated path invariant. -/
theorem nonempty_after_execution_withPath
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
    (execution : SplayExecution key.val before after)
    (upper_le_n : upper ≤ n) :
    Nonempty (PathPrefixResult focused after upper_le_n) :=
  nonempty_after_execution_withPath_of_eq
    comparison key comparisonRoot leftBoundary rightBoundary
    ordered base focused execution rfl upper_le_n

/--
At the terminal accessed-key root the residual search path is empty, so all
initial strict search ancestors occur in the two final silent sets.
-/
theorem exists_terminal_spines_searchPath_subset_silent
    {n : ℕ} (comparison : BST 0 n) (key : Fin n)
    (comparisonRoot : comparison.HasRoot key.val)
    (leftBoundary rightBoundary : External n)
    (ordered :
      leftBoundary < valuePos key ∧ valuePos key < rightBoundary)
    (base : SpineBase key leftBoundary rightBoundary)
    {before : BST 0 n}
    {finalLeftTree : BST 0 key.val}
    {finalRightTree : BST (key.val + 1) n}
    (initial :
      FocusedSpines
        (temporarySnapshot comparison key comparisonRoot
          leftBoundary rightBoundary ordered)
        key leftBoundary rightBoundary base before)
    (execution :
      SplayExecution key.val before
        (.node finalLeftTree finalRightTree)) :
    ∃ finalLeft :
        LeftSpine
          (temporarySnapshot comparison key comparisonRoot
            leftBoundary rightBoundary ordered)
          base.leftTree finalLeftTree,
      ∃ finalRight :
          RightSpine
            (temporarySnapshot comparison key comparisonRoot
              leftBoundary rightBoundary ordered)
            base.rightTree finalRightTree,
        searchPathKeys before (Nat.le_refl n) key.val ⊆
          WholeSplayTemporarySpineRemoval.LeftSpine.silentKeys finalLeft ∪
            WholeSplayTemporarySpineRemoval.RightSpine.silentKeys
              finalRight := by
  obtain ⟨⟨finalFocused, finalPrefix, finalPath⟩⟩ :=
    nonempty_after_execution_withPath
      comparison key comparisonRoot leftBoundary rightBoundary
      ordered base initial execution (Nat.le_refl n)
  cases finalFocused with
  | atKey finalLeft finalRight =>
      refine ⟨finalLeft, finalRight, ?_⟩
      intro identity initialPath
      have terminalCases := finalPath initialPath
      change
        identity ∈
          searchPathKeys (.node finalLeftTree finalRightTree)
              (Nat.le_refl n) key.val ∪
            (WholeSplayTemporarySpineRemoval.LeftSpine.silentKeys
                finalLeft ∪
              WholeSplayTemporarySpineRemoval.RightSpine.silentKeys
                finalRight)
        at terminalCases
      simpa [searchPathKeys] using terminalCases
  | leftContext innerFocused contextRight =>
      have bounds := FocusedSpines.key_bounds innerFocused
      omega
  | rightContext contextLeft innerFocused =>
      have bounds := FocusedSpines.key_bounds innerFocused
      omega

/--
Neither final silent set intersects the complete temporary bend set.  The
same-side facts are the monotone-spine lemmas; the cross-side facts follow
from the indexed intervals around the promoted key.
-/
theorem silentKeys_disjoint_temporaryFinalBends
    {n baseLower baseUpper : ℕ}
    (comparison : BST 0 n) (key : Fin n)
    (comparisonRoot : comparison.HasRoot key.val)
    (leftBoundary rightBoundary : External n)
    (ordered :
      leftBoundary < valuePos key ∧ valuePos key < rightBoundary)
    {leftBase : BST baseLower key.val}
    {rightBase : BST (key.val + 1) baseUpper}
    {left : BST 0 key.val}
    {right : BST (key.val + 1) n}
    (leftSpine :
      LeftSpine
        (temporarySnapshot comparison key comparisonRoot
          leftBoundary rightBoundary ordered)
        leftBase left)
    (rightSpine :
      RightSpine
        (temporarySnapshot comparison key comparisonRoot
          leftBoundary rightBoundary ordered)
        rightBase right) :
    Disjoint
      (WholeSplayTemporarySpineRemoval.LeftSpine.silentKeys leftSpine ∪
        WholeSplayTemporarySpineRemoval.RightSpine.silentKeys rightSpine)
      (bends
        (temporarySnapshot comparison key comparisonRoot
          leftBoundary rightBoundary ordered)
        (.node left right)) := by
  classical
  apply Finset.disjoint_left.mpr
  intro identity silentMember bendMember
  rw [
    Splay.Accounting.WholeSplayTemporaryFinalSpineBends.temporaryFinalRoot_bends_eq
      comparison key comparisonRoot leftBoundary rightBoundary ordered
      leftSpine rightSpine,
    ← Splay.Accounting.WholeSplayTemporaryFinalSpineBends.LeftSpine.bendsFrom_none_eq
      leftSpine,
    ← Splay.Accounting.WholeSplayTemporaryFinalSpineBends.RightSpine.bendsFrom_none_eq
      rightSpine] at bendMember
  simp only [Finset.mem_union] at silentMember bendMember
  rcases silentMember with leftSilent | rightSilent
  · rcases bendMember with leftBend | rightBend
    · exact
        (Finset.disjoint_left.mp
          (WholeSplayTemporarySpineRemoval.LeftSpine.silentKeys_disjoint_bendsFrom
            leftSpine none (Or.inl rfl)))
          leftSilent leftBend
    · have silentBounds :=
        WholeSplayTemporarySpineRemoval.LeftSpine.mem_silentKeys_bounds
          leftSpine leftSilent
      have bendBounds :=
        mem_bendsFrom_bounds
          (temporarySnapshot comparison key comparisonRoot
            leftBoundary rightBoundary ordered)
          right rightSpine.upper_le_n none rightBend
      omega
  · rcases bendMember with leftBend | rightBend
    · have silentBounds :=
        WholeSplayTemporarySpineRemoval.RightSpine.mem_silentKeys_bounds
          rightSpine rightSilent
      have bendBounds :=
        mem_bendsFrom_bounds
          (temporarySnapshot comparison key comparisonRoot
            leftBoundary rightBoundary ordered)
          left leftSpine.upper_le_n none leftBend
      omega
    · exact
        (Finset.disjoint_left.mp
          (WholeSplayTemporarySpineRemoval.RightSpine.silentKeys_disjoint_bendsFrom
            rightSpine none (Or.inl rfl)))
          rightSilent rightBend

/--
Canonical, premise-free removal theorem: every direction-change identity on
the original search path is absent from the final temporary bend set.
-/
theorem canonical_finalSearchTurnsAbsent
    {n : ℕ} (comparison : BST 0 n) (key : Fin n)
    (comparisonRoot : comparison.HasRoot key.val)
    {before after : BST 0 n}
    (execution : SplayExecution key.val before after) :
    let selection :=
      WholeSplayTemporaryBoundaryGeometry.KeyFocus.boundaryMinimumSelection
        (Snapshot.ofTree comparison) before key
    ∀ turn ∈ searchTurnKeys before key.val,
      turn ∉
        bends
          (temporarySnapshot comparison key comparisonRoot
            selection.left selection.right selection.ordered)
          after := by
  let selection :=
    WholeSplayTemporaryBoundaryGeometry.KeyFocus.boundaryMinimumSelection
      (Snapshot.ofTree comparison) before key
  change
    ∀ turn ∈ searchTurnKeys before key.val,
      turn ∉
        bends
          (temporarySnapshot comparison key comparisonRoot
            selection.left selection.right selection.ordered)
          after
  obtain ⟨finalLeftTree, finalRightTree, rfl⟩ :=
    execution.hasRoot_after
  have placement :
      BoundaryPlacementAt key selection.left selection.right before := by
    simpa only [selection] using
      Splay.Accounting.WholeSplayTemporaryCoreClassification.canonicalBoundaryPlacement
        (Snapshot.ofTree comparison) before key
  let snapshot :=
    temporarySnapshot comparison key comparisonRoot
      selection.left selection.right selection.ordered
  obtain ⟨initial⟩ :=
    FocusedSpines.nonempty_initial_ofBoundaryPlacement
      snapshot key selection.left selection.right placement (Nat.le_refl n)
  obtain ⟨finalLeft, finalRight, pathToSilent⟩ :=
    exists_terminal_spines_searchPath_subset_silent
      comparison key comparisonRoot selection.left selection.right
      selection.ordered initial.base initial.focused execution
  have silentDisjoint :=
    silentKeys_disjoint_temporaryFinalBends
      comparison key comparisonRoot selection.left selection.right
      selection.ordered finalLeft finalRight
  intro turn turnMember finalBend
  have turnPath :
      turn ∈ searchPathKeys before (Nat.le_refl n) key.val := by
    apply
      searchTurnKeysFrom_subset_searchPathKeys
        none before (Nat.le_refl n) key.val
    simpa only [searchTurnKeys] using turnMember
  exact
    (Finset.disjoint_left.mp silentDisjoint)
      (pathToSilent turnPath) finalBend

end Splay.Accounting.WholeSplayTemporaryFocusedRemoval
