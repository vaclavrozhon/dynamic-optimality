import Splay.Accounting.WholeSplayTemporaryFinalSpineBends

namespace Splay.Accounting.WholeSplayTemporaryFocusedSpines

open Splay.Rank
open Splay.Tree
open Splay.Tree.BST
open Splay.Lazy.Canonical
open Splay.Accounting.LocalBendGeometry
open Splay.Accounting.WholeSplayTemporaryPriorityReduction
open Splay.Accounting.WholeSplayTemporaryCoreGeometry
open Splay.Accounting.WholeSplayTemporaryCoreClassification
open Splay.Accounting.WholeSplayTemporarySpineGeometry

/-!
Proof-relevant classification of every intermediate tree in a bottom-up
splay around two fixed artificial boundary minima.

The original left and right children of the accessed key are retained in
`SpineBase`.  At any later time, `FocusedSpines` follows the unchanged search
context to the accessed key and records the monotone left and right spines
which rotations have accumulated below it.  The four boundary inequalities
are deliberately stored at the base: they are the canonical witnesses used
to prove every new spine edge heavy.
-/

/--
The fixed children at the first occurrence of the accessed key, together
with the exact membership of both selected external positions in their
closed external intervals.
-/
structure SpineBase {n : ℕ} (key : Fin n)
    (leftBoundary rightBoundary : External n) : Type where
  leftLower : ℕ
  rightUpper : ℕ
  leftTree : BST leftLower key.val
  rightTree : BST (key.val + 1) rightUpper
  left_lower_mem : 2 * leftLower ≤ leftBoundary.val
  left_upper_mem : leftBoundary.val ≤ 2 * key.val
  right_lower_mem : 2 * (key.val + 1) ≤ rightBoundary.val
  right_upper_mem : rightBoundary.val ≤ 2 * rightUpper

/--
A focused key below an arbitrary unchanged search context, whose current
children are proof-relevant monotone extensions of the two fixed base
children.
-/
inductive FocusedSpines {n : ℕ} (snapshot : Snapshot n) (key : Fin n)
    (leftBoundary rightBoundary : External n)
    (base : SpineBase key leftBoundary rightBoundary) :
    {lower upper : ℕ} → BST lower upper → Type
  | atKey {lower upper : ℕ}
      {leftTree : BST lower key.val}
      {rightTree : BST (key.val + 1) upper}
      (leftSpine :
        LeftSpine snapshot base.leftTree leftTree)
      (rightSpine :
        RightSpine snapshot base.rightTree rightTree) :
      FocusedSpines snapshot key leftBoundary rightBoundary base
        (.node leftTree rightTree)
  | leftContext {lower root upper : ℕ}
      {inner : BST lower root}
      (focused :
        FocusedSpines snapshot key leftBoundary rightBoundary base inner)
      (rightTree : BST (root + 1) upper) :
      FocusedSpines snapshot key leftBoundary rightBoundary base
        (.node inner rightTree)
  | rightContext {lower root upper : ℕ}
      (leftTree : BST lower root)
      {inner : BST (root + 1) upper}
      (focused :
        FocusedSpines snapshot key leftBoundary rightBoundary base inner) :
      FocusedSpines snapshot key leftBoundary rightBoundary base
        (.node leftTree inner)

/--
The immutable zipper from the original whole tree to the exact node whose
children are stored in `SpineBase`.  This connects both base subtrees back
to the pre-splay global tree, independently of all later rotations.
-/
inductive BaseFocus {n : ℕ} (key : Fin n)
    (leftBoundary rightBoundary : External n)
    (base : SpineBase key leftBoundary rightBoundary) :
    {lower upper : ℕ} → BST lower upper → Type
  | root :
      BaseFocus key leftBoundary rightBoundary base
        (.node base.leftTree base.rightTree)
  | leftContext {lower root upper : ℕ}
      {inner : BST lower root}
      (focus :
        BaseFocus key leftBoundary rightBoundary base inner)
      (rightTree : BST (root + 1) upper) :
      BaseFocus key leftBoundary rightBoundary base
        (.node inner rightTree)
  | rightContext {lower root upper : ℕ}
      (leftTree : BST lower root)
      {inner : BST (root + 1) upper}
      (focus :
        BaseFocus key leftBoundary rightBoundary base inner) :
      BaseFocus key leftBoundary rightBoundary base
        (.node leftTree inner)

/-- Strong initialization package retaining both the original zipper and the
proof-relevant current-spine classification. -/
structure InitialFocusedSpines {n lower upper : ℕ}
    (snapshot : Snapshot n) (key : Fin n)
    (leftBoundary rightBoundary : External n)
    (tree : BST lower upper) : Type where
  base : SpineBase key leftBoundary rightBoundary
  baseFocus :
    BaseFocus key leftBoundary rightBoundary base tree
  focused :
    FocusedSpines snapshot key leftBoundary rightBoundary base tree

/--
Entering a subtree cannot delete a bend already present when that subtree
has no incoming edge: only the subtree root's incoming turn changes, while
all descendant data is identical.
-/
theorem bendsFrom_none_subset
    {n lower upper : ℕ} (snapshot : Snapshot n)
    (tree : BST lower upper) (upper_le_n : upper ≤ n)
    (incoming : Option TernaryBranch) :
    bendsFrom snapshot tree upper_le_n none ⊆
      bendsFrom snapshot tree upper_le_n incoming := by
  cases tree with
  | empty boundary =>
      simp [bendsFrom]
  | node left right =>
      intro element member
      simp only [bendsFrom, Finset.mem_union] at member ⊢
      rcases member with atRoot | inChildren
      · simp [bendAt, Turns] at atRoot
      · exact Or.inr inChildren

namespace BaseFocus

/-- The fixed base interval is contained in every enclosing focus interval. -/
theorem rightUpper_le_upper
    {n lower upper : ℕ} {key : Fin n}
    {leftBoundary rightBoundary : External n}
    {base : SpineBase key leftBoundary rightBoundary}
    {tree : BST lower upper}
    (focus : BaseFocus key leftBoundary rightBoundary base tree) :
    base.rightUpper ≤ upper := by
  induction focus with
  | root =>
      exact Nat.le_refl _
  | leftContext focus rightTree ih =>
      have rightBounds := rightTree.lower_le_upper
      omega
  | rightContext leftTree focus ih =>
      exact ih

/--
Every original bend internal to the fixed left base occurs in the original
whole tree reached by the zipper.
-/
theorem leftBase_bends_subset
    {n lower upper : ℕ} {snapshot : Snapshot n} {key : Fin n}
    {leftBoundary rightBoundary : External n}
    {base : SpineBase key leftBoundary rightBoundary}
    {tree : BST lower upper}
    (focus : BaseFocus key leftBoundary rightBoundary base tree)
    (upper_le_n : upper ≤ n)
    (incoming : Option TernaryBranch) :
    bendsFrom snapshot base.leftTree
        (Nat.le_of_lt key.isLt) none ⊆
      bendsFrom snapshot tree upper_le_n incoming := by
  induction focus generalizing incoming with
  | root =>
      intro element member
      simp only [bendsFrom, Finset.mem_union]
      exact
        Or.inr
          (Or.inl
            (bendsFrom_none_subset snapshot base.leftTree
              (Nat.le_of_lt key.isLt) _ member))
  | @leftContext childLower pivot childUpper inner focus rightTree ih =>
      have pivot_le_n : pivot ≤ n := by
        have rightBounds := rightTree.lower_le_upper
        omega
      intro element member
      simp only [bendsFrom, Finset.mem_union]
      exact Or.inr (Or.inl (ih pivot_le_n _ member))
  | rightContext leftTree focus ih =>
      intro element member
      simp only [bendsFrom, Finset.mem_union]
      exact Or.inr (Or.inr (ih upper_le_n _ member))

/--
Every original bend internal to the fixed right base occurs in the original
whole tree reached by the zipper.
-/
theorem rightBase_bends_subset
    {n lower upper : ℕ} {snapshot : Snapshot n} {key : Fin n}
    {leftBoundary rightBoundary : External n}
    {base : SpineBase key leftBoundary rightBoundary}
    {tree : BST lower upper}
    (focus : BaseFocus key leftBoundary rightBoundary base tree)
    (upper_le_n : upper ≤ n)
    (incoming : Option TernaryBranch) :
    bendsFrom snapshot base.rightTree
        (focus.rightUpper_le_upper.trans upper_le_n) none ⊆
      bendsFrom snapshot tree upper_le_n incoming := by
  induction focus generalizing incoming with
  | root =>
      intro element member
      simp only [bendsFrom, Finset.mem_union]
      exact
        Or.inr
          (Or.inr
            (bendsFrom_none_subset snapshot base.rightTree
              (rightUpper_le_upper .root |>.trans upper_le_n)
              _ member))
  | @leftContext childLower pivot childUpper inner focus rightTree ih =>
      have pivot_le_n : pivot ≤ n := by
        have rightBounds := rightTree.lower_le_upper
        omega
      intro element member
      simp only [bendsFrom, Finset.mem_union]
      exact Or.inr (Or.inl (ih pivot_le_n _ member))
  | rightContext leftTree focus ih =>
      intro element member
      simp only [bendsFrom, Finset.mem_union]
      exact Or.inr (Or.inr (ih upper_le_n _ member))

/-- Complete-tree form used to rule out original left-base bends as newly
created endpoint identities. -/
theorem leftBase_bends_subset_bends
    {n : ℕ} {snapshot : Snapshot n} {key : Fin n}
    {leftBoundary rightBoundary : External n}
    {base : SpineBase key leftBoundary rightBoundary}
    {before : BST 0 n}
    (focus : BaseFocus key leftBoundary rightBoundary base before) :
    bendsFrom snapshot base.leftTree
        (Nat.le_of_lt key.isLt) none ⊆
      bends snapshot before := by
  simpa only [bends] using
    focus.leftBase_bends_subset (Nat.le_refl n) none

/-- Complete-tree form used to rule out original right-base bends as newly
created endpoint identities. -/
theorem rightBase_bends_subset_bends
    {n : ℕ} {snapshot : Snapshot n} {key : Fin n}
    {leftBoundary rightBoundary : External n}
    {base : SpineBase key leftBoundary rightBoundary}
    {before : BST 0 n}
    (focus : BaseFocus key leftBoundary rightBoundary base before) :
    bendsFrom snapshot base.rightTree
        focus.rightUpper_le_upper none ⊆
      bends snapshot before := by
  simpa only [bends] using
    focus.rightBase_bends_subset (Nat.le_refl n) none

end BaseFocus

namespace RightSpine

/-- A right spine can only extend the upper endpoint of its fixed base. -/
theorem baseUpper_le_upper
    {n key baseUpper upper : ℕ} {snapshot : Snapshot n}
    {base : BST (key + 1) baseUpper}
    {tree : BST (key + 1) upper}
    (spine : RightSpine snapshot base tree) :
    baseUpper ≤ upper := by
  induction spine with
  | base _ =>
      exact Nat.le_refl _
  | grow innerSpine hanging _ _ ih =>
      have hangingBounds := hanging.lower_le_upper
      omega

/--
Proof-relevant evidence that a right spine is an initial construction
prefix of another spine over the same snapshot and fixed base.
-/
inductive IsPrefix
    {n key baseUpper : ℕ} {snapshot : Snapshot n}
    {base : BST (key + 1) baseUpper}
    {oldUpper : ℕ} {oldTree : BST (key + 1) oldUpper}
    (oldSpine : RightSpine snapshot base oldTree) :
    {finalUpper : ℕ} → {finalTree : BST (key + 1) finalUpper} →
      RightSpine snapshot base finalTree → Type
  | refl :
      IsPrefix oldSpine oldSpine
  | grow {root upper : ℕ} {inner : BST (key + 1) root}
      {innerSpine : RightSpine snapshot base inner}
      (prior : IsPrefix oldSpine innerSpine)
      (hanging : BST (root + 1) upper)
      (upper_le_n : upper ≤ n)
      (heavy : _) :
      IsPrefix oldSpine
        (RightSpine.grow innerSpine hanging upper_le_n heavy)

namespace IsPrefix

/-- Prefix evidence composes chronologically. -/
def trans
    {n key baseUpper : ℕ} {snapshot : Snapshot n}
    {base : BST (key + 1) baseUpper}
    {firstUpper secondUpper finalUpper : ℕ}
    {firstTree : BST (key + 1) firstUpper}
    {secondTree : BST (key + 1) secondUpper}
    {finalTree : BST (key + 1) finalUpper}
    {first : RightSpine snapshot base firstTree}
    {second : RightSpine snapshot base secondTree}
    {final : RightSpine snapshot base finalTree}
    (firstPrefix : IsPrefix first second)
    (secondPrefix : IsPrefix second final) :
    IsPrefix first final :=
  match secondPrefix with
  | .refl => firstPrefix
  | .grow prior hanging upper_le_n heavy =>
      .grow (trans firstPrefix prior) hanging upper_le_n heavy

/-- Hanging-subtree bends are monotone under right-spine extension. -/
theorem hangingBends_subset
    {n key baseUpper oldUpper finalUpper : ℕ}
    {snapshot : Snapshot n}
    {base : BST (key + 1) baseUpper}
    {oldTree : BST (key + 1) oldUpper}
    {finalTree : BST (key + 1) finalUpper}
    {oldSpine : RightSpine snapshot base oldTree}
    {finalSpine : RightSpine snapshot base finalTree}
    (extension : IsPrefix oldSpine finalSpine) :
    oldSpine.hangingBends ⊆ finalSpine.hangingBends := by
  induction extension with
  | refl =>
      exact Finset.Subset.rfl
  | grow prior hanging upper_le_n heavy ih =>
      intro element member
      simp only [
        WholeSplayTemporarySpineGeometry.RightSpine.hangingBends,
        Finset.mem_union]
      exact Or.inl (ih member)

/-- A nontrivial right spine always enters its base from the left. -/
theorem incomingAtBase_eq_some_of_ne_none
    {n key baseUpper upper : ℕ} {snapshot : Snapshot n}
    {base : BST (key + 1) baseUpper}
    {tree : BST (key + 1) upper}
    (spine : RightSpine snapshot base tree)
    (nontrivial :
      WholeSplayTemporaryFinalSpineBends.RightSpine.incomingAtBase
        spine ≠ none) :
    WholeSplayTemporaryFinalSpineBends.RightSpine.incomingAtBase
        spine = some .left := by
  cases spine with
  | base bound =>
      simp [WholeSplayTemporaryFinalSpineBends.RightSpine.incomingAtBase]
        at nontrivial
  | grow innerSpine hanging bound heavy =>
      rfl

/--
Once the first right-spine grow has happened, all later extensions preserve
the incoming edge seen by the fixed base.
-/
theorem incomingAtBase_eq_of_ne_none
    {n key baseUpper oldUpper finalUpper : ℕ}
    {snapshot : Snapshot n}
    {base : BST (key + 1) baseUpper}
    {oldTree : BST (key + 1) oldUpper}
    {finalTree : BST (key + 1) finalUpper}
    {oldSpine : RightSpine snapshot base oldTree}
    {finalSpine : RightSpine snapshot base finalTree}
    (extension : IsPrefix oldSpine finalSpine)
    (nontrivial :
      WholeSplayTemporaryFinalSpineBends.RightSpine.incomingAtBase
        oldSpine ≠ none) :
    WholeSplayTemporaryFinalSpineBends.RightSpine.incomingAtBase
        finalSpine =
      WholeSplayTemporaryFinalSpineBends.RightSpine.incomingAtBase
        oldSpine := by
  have oldSome := incomingAtBase_eq_some_of_ne_none oldSpine nontrivial
  have finalSome :
      WholeSplayTemporaryFinalSpineBends.RightSpine.incomingAtBase
          finalSpine = some .left := by
    induction extension with
    | refl =>
        exact oldSome
    | grow prior hanging upper_le_n heavy ih =>
        rfl
  exact finalSome.trans oldSome.symm

end IsPrefix

/--
The fixed right boundary is the canonical minimum of every node newly
adjoined to a right spine, hence its inward-left edge is heavy.
-/
noncomputable def grow_temporarySnapshot
    {n : ℕ} (comparison : BST 0 n) (key : Fin n)
    (comparisonRoot : comparison.HasRoot key.val)
    (leftBoundary rightBoundary : External n)
    (ordered :
      leftBoundary < valuePos key ∧ valuePos key < rightBoundary)
    (base : SpineBase key leftBoundary rightBoundary)
    {root upper : ℕ}
    {inner : BST (key.val + 1) root}
    (innerSpine :
      RightSpine
        (temporarySnapshot comparison key comparisonRoot
          leftBoundary rightBoundary ordered)
        base.rightTree inner)
    (hanging : BST (root + 1) upper)
    (upper_le_n : upper ≤ n) :
    RightSpine
      (temporarySnapshot comparison key comparisonRoot
        leftBoundary rightBoundary ordered)
      base.rightTree (.node inner hanging) := by
  apply RightSpine.grow innerSpine hanging upper_le_n
  let node : AtNode n := {
    lower := key.val + 1
    root := root
    upper := upper
    left := inner
    right := hanging
    upper_le_n := upper_le_n
  }
  change node.heavyBranch
      (temporarySnapshot comparison key comparisonRoot
        leftBoundary rightBoundary ordered) = .left
  apply
    heavyBranch_eq_of_isIntervalMin
      (temporarySnapshot comparison key comparisonRoot
        leftBoundary rightBoundary ordered)
      node rightBoundary .left
  · apply
      right_isIntervalMin comparison key comparisonRoot
        leftBoundary rightBoundary node.wholeLower node.wholeUpper ordered
    · constructor
      · change 2 * (key.val + 1) ≤ rightBoundary.val
        exact base.right_lower_mem
      · change rightBoundary.val ≤ 2 * upper
        have baseToRoot := baseUpper_le_upper innerSpine
        have rootToUpper := hanging.lower_le_upper
        have boundaryAtBase := base.right_upper_mem
        omega
    · change 2 * key.val + 1 < 2 * (key.val + 1)
      omega
  · change rightBoundary.val ≤ 2 * root
    have baseToRoot := baseUpper_le_upper innerSpine
    have boundaryAtBase := base.right_upper_mem
    omega

namespace IsPrefix

/-- The canonical right-spine grow is one proof-relevant prefix extension. -/
noncomputable def of_grow_temporarySnapshot
    {n : ℕ} (comparison : BST 0 n) (key : Fin n)
    (comparisonRoot : comparison.HasRoot key.val)
    (leftBoundary rightBoundary : External n)
    (ordered :
      leftBoundary < valuePos key ∧ valuePos key < rightBoundary)
    (base : SpineBase key leftBoundary rightBoundary)
    {root upper : ℕ}
    {inner : BST (key.val + 1) root}
    (innerSpine :
      RightSpine
        (temporarySnapshot comparison key comparisonRoot
          leftBoundary rightBoundary ordered)
        base.rightTree inner)
    (hanging : BST (root + 1) upper)
    (upper_le_n : upper ≤ n) :
    IsPrefix innerSpine
      (RightSpine.grow_temporarySnapshot comparison key comparisonRoot
        leftBoundary rightBoundary ordered base
        innerSpine hanging upper_le_n) := by
  unfold RightSpine.grow_temporarySnapshot
  apply IsPrefix.grow .refl

end IsPrefix

end RightSpine

namespace LeftSpine

/-- A left spine can only extend the lower endpoint of its fixed base. -/
theorem lower_le_baseLower
    {n key baseLower lower : ℕ} {snapshot : Snapshot n}
    {base : BST baseLower key}
    {tree : BST lower key}
    (spine : LeftSpine snapshot base tree) :
    lower ≤ baseLower := by
  induction spine with
  | base _ =>
      exact Nat.le_refl _
  | grow innerSpine hanging _ _ _ ih =>
      have hangingBounds := hanging.lower_le_upper
      omega

/--
Proof-relevant evidence that a left spine is an initial construction prefix
of another spine over the same snapshot and fixed base.
-/
inductive IsPrefix
    {n key baseLower : ℕ} {snapshot : Snapshot n}
    {base : BST baseLower key}
    {oldLower : ℕ} {oldTree : BST oldLower key}
    (oldSpine : LeftSpine snapshot base oldTree) :
    {finalLower : ℕ} → {finalTree : BST finalLower key} →
      LeftSpine snapshot base finalTree → Type
  | refl :
      IsPrefix oldSpine oldSpine
  | grow {lower root : ℕ} {inner : BST (root + 1) key}
      {innerSpine : LeftSpine snapshot base inner}
      (prior : IsPrefix oldSpine innerSpine)
      (hanging : BST lower root)
      (root_le_n : root ≤ n)
      (key_le_n : key ≤ n)
      (heavy : _) :
      IsPrefix oldSpine
        (LeftSpine.grow innerSpine hanging root_le_n key_le_n heavy)

namespace IsPrefix

/-- Prefix evidence composes chronologically. -/
def trans
    {n key baseLower : ℕ} {snapshot : Snapshot n}
    {base : BST baseLower key}
    {firstLower secondLower finalLower : ℕ}
    {firstTree : BST firstLower key}
    {secondTree : BST secondLower key}
    {finalTree : BST finalLower key}
    {first : LeftSpine snapshot base firstTree}
    {second : LeftSpine snapshot base secondTree}
    {final : LeftSpine snapshot base finalTree}
    (firstPrefix : IsPrefix first second)
    (secondPrefix : IsPrefix second final) :
    IsPrefix first final :=
  match secondPrefix with
  | .refl => firstPrefix
  | .grow prior hanging root_le_n key_le_n heavy =>
      .grow (trans firstPrefix prior)
        hanging root_le_n key_le_n heavy

/-- Hanging-subtree bends are monotone under left-spine extension. -/
theorem hangingBends_subset
    {n key baseLower oldLower finalLower : ℕ}
    {snapshot : Snapshot n}
    {base : BST baseLower key}
    {oldTree : BST oldLower key}
    {finalTree : BST finalLower key}
    {oldSpine : LeftSpine snapshot base oldTree}
    {finalSpine : LeftSpine snapshot base finalTree}
    (extension : IsPrefix oldSpine finalSpine) :
    oldSpine.hangingBends ⊆ finalSpine.hangingBends := by
  induction extension with
  | refl =>
      exact Finset.Subset.rfl
  | grow prior hanging root_le_n key_le_n heavy ih =>
      intro element member
      simp only [
        WholeSplayTemporarySpineGeometry.LeftSpine.hangingBends,
        Finset.mem_union]
      exact Or.inr (ih member)

/-- A nontrivial left spine always enters its base from the right. -/
theorem incomingAtBase_eq_some_of_ne_none
    {n key baseLower lower : ℕ} {snapshot : Snapshot n}
    {base : BST baseLower key}
    {tree : BST lower key}
    (spine : LeftSpine snapshot base tree)
    (nontrivial :
      WholeSplayTemporaryFinalSpineBends.LeftSpine.incomingAtBase
        spine ≠ none) :
    WholeSplayTemporaryFinalSpineBends.LeftSpine.incomingAtBase
        spine = some .right := by
  cases spine with
  | base bound =>
      simp [WholeSplayTemporaryFinalSpineBends.LeftSpine.incomingAtBase]
        at nontrivial
  | grow innerSpine hanging rootBound bound heavy =>
      rfl

/--
Once the first left-spine grow has happened, all later extensions preserve
the incoming edge seen by the fixed base.
-/
theorem incomingAtBase_eq_of_ne_none
    {n key baseLower oldLower finalLower : ℕ}
    {snapshot : Snapshot n}
    {base : BST baseLower key}
    {oldTree : BST oldLower key}
    {finalTree : BST finalLower key}
    {oldSpine : LeftSpine snapshot base oldTree}
    {finalSpine : LeftSpine snapshot base finalTree}
    (extension : IsPrefix oldSpine finalSpine)
    (nontrivial :
      WholeSplayTemporaryFinalSpineBends.LeftSpine.incomingAtBase
        oldSpine ≠ none) :
    WholeSplayTemporaryFinalSpineBends.LeftSpine.incomingAtBase
        finalSpine =
      WholeSplayTemporaryFinalSpineBends.LeftSpine.incomingAtBase
        oldSpine := by
  have oldSome := incomingAtBase_eq_some_of_ne_none oldSpine nontrivial
  have finalSome :
      WholeSplayTemporaryFinalSpineBends.LeftSpine.incomingAtBase
          finalSpine = some .right := by
    induction extension with
    | refl =>
        exact oldSome
    | grow prior hanging root_le_n key_le_n heavy ih =>
        rfl
  exact finalSome.trans oldSome.symm

end IsPrefix

/--
The fixed left boundary is the canonical minimum of every node newly
adjoined to a left spine, hence its inward-right edge is heavy.
-/
noncomputable def grow_temporarySnapshot
    {n : ℕ} (comparison : BST 0 n) (key : Fin n)
    (comparisonRoot : comparison.HasRoot key.val)
    (leftBoundary rightBoundary : External n)
    (ordered :
      leftBoundary < valuePos key ∧ valuePos key < rightBoundary)
    (base : SpineBase key leftBoundary rightBoundary)
    {lower root : ℕ}
    {inner : BST (root + 1) key.val}
    (innerSpine :
      LeftSpine
        (temporarySnapshot comparison key comparisonRoot
          leftBoundary rightBoundary ordered)
        base.leftTree inner)
    (hanging : BST lower root)
    (root_le_n : root ≤ n) :
    LeftSpine
      (temporarySnapshot comparison key comparisonRoot
        leftBoundary rightBoundary ordered)
      base.leftTree (.node hanging inner) := by
  apply
    LeftSpine.grow innerSpine hanging root_le_n
      (Nat.le_of_lt key.isLt)
  let node : AtNode n := {
    lower := lower
    root := root
    upper := key.val
    left := hanging
    right := inner
    upper_le_n := Nat.le_of_lt key.isLt
  }
  change node.heavyBranch
      (temporarySnapshot comparison key comparisonRoot
        leftBoundary rightBoundary ordered) = .right
  apply
    heavyBranch_eq_of_isIntervalMin
      (temporarySnapshot comparison key comparisonRoot
        leftBoundary rightBoundary ordered)
      node leftBoundary .right
  · apply
      left_isIntervalMin comparison key comparisonRoot
        leftBoundary rightBoundary node.wholeLower node.wholeUpper ordered
    · constructor
      · change 2 * lower ≤ leftBoundary.val
        have lowerToRoot := hanging.lower_le_upper
        have innerToBase := lower_le_baseLower innerSpine
        have boundaryAtBase := base.left_lower_mem
        omega
      · change leftBoundary.val ≤ 2 * key.val
        exact base.left_upper_mem
    · change 2 * key.val < 2 * key.val + 1
      omega
  · change 2 * root + 2 ≤ leftBoundary.val
    have innerToBase := lower_le_baseLower innerSpine
    have boundaryAtBase := base.left_lower_mem
    omega

namespace IsPrefix

/-- The canonical left-spine grow is one proof-relevant prefix extension. -/
noncomputable def of_grow_temporarySnapshot
    {n : ℕ} (comparison : BST 0 n) (key : Fin n)
    (comparisonRoot : comparison.HasRoot key.val)
    (leftBoundary rightBoundary : External n)
    (ordered :
      leftBoundary < valuePos key ∧ valuePos key < rightBoundary)
    (base : SpineBase key leftBoundary rightBoundary)
    {lower root : ℕ}
    {inner : BST (root + 1) key.val}
    (innerSpine :
      LeftSpine
        (temporarySnapshot comparison key comparisonRoot
          leftBoundary rightBoundary ordered)
        base.leftTree inner)
    (hanging : BST lower root)
    (root_le_n : root ≤ n) :
    IsPrefix innerSpine
      (LeftSpine.grow_temporarySnapshot comparison key comparisonRoot
        leftBoundary rightBoundary ordered base
        innerSpine hanging root_le_n) := by
  unfold LeftSpine.grow_temporarySnapshot
  apply IsPrefix.grow .refl

end IsPrefix

end LeftSpine

/-- The unique pair of current spine objects stored at the terminal key
constructor of a `FocusedSpines` witness. -/
structure SpinePair {n : ℕ} (snapshot : Snapshot n) (key : Fin n)
    (leftBoundary rightBoundary : External n)
    (base : SpineBase key leftBoundary rightBoundary) : Type where
  leftLower : ℕ
  leftTree : BST leftLower key.val
  leftSpine : LeftSpine snapshot base.leftTree leftTree
  rightUpper : ℕ
  rightTree : BST (key.val + 1) rightUpper
  rightSpine : RightSpine snapshot base.rightTree rightTree

namespace FocusedSpines

/-- Extract the terminal pair of spines, ignoring the enclosing search
context. -/
def spinePair
    {n lower upper : ℕ} {snapshot : Snapshot n} {key : Fin n}
    {leftBoundary rightBoundary : External n}
    {base : SpineBase key leftBoundary rightBoundary}
    {tree : BST lower upper}
    (focused :
      FocusedSpines snapshot key leftBoundary rightBoundary base tree) :
    SpinePair snapshot key leftBoundary rightBoundary base :=
  match focused with
  | .atKey leftSpine rightSpine =>
      ⟨_, _, leftSpine, _, _, rightSpine⟩
  | .leftContext innerFocused _ =>
      spinePair innerFocused
  | .rightContext _ innerFocused =>
      spinePair innerFocused

/-- Both terminal spines of the second focused witness extend those of the
first witness. -/
structure IsPrefix
    {n firstLower firstUpper finalLower finalUpper : ℕ}
    {snapshot : Snapshot n} {key : Fin n}
    {leftBoundary rightBoundary : External n}
    {base : SpineBase key leftBoundary rightBoundary}
    {firstTree : BST firstLower firstUpper}
    {finalTree : BST finalLower finalUpper}
    (first :
      FocusedSpines snapshot key leftBoundary rightBoundary base firstTree)
    (final :
      FocusedSpines snapshot key leftBoundary rightBoundary base finalTree) :
    Type where
  left :
    LeftSpine.IsPrefix
      (spinePair first).leftSpine (spinePair final).leftSpine
  right :
    RightSpine.IsPrefix
      (spinePair first).rightSpine (spinePair final).rightSpine

namespace IsPrefix

/-- Every focused witness is a prefix of itself. -/
def refl
    {n lower upper : ℕ} {snapshot : Snapshot n} {key : Fin n}
    {leftBoundary rightBoundary : External n}
    {base : SpineBase key leftBoundary rightBoundary}
    {tree : BST lower upper}
    (focused :
      FocusedSpines snapshot key leftBoundary rightBoundary base tree) :
    IsPrefix focused focused :=
  ⟨.refl, .refl⟩

/-- Focused prefix evidence composes componentwise. -/
def trans
    {n firstLower firstUpper secondLower secondUpper
      finalLower finalUpper : ℕ}
    {snapshot : Snapshot n} {key : Fin n}
    {leftBoundary rightBoundary : External n}
    {base : SpineBase key leftBoundary rightBoundary}
    {firstTree : BST firstLower firstUpper}
    {secondTree : BST secondLower secondUpper}
    {finalTree : BST finalLower finalUpper}
    {first :
      FocusedSpines snapshot key leftBoundary rightBoundary base firstTree}
    {second :
      FocusedSpines snapshot key leftBoundary rightBoundary base secondTree}
    {final :
      FocusedSpines snapshot key leftBoundary rightBoundary base finalTree}
    (firstPrefix : IsPrefix first second)
    (secondPrefix : IsPrefix second final) :
    IsPrefix first final :=
  ⟨LeftSpine.IsPrefix.trans firstPrefix.left secondPrefix.left,
    RightSpine.IsPrefix.trans firstPrefix.right secondPrefix.right⟩

/-- Left hanging bends persist between the extracted terminal pairs. -/
theorem left_hangingBends_subset
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
    (extension : IsPrefix first final) :
    (spinePair first).leftSpine.hangingBends ⊆
      (spinePair final).leftSpine.hangingBends :=
  LeftSpine.IsPrefix.hangingBends_subset extension.left

/-- Right hanging bends persist between the extracted terminal pairs. -/
theorem right_hangingBends_subset
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
    (extension : IsPrefix first final) :
    (spinePair first).rightSpine.hangingBends ⊆
      (spinePair final).rightSpine.hangingBends :=
  RightSpine.IsPrefix.hangingBends_subset extension.right

/-- The left base incoming edge stays fixed throughout a nontrivial suffix. -/
theorem left_incomingAtBase_eq_of_ne_none
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
    (extension : IsPrefix first final)
    (nontrivial :
      WholeSplayTemporaryFinalSpineBends.LeftSpine.incomingAtBase
        (spinePair first).leftSpine ≠ none) :
    WholeSplayTemporaryFinalSpineBends.LeftSpine.incomingAtBase
        (spinePair final).leftSpine =
      WholeSplayTemporaryFinalSpineBends.LeftSpine.incomingAtBase
        (spinePair first).leftSpine :=
  LeftSpine.IsPrefix.incomingAtBase_eq_of_ne_none
    extension.left nontrivial

/-- The right base incoming edge stays fixed throughout a nontrivial suffix. -/
theorem right_incomingAtBase_eq_of_ne_none
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
    (extension : IsPrefix first final)
    (nontrivial :
      WholeSplayTemporaryFinalSpineBends.RightSpine.incomingAtBase
        (spinePair first).rightSpine ≠ none) :
    WholeSplayTemporaryFinalSpineBends.RightSpine.incomingAtBase
        (spinePair final).rightSpine =
      WholeSplayTemporaryFinalSpineBends.RightSpine.incomingAtBase
        (spinePair first).rightSpine :=
  RightSpine.IsPrefix.incomingAtBase_eq_of_ne_none
    extension.right nontrivial

end IsPrefix

/-- A final focused witness packaged with componentwise prefix evidence from
one fixed earlier witness. -/
structure PrefixResult
    {n firstLower firstUpper finalLower finalUpper : ℕ}
    {snapshot : Snapshot n} {key : Fin n}
    {leftBoundary rightBoundary : External n}
    {base : SpineBase key leftBoundary rightBoundary}
    {firstTree : BST firstLower firstUpper}
    (first :
      FocusedSpines snapshot key leftBoundary rightBoundary base firstTree)
    (finalTree : BST finalLower finalUpper) : Type where
  focused :
    FocusedSpines snapshot key leftBoundary rightBoundary base finalTree
  isPrefix : IsPrefix first focused

/-- The focused key belongs to the interval of every classified tree. -/
theorem key_bounds
    {n lower upper : ℕ} {snapshot : Snapshot n} {key : Fin n}
    {leftBoundary rightBoundary : External n}
    {base : SpineBase key leftBoundary rightBoundary}
    {tree : BST lower upper}
    (focused :
      FocusedSpines snapshot key leftBoundary rightBoundary base tree) :
    lower ≤ key.val ∧ key.val < upper := by
  induction focused with
  | atKey leftSpine rightSpine =>
      have leftBounds := LeftSpine.lower_le_baseLower leftSpine
      have originalLeftBounds := base.leftTree.lower_le_upper
      have rightBounds := rightSpine.upper_le_n
      have currentRightBounds :=
        RightSpine.baseUpper_le_upper rightSpine
      have originalRightBounds := base.rightTree.lower_le_upper
      omega
  | leftContext focused rightTree ih =>
      have rightBounds := rightTree.lower_le_upper
      omega
  | rightContext leftTree focused ih =>
      have leftBounds := leftTree.lower_le_upper
      omega

/--
Strong initialization from exact boundary placement.  Besides the trivial
two spines it retains a proof-relevant zipper from the original whole tree
to their fixed base children.
-/
theorem nonempty_initial_ofBoundaryPlacement
    {n lower upper : ℕ} (snapshot : Snapshot n) (key : Fin n)
    (leftBoundary rightBoundary : External n)
    {tree : BST lower upper}
    (placement :
      BoundaryPlacementAt key leftBoundary rightBoundary tree)
    (upper_le_n : upper ≤ n) :
    Nonempty
      (InitialFocusedSpines snapshot key
        leftBoundary rightBoundary tree) := by
  induction placement with
  | root leftTree rightTree leftLower leftUpper
      rightLower rightUpper =>
      let base : SpineBase key leftBoundary rightBoundary :=
        ⟨_, _, leftTree, rightTree, leftLower, leftUpper,
          rightLower, rightUpper⟩
      exact
        ⟨{
          base := base
          baseFocus := .root
          focused :=
            .atKey
              (.base (Nat.le_of_lt key.isLt))
              (.base upper_le_n)
        }⟩
  | @leftContext childLower pivot childUpper leftTree
      placement rightTree ih =>
      have pivot_le_n : pivot ≤ n := by
        have rightBounds := rightTree.lower_le_upper
        omega
      obtain ⟨initial⟩ := ih pivot_le_n
      exact
        ⟨{
          base := initial.base
          baseFocus := .leftContext initial.baseFocus rightTree
          focused := .leftContext initial.focused rightTree
        }⟩
  | rightContext leftTree placement ih =>
      obtain ⟨initial⟩ := ih upper_le_n
      exact
        ⟨{
          base := initial.base
          baseFocus := .rightContext leftTree initial.baseFocus
          focused := .rightContext leftTree initial.focused
        }⟩

/-- Chosen proof-relevant strong initialization package. -/
noncomputable def initialOfBoundaryPlacement
    {n lower upper : ℕ} (snapshot : Snapshot n) (key : Fin n)
    (leftBoundary rightBoundary : External n)
    {tree : BST lower upper}
    (placement :
      BoundaryPlacementAt key leftBoundary rightBoundary tree)
    (upper_le_n : upper ≤ n) :
    InitialFocusedSpines snapshot key leftBoundary rightBoundary tree :=
  Classical.choice
    (nonempty_initial_ofBoundaryPlacement snapshot key
      leftBoundary rightBoundary placement upper_le_n)

/--
Boundary placement initializes one fixed pair of base children and trivial
left/right spines, under the unchanged search context.  `Nonempty` is the
correct eliminator because `BoundaryPlacementAt` is a proposition whereas
the resulting classification intentionally lives in `Type`.
-/
theorem nonempty_ofBoundaryPlacement
    {n lower upper : ℕ} (snapshot : Snapshot n) (key : Fin n)
    (leftBoundary rightBoundary : External n)
    {tree : BST lower upper}
    (placement :
      BoundaryPlacementAt key leftBoundary rightBoundary tree)
    (upper_le_n : upper ≤ n) :
    Nonempty
      (Σ base : SpineBase key leftBoundary rightBoundary,
        FocusedSpines snapshot key leftBoundary rightBoundary base tree) := by
  induction placement with
  | root leftTree rightTree leftLower leftUpper
      rightLower rightUpper =>
      let base : SpineBase key leftBoundary rightBoundary :=
        ⟨_, _, leftTree, rightTree, leftLower, leftUpper,
          rightLower, rightUpper⟩
      exact
        ⟨⟨base,
          .atKey
            (.base (Nat.le_of_lt key.isLt))
            (.base upper_le_n)⟩⟩
  | @leftContext childLower pivot childUpper leftTree
      placement rightTree ih =>
      have pivot_le_n : pivot ≤ n := by
        have rightBounds := rightTree.lower_le_upper
        omega
      obtain ⟨⟨base, focused⟩⟩ := ih pivot_le_n
      exact ⟨⟨base, .leftContext focused rightTree⟩⟩
  | rightContext leftTree placement ih =>
      obtain ⟨⟨base, focused⟩⟩ := ih upper_le_n
      exact ⟨⟨base, .rightContext leftTree focused⟩⟩

/-- A noncomputable proof-relevant initialization chosen from the theorem. -/
noncomputable def ofBoundaryPlacement
    {n lower upper : ℕ} (snapshot : Snapshot n) (key : Fin n)
    (leftBoundary rightBoundary : External n)
    {tree : BST lower upper}
    (placement :
      BoundaryPlacementAt key leftBoundary rightBoundary tree)
    (upper_le_n : upper ≤ n) :
    Σ base : SpineBase key leftBoundary rightBoundary,
      FocusedSpines snapshot key leftBoundary rightBoundary base tree :=
  Classical.choice
    (nonempty_ofBoundaryPlacement snapshot key leftBoundary rightBoundary
      placement upper_le_n)

/--
A final root zig preserves the focused-spine classification.  Its only
geometric effect is to adjoin the demoted root and its hanging subtree to
the appropriate monotone spine.
-/
theorem nonempty_after_zig_withPrefix
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
    Nonempty (PrefixResult focused after) := by
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

/-- Classification-only projection of `nonempty_after_zig_withPrefix`. -/
theorem nonempty_after_zig
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
    Nonempty
      (FocusedSpines
        (temporarySnapshot comparison key comparisonRoot
          leftBoundary rightBoundary ordered)
        key leftBoundary rightBoundary base after) := by
  obtain ⟨result⟩ :=
    nonempty_after_zig_withPrefix comparison key comparisonRoot
      leftBoundary rightBoundary ordered base focused step upper_le_n
  exact ⟨result.focused⟩

/-- Proof-relevant choice form of `nonempty_after_zig`. -/
noncomputable def after_zig
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
    FocusedSpines
      (temporarySnapshot comparison key comparisonRoot
        leftBoundary rightBoundary ordered)
      key leftBoundary rightBoundary base after :=
  Classical.choice
    (nonempty_after_zig comparison key comparisonRoot
      leftBoundary rightBoundary ordered base focused step upper_le_n)

/--
A root double rotation preserves the same two fixed bases.  Zig-zig adds
one whole hanging subtree to one spine; zig-zag adds one hanging subtree to
each spine.
-/
theorem nonempty_after_doubleRotation_withPrefix
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
    Nonempty (PrefixResult focused after) := by
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

/-- Classification-only projection of
`nonempty_after_doubleRotation_withPrefix`. -/
theorem nonempty_after_doubleRotation
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
    Nonempty
      (FocusedSpines
        (temporarySnapshot comparison key comparisonRoot
          leftBoundary rightBoundary ordered)
        key leftBoundary rightBoundary base after) := by
  obtain ⟨result⟩ :=
    nonempty_after_doubleRotation_withPrefix
      comparison key comparisonRoot leftBoundary rightBoundary
      ordered base focused step upper_le_n
  exact ⟨result.focused⟩

/-- Proof-relevant choice form of `nonempty_after_doubleRotation`. -/
noncomputable def after_doubleRotation
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
    FocusedSpines
      (temporarySnapshot comparison key comparisonRoot
        leftBoundary rightBoundary ordered)
      key leftBoundary rightBoundary base after :=
  Classical.choice
    (nonempty_after_doubleRotation comparison key comparisonRoot
      leftBoundary rightBoundary ordered base focused step upper_le_n)

/--
Preservation under a double rotation at arbitrary contextual depth.  The
surrounding constructors are copied verbatim and the root theorem is used
exactly at the rotated subtree.
-/
private theorem nonempty_after_doubleRotationAt_withPrefix_of_eq
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
    Nonempty (PrefixResult focused after) := by
  induction step generalizing key with
  | root rootStep =>
      rw [← key_eq] at rootStep
      exact
        nonempty_after_doubleRotation_withPrefix
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
              isPrefix :=
                ⟨result.isPrefix.left, result.isPrefix.right⟩
            }⟩

/--
Public specialization of contextual preservation to the accessed finite key.
-/
theorem nonempty_after_doubleRotationAt_withPrefix
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
    Nonempty (PrefixResult focused after) :=
  nonempty_after_doubleRotationAt_withPrefix_of_eq
    comparison key comparisonRoot leftBoundary rightBoundary
    ordered base focused step rfl upper_le_n

/-- Classification-only projection of
`nonempty_after_doubleRotationAt_withPrefix`. -/
theorem nonempty_after_doubleRotationAt
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
    Nonempty
      (FocusedSpines
        (temporarySnapshot comparison key comparisonRoot
          leftBoundary rightBoundary ordered)
        key leftBoundary rightBoundary base after) := by
  obtain ⟨result⟩ :=
    nonempty_after_doubleRotationAt_withPrefix
      comparison key comparisonRoot leftBoundary rightBoundary
      ordered base focused step upper_le_n
  exact ⟨result.focused⟩

/-- Proof-relevant choice form of `nonempty_after_doubleRotationAt`. -/
noncomputable def after_doubleRotationAt
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
    FocusedSpines
      (temporarySnapshot comparison key comparisonRoot
        leftBoundary rightBoundary ordered)
      key leftBoundary rightBoundary base after :=
  Classical.choice
    (nonempty_after_doubleRotationAt comparison key comparisonRoot
      leftBoundary rightBoundary ordered base focused step upper_le_n)

/-- One bottom-up splay step preserves both fixed spines as construction
prefixes of the resulting pair. -/
theorem nonempty_after_splayStep_withPrefix
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
    Nonempty (PrefixResult focused after) := by
  cases step with
  | zig zigStep =>
      exact
        nonempty_after_zig_withPrefix comparison key comparisonRoot
          leftBoundary rightBoundary ordered base focused zigStep upper_le_n
  | double doubleStep =>
      exact
        nonempty_after_doubleRotationAt_withPrefix
          comparison key comparisonRoot
          leftBoundary rightBoundary ordered base focused doubleStep upper_le_n

/-- Classification-only projection of
`nonempty_after_splayStep_withPrefix`. -/
theorem nonempty_after_splayStep
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
    Nonempty
      (FocusedSpines
        (temporarySnapshot comparison key comparisonRoot
          leftBoundary rightBoundary ordered)
        key leftBoundary rightBoundary base after) := by
  obtain ⟨result⟩ :=
    nonempty_after_splayStep_withPrefix
      comparison key comparisonRoot leftBoundary rightBoundary
      ordered base focused step upper_le_n
  exact ⟨result.focused⟩

/-- Proof-relevant choice form of `nonempty_after_splayStep`. -/
noncomputable def after_splayStep
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
    FocusedSpines
      (temporarySnapshot comparison key comparisonRoot
        leftBoundary rightBoundary ordered)
      key leftBoundary rightBoundary base after :=
  Classical.choice
    (nonempty_after_splayStep comparison key comparisonRoot
      leftBoundary rightBoundary ordered base focused step upper_le_n)

/-- Internal generalized-key form used to recurse through a propositional
execution while retaining a proof-relevant classification. -/
private theorem nonempty_after_execution_withPrefix_of_eq
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
    Nonempty (PrefixResult focused after) := by
  induction execution generalizing key with
  | done root =>
      exact
        ⟨{
          focused := focused
          isPrefix := IsPrefix.refl focused
        }⟩
  | next head tail ih =>
      rw [← key_eq] at head
      obtain ⟨headResult⟩ :=
        nonempty_after_splayStep_withPrefix
          comparison key comparisonRoot
          leftBoundary rightBoundary ordered base focused head upper_le_n
      obtain ⟨tailResult⟩ :=
        ih key comparisonRoot ordered base headResult.focused key_eq
      exact
        ⟨{
          focused := tailResult.focused
          isPrefix :=
            IsPrefix.trans headResult.isPrefix tailResult.isPrefix
        }⟩

/-- Every complete bottom-up splay execution preserves the fixed bases and
their two proof-relevant monotone spines. -/
theorem nonempty_after_execution_withPrefix
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
    Nonempty (PrefixResult focused after) :=
  nonempty_after_execution_withPrefix_of_eq
    comparison key comparisonRoot leftBoundary rightBoundary
    ordered base focused execution rfl upper_le_n

/-- Classification-only projection of
`nonempty_after_execution_withPrefix`. -/
theorem nonempty_after_execution
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
    Nonempty
      (FocusedSpines
        (temporarySnapshot comparison key comparisonRoot
          leftBoundary rightBoundary ordered)
        key leftBoundary rightBoundary base after) := by
  obtain ⟨result⟩ :=
    nonempty_after_execution_withPrefix
      comparison key comparisonRoot leftBoundary rightBoundary
      ordered base focused execution upper_le_n
  exact ⟨result.focused⟩

/-- Chosen proof-relevant execution result carrying both spine prefixes. -/
noncomputable def after_execution_withPrefix
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
    PrefixResult focused after :=
  Classical.choice
    (nonempty_after_execution_withPrefix
      comparison key comparisonRoot leftBoundary rightBoundary
      ordered base focused execution upper_le_n)

/-- Proof-relevant choice form of `nonempty_after_execution`. -/
noncomputable def after_execution
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
    FocusedSpines
      (temporarySnapshot comparison key comparisonRoot
        leftBoundary rightBoundary ordered)
      key leftBoundary rightBoundary base after :=
  Classical.choice
    (nonempty_after_execution comparison key comparisonRoot
      leftBoundary rightBoundary ordered base focused execution upper_le_n)

end FocusedSpines

/--
Terminal form of the classification: the accessed key is now the global
root and its two children are monotone extensions of the fixed base
children.
-/
inductive FinalTwoSpines {n : ℕ} (snapshot : Snapshot n) (key : Fin n)
    (leftBoundary rightBoundary : External n)
    (base : SpineBase key leftBoundary rightBoundary) :
    BST 0 n → Type
  | atRoot {leftTree : BST 0 key.val}
      {rightTree : BST (key.val + 1) n}
      (leftSpine :
        LeftSpine snapshot base.leftTree leftTree)
      (rightSpine :
        RightSpine snapshot base.rightTree rightTree) :
      FinalTwoSpines snapshot key leftBoundary rightBoundary base
        (.node leftTree rightTree)

/--
End-to-end witness retaining the immutable pre-splay base zipper together
with the final two-spine decomposition.
-/
structure ExecutionTwoSpines {n : ℕ} (snapshot : Snapshot n)
    (key : Fin n) (leftBoundary rightBoundary : External n)
    (before after : BST 0 n) : Type where
  base : SpineBase key leftBoundary rightBoundary
  baseFocus :
    BaseFocus key leftBoundary rightBoundary base before
  finalSpines :
    FinalTwoSpines snapshot key leftBoundary rightBoundary base after

namespace FocusedSpines

/--
`HasRoot` eliminates every remaining contextual constructor, leaving
exactly the two proof-relevant spines below the accessed root.
-/
theorem nonempty_toFinalTwoSpines
    {n : ℕ} {snapshot : Snapshot n} {key : Fin n}
    {leftBoundary rightBoundary : External n}
    {base : SpineBase key leftBoundary rightBoundary}
    {tree : BST 0 n}
    (focused :
      FocusedSpines snapshot key leftBoundary rightBoundary base tree)
    (hasRoot : tree.HasRoot key.val) :
    Nonempty
      (FinalTwoSpines snapshot key
        leftBoundary rightBoundary base tree) := by
  obtain ⟨leftTree, rightTree, rfl⟩ := hasRoot
  cases focused with
  | atKey leftSpine rightSpine =>
      exact ⟨.atRoot leftSpine rightSpine⟩
  | leftContext innerFocused contextRight =>
      have bounds := key_bounds innerFocused
      omega
  | rightContext contextLeft innerFocused =>
      have bounds := key_bounds innerFocused
      omega

/-- Proof-relevant choice form of `nonempty_toFinalTwoSpines`. -/
noncomputable def toFinalTwoSpines
    {n : ℕ} {snapshot : Snapshot n} {key : Fin n}
    {leftBoundary rightBoundary : External n}
    {base : SpineBase key leftBoundary rightBoundary}
    {tree : BST 0 n}
    (focused :
      FocusedSpines snapshot key leftBoundary rightBoundary base tree)
    (hasRoot : tree.HasRoot key.val) :
    FinalTwoSpines snapshot key leftBoundary rightBoundary base tree :=
  Classical.choice (nonempty_toFinalTwoSpines focused hasRoot)

/--
Complete-execution terminal theorem.  Preservation supplies the final
focused object and `SplayExecution.hasRoot_after` removes its context.
-/
theorem nonempty_finalTwoSpines_after_execution
    {n : ℕ} (comparison : BST 0 n) (key : Fin n)
    (comparisonRoot : comparison.HasRoot key.val)
    (leftBoundary rightBoundary : External n)
    (ordered :
      leftBoundary < valuePos key ∧ valuePos key < rightBoundary)
    (base : SpineBase key leftBoundary rightBoundary)
    {before after : BST 0 n}
    (focused :
      FocusedSpines
        (temporarySnapshot comparison key comparisonRoot
          leftBoundary rightBoundary ordered)
        key leftBoundary rightBoundary base before)
    (execution : SplayExecution key.val before after) :
    Nonempty
      (FinalTwoSpines
        (temporarySnapshot comparison key comparisonRoot
          leftBoundary rightBoundary ordered)
        key leftBoundary rightBoundary base after) := by
  obtain ⟨finalFocused⟩ :=
    nonempty_after_execution comparison key comparisonRoot
      leftBoundary rightBoundary ordered base focused execution
      (Nat.le_refl n)
  exact
    nonempty_toFinalTwoSpines finalFocused execution.hasRoot_after

/-- Proof-relevant choice form of
`nonempty_finalTwoSpines_after_execution`. -/
noncomputable def finalTwoSpinesAfterExecution
    {n : ℕ} (comparison : BST 0 n) (key : Fin n)
    (comparisonRoot : comparison.HasRoot key.val)
    (leftBoundary rightBoundary : External n)
    (ordered :
      leftBoundary < valuePos key ∧ valuePos key < rightBoundary)
    (base : SpineBase key leftBoundary rightBoundary)
    {before after : BST 0 n}
    (focused :
      FocusedSpines
        (temporarySnapshot comparison key comparisonRoot
          leftBoundary rightBoundary ordered)
        key leftBoundary rightBoundary base before)
    (execution : SplayExecution key.val before after) :
    FinalTwoSpines
      (temporarySnapshot comparison key comparisonRoot
        leftBoundary rightBoundary ordered)
      key leftBoundary rightBoundary base after :=
  Classical.choice
    (nonempty_finalTwoSpines_after_execution comparison key comparisonRoot
      leftBoundary rightBoundary ordered base focused execution)

/--
Canonical end-to-end specialization.  Exact boundary placement creates the
base and its original zipper; execution preservation and the root
postcondition produce the final two spines over that same base.
-/
theorem nonempty_executionTwoSpines_ofBoundaryPlacement
    {n : ℕ} (comparison : BST 0 n) (key : Fin n)
    (comparisonRoot : comparison.HasRoot key.val)
    (leftBoundary rightBoundary : External n)
    {before after : BST 0 n}
    (placement :
      BoundaryPlacementAt key leftBoundary rightBoundary before)
    (execution : SplayExecution key.val before after) :
    Nonempty
      (ExecutionTwoSpines
        (temporarySnapshot comparison key comparisonRoot
          leftBoundary rightBoundary placement.ordered)
        key leftBoundary rightBoundary before after) := by
  obtain ⟨initial⟩ :=
    nonempty_initial_ofBoundaryPlacement
      (temporarySnapshot comparison key comparisonRoot
        leftBoundary rightBoundary placement.ordered)
      key leftBoundary rightBoundary placement (Nat.le_refl n)
  obtain ⟨finalSpines⟩ :=
    nonempty_finalTwoSpines_after_execution
      comparison key comparisonRoot leftBoundary rightBoundary
      placement.ordered initial.base initial.focused execution
  exact
    ⟨{
      base := initial.base
      baseFocus := initial.baseFocus
      finalSpines := finalSpines
    }⟩

/-- Chosen proof-relevant canonical end-to-end witness. -/
noncomputable def executionTwoSpinesOfBoundaryPlacement
    {n : ℕ} (comparison : BST 0 n) (key : Fin n)
    (comparisonRoot : comparison.HasRoot key.val)
    (leftBoundary rightBoundary : External n)
    {before after : BST 0 n}
    (placement :
      BoundaryPlacementAt key leftBoundary rightBoundary before)
    (execution : SplayExecution key.val before after) :
    ExecutionTwoSpines
      (temporarySnapshot comparison key comparisonRoot
        leftBoundary rightBoundary placement.ordered)
      key leftBoundary rightBoundary before after :=
  Classical.choice
    (nonempty_executionTwoSpines_ofBoundaryPlacement
      comparison key comparisonRoot leftBoundary rightBoundary
      placement execution)

end FocusedSpines

end Splay.Accounting.WholeSplayTemporaryFocusedSpines
