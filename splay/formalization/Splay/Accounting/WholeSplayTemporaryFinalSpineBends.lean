import Splay.Accounting.WholeSplayTemporarySpineGeometry

namespace Splay.Accounting.WholeSplayTemporaryFinalSpineBends

open Splay.Rank
open Splay.Tree.BST
open Splay.Lazy.Canonical
open Splay.Accounting.LocalBendGeometry
open Splay.Accounting.ContextualBendGeometry
open Splay.Accounting.WholeSplayTemporaryPriorityReduction
open Splay.Accounting.WholeSplayTemporaryCoreClassification
open Splay.Accounting.WholeSplayTemporarySpineGeometry

/-!
Exact bend-set decompositions for the two monotone spines below the
promoted key.

Each spine consists of:

* the fixed child subtree from the accessed node, possibly entered by one
  new heavy edge; and
* hanging subtrees which are still entered with no heavy edge.

The first component is the source of the one optional administrative
attachment on that side.  The hanging components are the only remaining
place where a genuine zig-zig winner can occur.
-/

namespace RightSpine

/--
Incoming edge seen by the original right child after the right spine has
been assembled.
-/
def incomingAtBase
    {n key baseUpper upper : ℕ} {snapshot : Snapshot n}
    {base : BST (key + 1) baseUpper}
    {tree : BST (key + 1) upper}
    (spine : RightSpine snapshot base tree) :
    Option TernaryBranch :=
  match spine with
  | .base _ => none
  | .grow _ _ _ _ => some .left

/--
The bend set of a complete right spine is exactly its fixed base under the
final incoming edge, together with the unchanged hanging-subtree bend sets.
-/
theorem bendsFrom_none_eq
    {n key baseUpper upper : ℕ} {snapshot : Snapshot n}
    {base : BST (key + 1) baseUpper}
    {tree : BST (key + 1) upper}
    (spine : RightSpine snapshot base tree) :
    bendsFrom snapshot tree spine.upper_le_n none =
      bendsFrom snapshot base spine.base_le_n
          (incomingAtBase spine) ∪
        spine.hangingBends := by
  cases spine with
  | base bound =>
      simp [incomingAtBase,
        WholeSplayTemporarySpineGeometry.RightSpine.hangingBends]
  | @grow root upper inner innerSpine hanging bound heavy =>
      simp only [incomingAtBase,
        WholeSplayTemporarySpineGeometry.RightSpine.hangingBends]
      exact
        WholeSplayTemporarySpineGeometry.RightSpine.bendsFrom_none_grow
          innerSpine hanging bound heavy

/--
After deleting the fixed base and hanging components, at most the right
administrative attachment remains.
-/
theorem created_over_base_and_hanging_le_one
    {n key baseUpper upper : ℕ} {snapshot : Snapshot n}
    {base : BST (key + 1) baseUpper}
    {tree : BST (key + 1) upper}
    (spine : RightSpine snapshot base tree) :
    ((bendsFrom snapshot tree spine.upper_le_n none) \
      (bendsFrom snapshot base spine.base_le_n none ∪
        spine.hangingBends)).card ≤ 1 := by
  rw [bendsFrom_none_eq]
  exact
    (card_sdiff_union_same_le
      (bendsFrom snapshot base spine.base_le_n
        (incomingAtBase spine))
      (bendsFrom snapshot base spine.base_le_n none)
      spine.hangingBends).trans
      (bendsFrom_sdiff_le_one snapshot base spine.base_le_n _ _)

end RightSpine

namespace LeftSpine

/--
Incoming edge seen by the original left child after the left spine has been
assembled.
-/
def incomingAtBase
    {n key baseLower lower : ℕ} {snapshot : Snapshot n}
    {base : BST baseLower key}
    {tree : BST lower key}
    (spine : LeftSpine snapshot base tree) :
    Option TernaryBranch :=
  match spine with
  | .base _ => none
  | .grow _ _ _ _ _ => some .right

/--
The bend set of a complete left spine is exactly its fixed base under the
final incoming edge, together with the unchanged hanging-subtree bend sets.
-/
theorem bendsFrom_none_eq
    {n key baseLower lower : ℕ} {snapshot : Snapshot n}
    {base : BST baseLower key}
    {tree : BST lower key}
    (spine : LeftSpine snapshot base tree) :
    bendsFrom snapshot tree spine.upper_le_n none =
      bendsFrom snapshot base spine.base_le_n
          (incomingAtBase spine) ∪
        spine.hangingBends := by
  cases spine with
  | base bound =>
      simp [incomingAtBase,
        WholeSplayTemporarySpineGeometry.LeftSpine.hangingBends]
  | @grow lower root inner innerSpine hanging rootBound bound heavy =>
      simp only [incomingAtBase,
        WholeSplayTemporarySpineGeometry.LeftSpine.hangingBends]
      exact
        WholeSplayTemporarySpineGeometry.LeftSpine.bendsFrom_none_grow
          innerSpine hanging rootBound bound heavy

/--
After deleting the fixed base and hanging components, at most the left
administrative attachment remains.
-/
theorem created_over_base_and_hanging_le_one
    {n key baseLower lower : ℕ} {snapshot : Snapshot n}
    {base : BST baseLower key}
    {tree : BST lower key}
    (spine : LeftSpine snapshot base tree) :
    ((bendsFrom snapshot tree spine.upper_le_n none) \
      (bendsFrom snapshot base spine.base_le_n none ∪
        spine.hangingBends)).card ≤ 1 := by
  rw [bendsFrom_none_eq]
  exact
    (card_sdiff_union_same_le
      (bendsFrom snapshot base spine.base_le_n
        (incomingAtBase spine))
      (bendsFrom snapshot base spine.base_le_n none)
      spine.hangingBends).trans
      (bendsFrom_sdiff_le_one snapshot base spine.base_le_n _ _)

end LeftSpine

/--
Exact four-component decomposition at a final promoted root whose heavy
branch is the middle external position.
-/
theorem finalRoot_bendsFrom_eq
    {n key baseLower baseUpper lower upper : ℕ}
    {snapshot : Snapshot n}
    {leftBase : BST baseLower key}
    {rightBase : BST (key + 1) baseUpper}
    {left : BST lower key}
    {right : BST (key + 1) upper}
    (leftSpine : LeftSpine snapshot leftBase left)
    (rightSpine : RightSpine snapshot rightBase right)
    (heavy :
      (({
        lower := lower
        root := key
        upper := upper
        left := left
        right := right
        upper_le_n := rightSpine.upper_le_n
      } : AtNode n).heavyBranch snapshot) = .middle) :
    bendsFrom snapshot (.node left right)
        rightSpine.upper_le_n none =
      (bendsFrom snapshot leftBase leftSpine.base_le_n
          (LeftSpine.incomingAtBase leftSpine) ∪
        leftSpine.hangingBends) ∪
      (bendsFrom snapshot rightBase rightSpine.base_le_n
          (RightSpine.incomingAtBase rightSpine) ∪
        rightSpine.hangingBends) := by
  simp only [bendsFrom, heavy]
  simp only [childIncoming, bendAt, Turns]
  simp
  rw [LeftSpine.bendsFrom_none_eq leftSpine,
    RightSpine.bendsFrom_none_eq rightSpine]
  ac_rfl

/--
The interval owner of the promoted key supplies the middle-heavy premise of
`finalRoot_bendsFrom_eq` automatically.
-/
theorem finalRoot_bendsFrom_eq_of_owner
    {n baseLower baseUpper lower upper : ℕ}
    {snapshot : Snapshot n}
    {key : Fin n}
    {leftBase : BST baseLower key.val}
    {rightBase : BST (key.val + 1) baseUpper}
    {left : BST lower key.val}
    {right : BST (key.val + 1) upper}
    (leftSpine : LeftSpine snapshot leftBase left)
    (rightSpine : RightSpine snapshot rightBase right)
    (owner :
      IntervalOwner snapshot (.node left right)
        rightSpine.upper_le_n key) :
    bendsFrom snapshot (.node left right)
        rightSpine.upper_le_n none =
      (bendsFrom snapshot leftBase leftSpine.base_le_n
          (LeftSpine.incomingAtBase leftSpine) ∪
        leftSpine.hangingBends) ∪
      (bendsFrom snapshot rightBase rightSpine.base_le_n
          (RightSpine.incomingAtBase rightSpine) ∪
        rightSpine.hangingBends) := by
  apply finalRoot_bendsFrom_eq leftSpine rightSpine
  apply IntervalOwner.heavyBranch_eq
    left right rightSpine.upper_le_n key owner .middle
  rfl

/--
Complete-tree specialization for the canonical two-boundary temporary
snapshot.  No extra heavy-branch premise remains.
-/
theorem temporaryFinalRoot_bends_eq
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
    bends
        (temporarySnapshot comparison key comparisonRoot
          leftBoundary rightBoundary ordered)
        (.node left right) =
      (bendsFrom
          (temporarySnapshot comparison key comparisonRoot
            leftBoundary rightBoundary ordered)
          leftBase leftSpine.base_le_n
          (LeftSpine.incomingAtBase leftSpine) ∪
        leftSpine.hangingBends) ∪
      (bendsFrom
          (temporarySnapshot comparison key comparisonRoot
            leftBoundary rightBoundary ordered)
          rightBase rightSpine.base_le_n
          (RightSpine.incomingAtBase rightSpine) ∪
        rightSpine.hangingBends) := by
  apply finalRoot_bendsFrom_eq_of_owner leftSpine rightSpine
  exact
    temporarySnapshot_fullIntervalOwner
      comparison key comparisonRoot leftBoundary rightBoundary
        ordered (.node left right)

end Splay.Accounting.WholeSplayTemporaryFinalSpineBends
