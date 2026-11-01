import Splay.Accounting.WholeSplayTemporaryCreationGeometry
import Splay.Accounting.WholeSplayTemporarySpineGeometry
import Splay.Accounting.WholeSplayTemporaryFocusedSpines
import Splay.Accounting.WholeSplayTemporaryCreationChronology
import Splay.Accounting.WholeSplayTemporaryCreationContext
import Splay.Accounting.WholeSplayTemporaryCreationSetDecomposition
import Splay.Accounting.WholeSplayTemporaryFinalSpineAttachments
import Splay.Accounting.WholeSplayTemporaryRootCreation
import Splay.Accounting.WholeSplayTemporarySpineCreation

namespace Splay.Accounting.WholeSplayTemporaryCreationPersistence

open Splay.Rank
open Splay.Tree.BST
open Splay.Lazy.Canonical
open Splay.Accounting.LocalBendGeometry
open Splay.Accounting.WholeSplayTemporaryPriorityReduction
open Splay.Accounting.WholeSplayTemporaryBoundaryGeometry
open Splay.Accounting.WholeSplayTemporaryCoreGeometry
open Splay.Accounting.WholeSplayTemporaryCreationGeometry
open Splay.Accounting.WholeSplayTemporarySpineGeometry
open Splay.Accounting.WholeSplayTemporaryFocusedSpines
open Splay.Accounting.WholeSplayTemporaryCreationChronology
open Splay.Accounting.WholeSplayTemporaryCreationSetDecomposition

namespace AutomaticCanonicalPersistence

/--
Every canonical temporary-snapshot node strictly above the accessed key
selects its left branch.  This packages the repeatedly used path-heavy
equation independently of the concrete rotation shape.
-/
theorem heavyBranch_eq_left_of_key_lt_root
    {n : ℕ} (comparison : BST 0 n) (key : Fin n)
    (comparisonRoot : comparison.HasRoot key.val)
    (leftBoundary rightBoundary : External n)
    (ordered :
      leftBoundary < valuePos key ∧ valuePos key < rightBoundary)
    (node : AtNode n)
    (lower_le_key : node.lower ≤ key.val)
    (key_lt_root : key.val < node.root) :
    node.heavyBranch
        (temporarySnapshot comparison key comparisonRoot
          leftBoundary rightBoundary ordered) = .left := by
  apply
    heavyBranch_eq_of_isIntervalMin
      (temporarySnapshot comparison key comparisonRoot
        leftBoundary rightBoundary ordered)
      node (valuePos key) .left
  · apply
      valuePos_isIntervalMin comparison key comparisonRoot
        leftBoundary rightBoundary node.wholeLower node.wholeUpper ordered
    constructor
    · change 2 * node.lower ≤ 2 * key.val + 1
      omega
    · change 2 * key.val + 1 ≤ 2 * node.upper
      have root_lt_upper := node.root_lt_upper
      omega
  · simp only [TernaryBranch.Contains, valuePos]
    omega

/-- Symmetric path-heavy equation below a node lying left of the key. -/
theorem heavyBranch_eq_right_of_root_lt_key
    {n : ℕ} (comparison : BST 0 n) (key : Fin n)
    (comparisonRoot : comparison.HasRoot key.val)
    (leftBoundary rightBoundary : External n)
    (ordered :
      leftBoundary < valuePos key ∧ valuePos key < rightBoundary)
    (node : AtNode n)
    (root_lt_key : node.root < key.val)
    (key_lt_upper : key.val < node.upper) :
    node.heavyBranch
        (temporarySnapshot comparison key comparisonRoot
          leftBoundary rightBoundary ordered) = .right := by
  apply
    heavyBranch_eq_of_isIntervalMin
      (temporarySnapshot comparison key comparisonRoot
        leftBoundary rightBoundary ordered)
      node (valuePos key) .right
  · apply
      valuePos_isIntervalMin comparison key comparisonRoot
        leftBoundary rightBoundary node.wholeLower node.wholeUpper ordered
    constructor
    · change 2 * node.lower ≤ 2 * key.val + 1
      have lower_le_root := node.lower_le_root
      omega
    · change 2 * key.val + 1 ≤ 2 * node.upper
      omega
  · simp only [TernaryBranch.Contains, valuePos]
    omega

/-- The accessed key itself selects the middle external branch. -/
theorem heavyBranch_eq_middle_at_key
    {n : ℕ} (comparison : BST 0 n) (key : Fin n)
    (comparisonRoot : comparison.HasRoot key.val)
    (leftBoundary rightBoundary : External n)
    (ordered :
      leftBoundary < valuePos key ∧ valuePos key < rightBoundary)
    (node : AtNode n)
    (root_eq : node.root = key.val) :
    node.heavyBranch
        (temporarySnapshot comparison key comparisonRoot
          leftBoundary rightBoundary ordered) = .middle := by
  apply
    heavyBranch_eq_of_isIntervalMin
      (temporarySnapshot comparison key comparisonRoot
        leftBoundary rightBoundary ordered)
      node (valuePos key) .middle
  · apply
      valuePos_isIntervalMin comparison key comparisonRoot
        leftBoundary rightBoundary node.wholeLower node.wholeUpper ordered
    constructor
    · change 2 * node.lower ≤ 2 * key.val + 1
      have lower_le_root := node.lower_le_root
      omega
    · change 2 * key.val + 1 ≤ 2 * node.upper
      have root_lt_upper := node.root_lt_upper
      omega
  · simp only [TernaryBranch.Contains, valuePos]
    omega

/--
Canonical right-boundary equation for the concrete outer node of one
right-spine grow.
-/
theorem rightSpineGrow_heavy
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
    (({
      lower := key.val + 1
      root := root
      upper := upper
      left := inner
      right := hanging
      upper_le_n := upper_le_n
    } : AtNode n).heavyBranch
      (temporarySnapshot comparison key comparisonRoot
        leftBoundary rightBoundary ordered)) = .left := by
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
        have baseToRoot := RightSpine.baseUpper_le_upper innerSpine
        have rootToUpper := hanging.lower_le_upper
        have boundaryAtBase := base.right_upper_mem
        omega
    · change 2 * key.val + 1 < 2 * (key.val + 1)
      omega
  · change rightBoundary.val ≤ 2 * root
    have baseToRoot := RightSpine.baseUpper_le_upper innerSpine
    have boundaryAtBase := base.right_upper_mem
    omega

/-- Mirror canonical left-boundary equation for a left-spine grow. -/
theorem leftSpineGrow_heavy
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
    (({
      lower := lower
      root := root
      upper := key.val
      left := hanging
      right := inner
      upper_le_n := Nat.le_of_lt key.isLt
    } : AtNode n).heavyBranch
      (temporarySnapshot comparison key comparisonRoot
        leftBoundary rightBoundary ordered)) = .right := by
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
        have innerToBase := LeftSpine.lower_le_baseLower innerSpine
        have boundaryAtBase := base.left_lower_mem
        omega
      · change leftBoundary.val ≤ 2 * key.val
        exact base.left_upper_mem
    · change 2 * key.val < 2 * key.val + 1
      omega
  · change 2 * root + 2 ≤ leftBoundary.val
    have innerToBase := LeftSpine.lower_le_baseLower innerSpine
    have boundaryAtBase := base.left_lower_mem
    omega

end AutomaticCanonicalPersistence

namespace RightSpineAttachment

/--
Incoming edge seen by the original right child after a final right spine has
been assembled.  It is unchanged for an empty spine and becomes `left` as
soon as at least one ancestor is placed above it.
-/
def baseIncoming
    {n key baseUpper upper : ℕ} {snapshot : Snapshot n}
    {base : BST (key + 1) baseUpper}
    {tree : BST (key + 1) upper}
    (spine : RightSpine snapshot base tree) :
    Option TernaryBranch :=
  match spine with
  | .base _ => none
  | .grow _ _ _ _ => some .left

/--
With no incoming edge at the outer root, a right spine consists exactly of
the fixed base under its one possible new incoming-left edge and the
unchanged hanging subtrees.

This is the set-level right-attachment invariant needed by the complete
construction; it loses no bend identities.
-/
theorem bendsFrom_none_decomposition
    {n key baseUpper upper : ℕ} {snapshot : Snapshot n}
    {base : BST (key + 1) baseUpper}
    {tree : BST (key + 1) upper}
    (spine : RightSpine snapshot base tree) :
    bendsFrom snapshot tree spine.upper_le_n none =
      bendsFrom snapshot base spine.base_le_n
          (baseIncoming spine) ∪
        spine.hangingBends := by
  cases spine with
  | base bound =>
      simp [baseIncoming, RightSpine.upper_le_n,
        RightSpine.base_le_n, RightSpine.hangingBends]
  | @grow root upper inner innerSpine hanging bound heavy =>
      have heavy' :
          (({
            lower := key + 1
            root := root
            upper := upper
            left := inner
            right := hanging
            upper_le_n := bound
          } : AtNode n).heavyBranch snapshot) = .left := by
        exact heavy
      simp only [baseIncoming, RightSpine.upper_le_n,
        RightSpine.base_le_n, RightSpine.hangingBends]
      simp only [bendsFrom, heavy', childIncoming]
      simp [bendAt, Turns, innerSpine.bendsFrom_some_left,
        Finset.union_assoc]

/--
Consequently a complete right spine has at most one new bend beyond its
fixed base and hanging-subtree components: the right administrative
attachment.
-/
theorem created_over_base_and_hanging_le_one
    {n key baseUpper upper : ℕ} {snapshot : Snapshot n}
    {base : BST (key + 1) baseUpper}
    {tree : BST (key + 1) upper}
    (spine : RightSpine snapshot base tree) :
    ((bendsFrom snapshot tree spine.upper_le_n none) \
      (bendsFrom snapshot base spine.base_le_n none ∪
        spine.hangingBends)).card ≤ 1 := by
  rw [bendsFrom_none_decomposition]
  exact
    (card_sdiff_union_same_le
      (bendsFrom snapshot base spine.base_le_n
        (baseIncoming spine))
      (bendsFrom snapshot base spine.base_le_n none)
      spine.hangingBends).trans
      (bendsFrom_sdiff_le_one snapshot base spine.base_le_n _ _)

end RightSpineAttachment

namespace ZigZigWinnerProvenance

/--
Joining two formerly detached subtrees below a fresh root can create at most
one bend beyond the two children with no incoming edge.  This is the local
set-theoretic reason that an LL/RR zig-zig has only one genuine hanging-tree
winner: the new root has no incoming edge, and at most one child receives
the newly selected heavy edge.
-/
theorem assembledNode_created_over_children_le_one
    {n lower root upper : ℕ} (snapshot : Snapshot n)
    (left : BST lower root) (right : BST (root + 1) upper)
    (upper_le_n : upper ≤ n) :
    ((bendsFrom snapshot (.node left right) upper_le_n none) \
      (bendsFrom snapshot left (by
          have rightBounds := right.lower_le_upper
          omega) none ∪
        bendsFrom snapshot right upper_le_n none)).card ≤ 1 := by
  let node : AtNode n :=
    { lower := lower
      root := root
      upper := upper
      left := left
      right := right
      upper_le_n := upper_le_n }
  have root_le_n : root ≤ n := by
    have rightBounds := right.lower_le_upper
    omega
  generalize branchEq : node.heavyBranch snapshot = branch
  cases branch with
  | left =>
      have changed :=
        (card_sdiff_union_same_le
          (bendsFrom snapshot left root_le_n (some .left))
          (bendsFrom snapshot left root_le_n none)
          (bendsFrom snapshot right upper_le_n none)).trans
          (bendsFrom_sdiff_le_one
            snapshot left root_le_n (some .left) none)
      simpa [bendsFrom, node, branchEq, childIncoming, bendAt, Turns]
        using changed
  | middle =>
      simp [bendsFrom, node, branchEq, childIncoming, bendAt, Turns]
  | right =>
      have changed :=
        (card_sdiff_same_union_le
          (bendsFrom snapshot left root_le_n none)
          (bendsFrom snapshot right upper_le_n (some .right))
          (bendsFrom snapshot right upper_le_n none)).trans
          (bendsFrom_sdiff_le_one
            snapshot right upper_le_n (some .right) none)
      simpa [bendsFrom, node, branchEq, childIncoming, bendAt, Turns]
        using changed

/--
Growing a right spine around a hanging subtree which was already entered
with `none` can create only the right-base incoming-edge attachment.  Once
the spine was already nontrivial, even that incoming edge is unchanged.
-/
theorem rightGrow_created_subset_baseAttachment
    {n key baseUpper root upper : ℕ} {snapshot : Snapshot n}
    {base : BST (key + 1) baseUpper}
    {inner : BST (key + 1) root}
    (innerSpine : RightSpine snapshot base inner)
    (hanging : BST (root + 1) upper)
    (upper_le_n : upper ≤ n)
    (heavy :
      (({
        lower := key + 1
        root := root
        upper := upper
        left := inner
        right := hanging
        upper_le_n := upper_le_n
      } : AtNode n).heavyBranch snapshot) = .left) :
    (bendsFrom snapshot (.node inner hanging) upper_le_n none \
      (bendsFrom snapshot inner innerSpine.upper_le_n none ∪
        bendsFrom snapshot hanging upper_le_n none)) ⊆
      (bendsFrom snapshot base innerSpine.base_le_n (some .left) \
        bendsFrom snapshot base innerSpine.base_le_n none) := by
  intro element member
  rw [
    Splay.Accounting.WholeSplayTemporarySpineGeometry.RightSpine.bendsFrom_none_grow
      innerSpine hanging upper_le_n heavy] at member
  cases innerSpine with
  | base baseBound =>
      simp only [
        Splay.Accounting.WholeSplayTemporarySpineGeometry.RightSpine.upper_le_n,
        Splay.Accounting.WholeSplayTemporarySpineGeometry.RightSpine.base_le_n,
        Splay.Accounting.WholeSplayTemporarySpineGeometry.RightSpine.hangingBends,
        Finset.empty_union, Finset.mem_sdiff, Finset.mem_union] at member ⊢
      tauto
  | @grow previousRoot previousUpper previous previousSpine
      previousHanging previousBound previousHeavy =>
      have innerEq :=
        Splay.Accounting.WholeSplayTemporaryFinalSpineBends.RightSpine.bendsFrom_none_eq
            (RightSpine.grow previousSpine previousHanging
              previousBound previousHeavy)
      simp only [
        Splay.Accounting.WholeSplayTemporaryFinalSpineBends.RightSpine.incomingAtBase,
        Splay.Accounting.WholeSplayTemporarySpineGeometry.RightSpine.upper_le_n,
        Splay.Accounting.WholeSplayTemporarySpineGeometry.RightSpine.base_le_n,
        Splay.Accounting.WholeSplayTemporarySpineGeometry.RightSpine.hangingBends,
        Finset.mem_sdiff, Finset.mem_union]
        at innerEq member ⊢
      rw [innerEq] at member
      simp only [Finset.mem_union] at member
      tauto

/-- Mirror of `rightGrow_created_subset_baseAttachment` for a left spine. -/
theorem leftGrow_created_subset_baseAttachment
    {n key baseLower lower root : ℕ} {snapshot : Snapshot n}
    {base : BST baseLower key}
    {inner : BST (root + 1) key}
    (innerSpine : LeftSpine snapshot base inner)
    (hanging : BST lower root)
    (root_le_n : root ≤ n) (key_le_n : key ≤ n)
    (heavy :
      (({
        lower := lower
        root := root
        upper := key
        left := hanging
        right := inner
        upper_le_n := key_le_n
      } : AtNode n).heavyBranch snapshot) = .right) :
    (bendsFrom snapshot (.node hanging inner) key_le_n none \
      (bendsFrom snapshot hanging root_le_n none ∪
        bendsFrom snapshot inner innerSpine.upper_le_n none)) ⊆
      (bendsFrom snapshot base innerSpine.base_le_n (some .right) \
        bendsFrom snapshot base innerSpine.base_le_n none) := by
  intro element member
  rw [
    Splay.Accounting.WholeSplayTemporarySpineGeometry.LeftSpine.bendsFrom_none_grow
      innerSpine hanging root_le_n key_le_n heavy] at member
  cases innerSpine with
  | base baseBound =>
      simp only [
        Splay.Accounting.WholeSplayTemporarySpineGeometry.LeftSpine.upper_le_n,
        Splay.Accounting.WholeSplayTemporarySpineGeometry.LeftSpine.base_le_n,
        Splay.Accounting.WholeSplayTemporarySpineGeometry.LeftSpine.hangingBends,
        Finset.union_empty, Finset.mem_sdiff, Finset.mem_union] at member ⊢
      tauto
  | @grow previousLower previousRoot previous previousSpine
      previousHanging previousRootBound previousBound previousHeavy =>
      have innerEq :=
        Splay.Accounting.WholeSplayTemporaryFinalSpineBends.LeftSpine.bendsFrom_none_eq
          (LeftSpine.grow previousSpine previousHanging
            previousRootBound previousBound previousHeavy)
      simp only [
        Splay.Accounting.WholeSplayTemporaryFinalSpineBends.LeftSpine.incomingAtBase,
        Splay.Accounting.WholeSplayTemporarySpineGeometry.LeftSpine.upper_le_n,
        Splay.Accounting.WholeSplayTemporarySpineGeometry.LeftSpine.base_le_n,
        Splay.Accounting.WholeSplayTemporarySpineGeometry.LeftSpine.hangingBends,
        Finset.mem_sdiff, Finset.mem_union]
        at innerEq member ⊢
      rw [innerEq] at member
      simp only [Finset.mem_union] at member
      tauto

/--
Changing the incoming edge of a current right spine from `none` to `left`
can only expose the fixed right-base attachment.  For a nontrivial spine
the two incoming-edge bend sets are in fact equal, since its outer edge is
already the stored heavy-left spine edge.
-/
theorem rightSpine_incomingDelta_subset_baseAttachment
    {n key baseUpper upper : ℕ} {snapshot : Snapshot n}
    {base : BST (key + 1) baseUpper}
    {tree : BST (key + 1) upper}
    (spine : RightSpine snapshot base tree) :
    (bendsFrom snapshot tree spine.upper_le_n (some .left) \
      bendsFrom snapshot tree spine.upper_le_n none) ⊆
      (bendsFrom snapshot base spine.base_le_n (some .left) \
        bendsFrom snapshot base spine.base_le_n none) := by
  cases spine with
  | base bound =>
      exact Finset.Subset.rfl
  | @grow root upper inner innerSpine hanging bound heavy =>
      have someEq :=
        Splay.Accounting.WholeSplayTemporarySpineGeometry.RightSpine.bendsFrom_some_left
          (RightSpine.grow innerSpine hanging bound heavy)
      have noneEq :=
        Splay.Accounting.WholeSplayTemporaryFinalSpineBends.RightSpine.bendsFrom_none_eq
          (RightSpine.grow innerSpine hanging bound heavy)
      simp only [
        Splay.Accounting.WholeSplayTemporaryFinalSpineBends.RightSpine.incomingAtBase]
        at noneEq
      intro element member
      rw [someEq, noneEq] at member
      exact False.elim
        ((Finset.mem_sdiff.mp member).2 (Finset.mem_sdiff.mp member).1)

/--
Mirror classification for a current left spine: its incoming-right delta is
always contained in the one fixed left-base attachment.
-/
theorem leftSpine_incomingDelta_subset_baseAttachment
    {n key baseLower lower : ℕ} {snapshot : Snapshot n}
    {base : BST baseLower key}
    {tree : BST lower key}
    (spine : LeftSpine snapshot base tree) :
    (bendsFrom snapshot tree spine.upper_le_n (some .right) \
      bendsFrom snapshot tree spine.upper_le_n none) ⊆
      (bendsFrom snapshot base spine.base_le_n (some .right) \
        bendsFrom snapshot base spine.base_le_n none) := by
  cases spine with
  | base bound =>
      exact Finset.Subset.rfl
  | @grow lower root inner innerSpine hanging rootBound bound heavy =>
      have someEq :=
        Splay.Accounting.WholeSplayTemporarySpineGeometry.LeftSpine.bendsFrom_some_right
          (LeftSpine.grow innerSpine hanging rootBound bound heavy)
      have noneEq :=
        Splay.Accounting.WholeSplayTemporaryFinalSpineBends.LeftSpine.bendsFrom_none_eq
          (LeftSpine.grow innerSpine hanging rootBound bound heavy)
      simp only [
        Splay.Accounting.WholeSplayTemporaryFinalSpineBends.LeftSpine.incomingAtBase]
        at noneEq
      intro element member
      rw [someEq, noneEq] at member
      exact False.elim
        ((Finset.mem_sdiff.mp member).2 (Finset.mem_sdiff.mp member).1)

end ZigZigWinnerProvenance

namespace AutomaticCanonicalPersistence

open Splay.Accounting.WholeSplayTemporaryRootCreation
open Splay.Accounting.WholeSplayTemporarySpineCreation

/--
The two fixed-base incoming-edge deltas.  These are the only
administrative endpoint identities that survive all the way to the two
final attachment slots.
-/
noncomputable def fixedBaseDeltas
    {n : ℕ}
    (comparison : BST 0 n) (key : Fin n)
    (comparisonRoot : comparison.HasRoot key.val)
    (leftBoundary rightBoundary : External n)
    (ordered :
      leftBoundary < valuePos key ∧ valuePos key < rightBoundary)
    (base : SpineBase key leftBoundary rightBoundary)
    (rightBase_le_n : base.rightUpper ≤ n) : Finset (Fin n) :=
  (bendsFrom
      (temporarySnapshot comparison key comparisonRoot
        leftBoundary rightBoundary ordered)
      base.leftTree (Nat.le_of_lt key.isLt) (some .right) \
    bendsFrom
      (temporarySnapshot comparison key comparisonRoot
        leftBoundary rightBoundary ordered)
      base.leftTree (Nat.le_of_lt key.isLt) none) ∪
  (bendsFrom
      (temporarySnapshot comparison key comparisonRoot
        leftBoundary rightBoundary ordered)
      base.rightTree rightBase_le_n (some .left) \
    bendsFrom
      (temporarySnapshot comparison key comparisonRoot
        leftBoundary rightBoundary ordered)
      base.rightTree rightBase_le_n none)

/--
A canonical root zig can create only one of the two fixed-base incoming
deltas.  The statement is generalized over the incoming edge of the
rotated fragment so it can also serve later contextual arguments.
-/
theorem zig_created_subset_baseDeltas
    {n lower upper : ℕ}
    (comparison : BST 0 n) (key : Fin n)
    (comparisonRoot : comparison.HasRoot key.val)
    (leftBoundary rightBoundary : External n)
    (ordered :
      leftBoundary < valuePos key ∧ valuePos key < rightBoundary)
    (base : SpineBase key leftBoundary rightBoundary)
    (rightBase_le_n : base.rightUpper ≤ n)
    {before after : BST lower upper}
    (focused :
      FocusedSpines
        (temporarySnapshot comparison key comparisonRoot
          leftBoundary rightBoundary ordered)
        key leftBoundary rightBoundary base before)
    (step : Zig key.val before after)
    (upper_le_n : upper ≤ n)
    (incoming : Option TernaryBranch) :
    (bendsFrom
        (temporarySnapshot comparison key comparisonRoot
          leftBoundary rightBoundary ordered)
        after upper_le_n incoming \
      bendsFrom
        (temporarySnapshot comparison key comparisonRoot
          leftBoundary rightBoundary ordered)
        before upper_le_n incoming) ⊆
      ((bendsFrom
          (temporarySnapshot comparison key comparisonRoot
            leftBoundary rightBoundary ordered)
          base.leftTree (Nat.le_of_lt key.isLt) (some .right) \
        bendsFrom
          (temporarySnapshot comparison key comparisonRoot
            leftBoundary rightBoundary ordered)
          base.leftTree (Nat.le_of_lt key.isLt) none) ∪
       (bendsFrom
          (temporarySnapshot comparison key comparisonRoot
            leftBoundary rightBoundary ordered)
          base.rightTree rightBase_le_n (some .left) \
        bendsFrom
          (temporarySnapshot comparison key comparisonRoot
            leftBoundary rightBoundary ordered)
          base.rightTree rightBase_le_n none)) := by
  let snapshot :=
    temporarySnapshot comparison key comparisonRoot
      leftBoundary rightBoundary ordered
  cases step with
  | @fromLeft lower promoted demoted upper a b c =>
      cases focused with
      | atKey leftSpine rightSpine =>
          have middleBounds := b.lower_le_upper
          omega
      | leftContext innerFocused contextRight =>
          cases innerFocused with
          | atKey leftSpine rightSpine =>
              have beforeRoot :
                  (({
                    lower := lower
                    root := demoted
                    upper := upper
                    left := .node a b
                    right := c
                    upper_le_n := upper_le_n
                  } : AtNode n).heavyBranch snapshot) = .left := by
                apply heavyBranch_eq_left_of_key_lt_root
                · change lower ≤ key.val
                  have aBounds := a.lower_le_upper
                  omega
                · change key.val < demoted
                  have bBounds := b.lower_le_upper
                  omega
              have beforePromoted :
                  (({
                    lower := lower
                    root := key.val
                    upper := demoted
                    left := a
                    right := b
                    upper_le_n := by
                      have cBounds := c.lower_le_upper
                      omega
                  } : AtNode n).heavyBranch snapshot) = .middle := by
                apply heavyBranch_eq_middle_at_key
                rfl
              have afterRoot :
                  (({
                    lower := lower
                    root := key.val
                    upper := upper
                    left := a
                    right := .node b c
                    upper_le_n := upper_le_n
                  } : AtNode n).heavyBranch snapshot) = .middle := by
                apply heavyBranch_eq_middle_at_key
                rfl
              have afterDemoted :
                  (({
                    lower := key.val + 1
                    root := demoted
                    upper := upper
                    left := b
                    right := c
                    upper_le_n := upper_le_n
                  } : AtNode n).heavyBranch snapshot) = .left := by
                exact
                  rightSpineGrow_heavy comparison key comparisonRoot
                    leftBoundary rightBoundary ordered base
                    rightSpine c upper_le_n
              intro identity created
              have localCreated :=
                zigFromLeft_created_subset_baseIncomingDelta
                  snapshot a b c upper_le_n incoming
                    beforeRoot beforePromoted afterRoot afterDemoted created
              apply Finset.mem_union.mpr
              apply Or.inr
              exact
                rightSpine_incomingLeftDelta_subset_baseDelta
                  rightSpine localCreated
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
      | rightContext contextLeft innerFocused =>
          cases innerFocused with
          | atKey leftSpine rightSpine =>
              have beforeRoot :
                  (({
                    lower := lower
                    root := demoted
                    upper := upper
                    left := a
                    right := .node b c
                    upper_le_n := upper_le_n
                  } : AtNode n).heavyBranch snapshot) = .right := by
                apply heavyBranch_eq_right_of_root_lt_key
                · change demoted < key.val
                  have bBounds := b.lower_le_upper
                  omega
                · change key.val < upper
                  have cBounds := c.lower_le_upper
                  omega
              have beforePromoted :
                  (({
                    lower := demoted + 1
                    root := key.val
                    upper := upper
                    left := b
                    right := c
                    upper_le_n := upper_le_n
                  } : AtNode n).heavyBranch snapshot) = .middle := by
                apply heavyBranch_eq_middle_at_key
                rfl
              have afterRoot :
                  (({
                    lower := lower
                    root := key.val
                    upper := upper
                    left := .node a b
                    right := c
                    upper_le_n := upper_le_n
                  } : AtNode n).heavyBranch snapshot) = .middle := by
                apply heavyBranch_eq_middle_at_key
                rfl
              have demoted_le_n : demoted ≤ n := by
                have aBounds := a.lower_le_upper
                have bBounds := b.lower_le_upper
                omega
              have afterDemoted :
                  (({
                    lower := lower
                    root := demoted
                    upper := key.val
                    left := a
                    right := b
                    upper_le_n := Nat.le_of_lt key.isLt
                  } : AtNode n).heavyBranch snapshot) = .right := by
                exact
                  leftSpineGrow_heavy comparison key comparisonRoot
                    leftBoundary rightBoundary ordered base
                    leftSpine a demoted_le_n
              intro identity created
              have localCreated :=
                zigFromRight_created_subset_baseIncomingDelta
                  snapshot a b c upper_le_n incoming
                    beforeRoot beforePromoted afterRoot afterDemoted created
              apply Finset.mem_union.mpr
              apply Or.inl
              exact
                leftSpine_incomingRightDelta_subset_baseDelta
                  leftSpine localCreated
          | leftContext focused rightTree =>
              have bounds := FocusedSpines.key_bounds focused
              omega
          | rightContext leftTree focused =>
              have bounds := FocusedSpines.key_bounds focused
              omega

/--
A left final zig creates only the right fixed-base delta.  This directional
form retains the information needed to select the matching terminal
attachment slot.
-/
theorem zigFromLeft_created_subset_rightBaseDelta
    {n lower demoted upper : ℕ}
    (comparison : BST 0 n) (key : Fin n)
    (comparisonRoot : comparison.HasRoot key.val)
    (leftBoundary rightBoundary : External n)
    (ordered :
      leftBoundary < valuePos key ∧ valuePos key < rightBoundary)
    (base : SpineBase key leftBoundary rightBoundary)
    (rightBase_le_n : base.rightUpper ≤ n)
    (a : BST lower key.val)
    (b : BST (key.val + 1) demoted)
    (c : BST (demoted + 1) upper)
    (focused :
      FocusedSpines
        (temporarySnapshot comparison key comparisonRoot
          leftBoundary rightBoundary ordered)
        key leftBoundary rightBoundary base
        (.node (.node a b) c))
    (upper_le_n : upper ≤ n)
    (incoming : Option TernaryBranch) :
    (bendsFrom
        (temporarySnapshot comparison key comparisonRoot
          leftBoundary rightBoundary ordered)
        (.node a (.node b c)) upper_le_n incoming \
      bendsFrom
        (temporarySnapshot comparison key comparisonRoot
          leftBoundary rightBoundary ordered)
        (.node (.node a b) c) upper_le_n incoming) ⊆
      (bendsFrom
          (temporarySnapshot comparison key comparisonRoot
            leftBoundary rightBoundary ordered)
          base.rightTree rightBase_le_n (some .left) \
        bendsFrom
          (temporarySnapshot comparison key comparisonRoot
            leftBoundary rightBoundary ordered)
          base.rightTree rightBase_le_n none) := by
  let snapshot :=
    temporarySnapshot comparison key comparisonRoot
      leftBoundary rightBoundary ordered
  cases focused with
  | atKey leftSpine rightSpine =>
      have bBounds := b.lower_le_upper
      omega
  | leftContext innerFocused contextRight =>
      cases innerFocused with
      | atKey leftSpine rightSpine =>
          have beforeRoot :
              (({
                lower := lower
                root := demoted
                upper := upper
                left := .node a b
                right := c
                upper_le_n := upper_le_n
              } : AtNode n).heavyBranch snapshot) = .left := by
            apply heavyBranch_eq_left_of_key_lt_root
            · change lower ≤ key.val
              have aBounds := a.lower_le_upper
              omega
            · change key.val < demoted
              have bBounds := b.lower_le_upper
              omega
          have beforePromoted :
              (({
                lower := lower
                root := key.val
                upper := demoted
                left := a
                right := b
                upper_le_n := by
                  have cBounds := c.lower_le_upper
                  omega
              } : AtNode n).heavyBranch snapshot) = .middle := by
            apply heavyBranch_eq_middle_at_key
            rfl
          have afterRoot :
              (({
                lower := lower
                root := key.val
                upper := upper
                left := a
                right := .node b c
                upper_le_n := upper_le_n
              } : AtNode n).heavyBranch snapshot) = .middle := by
            apply heavyBranch_eq_middle_at_key
            rfl
          have afterDemoted :
              (({
                lower := key.val + 1
                root := demoted
                upper := upper
                left := b
                right := c
                upper_le_n := upper_le_n
              } : AtNode n).heavyBranch snapshot) = .left := by
            exact
              rightSpineGrow_heavy comparison key comparisonRoot
                leftBoundary rightBoundary ordered base
                rightSpine c upper_le_n
          intro identity created
          exact
            rightSpine_incomingLeftDelta_subset_baseDelta
              rightSpine
              (zigFromLeft_created_subset_baseIncomingDelta
                snapshot a b c upper_le_n incoming
                  beforeRoot beforePromoted afterRoot afterDemoted created)
      | leftContext nestedFocused rightTree =>
          have bounds := FocusedSpines.key_bounds nestedFocused
          omega
      | rightContext leftTree nestedFocused =>
          have bounds := FocusedSpines.key_bounds nestedFocused
          omega
  | rightContext leftTree innerFocused =>
      have bounds := FocusedSpines.key_bounds innerFocused
      have bBounds := b.lower_le_upper
      omega

/-- Symmetric directional form for a right final zig. -/
theorem zigFromRight_created_subset_leftBaseDelta
    {n lower demoted upper : ℕ}
    (comparison : BST 0 n) (key : Fin n)
    (comparisonRoot : comparison.HasRoot key.val)
    (leftBoundary rightBoundary : External n)
    (ordered :
      leftBoundary < valuePos key ∧ valuePos key < rightBoundary)
    (base : SpineBase key leftBoundary rightBoundary)
    (a : BST lower demoted)
    (b : BST (demoted + 1) key.val)
    (c : BST (key.val + 1) upper)
    (focused :
      FocusedSpines
        (temporarySnapshot comparison key comparisonRoot
          leftBoundary rightBoundary ordered)
        key leftBoundary rightBoundary base
        (.node a (.node b c)))
    (upper_le_n : upper ≤ n)
    (incoming : Option TernaryBranch) :
    (bendsFrom
        (temporarySnapshot comparison key comparisonRoot
          leftBoundary rightBoundary ordered)
        (.node (.node a b) c) upper_le_n incoming \
      bendsFrom
        (temporarySnapshot comparison key comparisonRoot
          leftBoundary rightBoundary ordered)
        (.node a (.node b c)) upper_le_n incoming) ⊆
      (bendsFrom
          (temporarySnapshot comparison key comparisonRoot
            leftBoundary rightBoundary ordered)
          base.leftTree (Nat.le_of_lt key.isLt) (some .right) \
        bendsFrom
          (temporarySnapshot comparison key comparisonRoot
            leftBoundary rightBoundary ordered)
          base.leftTree (Nat.le_of_lt key.isLt) none) := by
  let snapshot :=
    temporarySnapshot comparison key comparisonRoot
      leftBoundary rightBoundary ordered
  cases focused with
  | atKey leftSpine rightSpine =>
      have bBounds := b.lower_le_upper
      omega
  | leftContext innerFocused rightTree =>
      have bounds := FocusedSpines.key_bounds innerFocused
      have bBounds := b.lower_le_upper
      omega
  | rightContext contextLeft innerFocused =>
      cases innerFocused with
      | atKey leftSpine rightSpine =>
          have beforeRoot :
              (({
                lower := lower
                root := demoted
                upper := upper
                left := a
                right := .node b c
                upper_le_n := upper_le_n
              } : AtNode n).heavyBranch snapshot) = .right := by
            apply heavyBranch_eq_right_of_root_lt_key
            · change demoted < key.val
              have bBounds := b.lower_le_upper
              omega
            · change key.val < upper
              have cBounds := c.lower_le_upper
              omega
          have beforePromoted :
              (({
                lower := demoted + 1
                root := key.val
                upper := upper
                left := b
                right := c
                upper_le_n := upper_le_n
              } : AtNode n).heavyBranch snapshot) = .middle := by
            apply heavyBranch_eq_middle_at_key
            rfl
          have afterRoot :
              (({
                lower := lower
                root := key.val
                upper := upper
                left := .node a b
                right := c
                upper_le_n := upper_le_n
              } : AtNode n).heavyBranch snapshot) = .middle := by
            apply heavyBranch_eq_middle_at_key
            rfl
          have demoted_le_n : demoted ≤ n := by
            have bBounds := b.lower_le_upper
            have keyBound := key.isLt
            omega
          have afterDemoted :
              (({
                lower := lower
                root := demoted
                upper := key.val
                left := a
                right := b
                upper_le_n := Nat.le_of_lt key.isLt
              } : AtNode n).heavyBranch snapshot) = .right := by
            exact
              leftSpineGrow_heavy comparison key comparisonRoot
                leftBoundary rightBoundary ordered base
                leftSpine a demoted_le_n
          intro identity created
          exact
            leftSpine_incomingRightDelta_subset_baseDelta
              leftSpine
              (zigFromRight_created_subset_baseIncomingDelta
                snapshot a b c upper_le_n incoming
                  beforeRoot beforePromoted afterRoot afterDemoted created)
      | leftContext nestedFocused rightTree =>
          have bounds := FocusedSpines.key_bounds nestedFocused
          omega
      | rightContext leftTree nestedFocused =>
          have bounds := FocusedSpines.key_bounds nestedFocused
          omega

/--
The opposite-direction double rotation has no nonadministrative creation,
even under an arbitrary unchanged search context.  Context localization
reduces to the two root zig-zag formulae; both current-spine deltas then
collapse to the two fixed bases.
-/
private theorem zigZag_created_subset_baseDeltas_general
    {n lower upper depth keyValue : ℕ} {flag : Bool}
    (comparison : BST 0 n) (key : Fin n)
    (comparisonRoot : comparison.HasRoot key.val)
    (leftBoundary rightBoundary : External n)
    (ordered :
      leftBoundary < valuePos key ∧ valuePos key < rightBoundary)
    (base : SpineBase key leftBoundary rightBoundary)
    (rightBase_le_n : base.rightUpper ≤ n)
    {before after : BST lower upper}
    (focused :
      FocusedSpines
        (temporarySnapshot comparison key comparisonRoot
          leftBoundary rightBoundary ordered)
        key leftBoundary rightBoundary base before)
    (orientation :
      DoubleOrientationAt flag
        (depth := depth) (key := keyValue) before after)
    (flagEq : flag = false)
    (keyEq : keyValue = key.val)
    (upper_le_n : upper ≤ n)
    (incoming : Option TernaryBranch) :
    (bendsFrom
        (temporarySnapshot comparison key comparisonRoot
          leftBoundary rightBoundary ordered)
        after upper_le_n incoming \
      bendsFrom
        (temporarySnapshot comparison key comparisonRoot
          leftBoundary rightBoundary ordered)
        before upper_le_n incoming) ⊆
      ((bendsFrom
          (temporarySnapshot comparison key comparisonRoot
            leftBoundary rightBoundary ordered)
          base.leftTree (Nat.le_of_lt key.isLt) (some .right) \
        bendsFrom
          (temporarySnapshot comparison key comparisonRoot
            leftBoundary rightBoundary ordered)
          base.leftTree (Nat.le_of_lt key.isLt) none) ∪
       (bendsFrom
          (temporarySnapshot comparison key comparisonRoot
            leftBoundary rightBoundary ordered)
          base.rightTree rightBase_le_n (some .left) \
        bendsFrom
          (temporarySnapshot comparison key comparisonRoot
            leftBoundary rightBoundary ordered)
          base.rightTree rightBase_le_n none)) := by
  let snapshot :=
    temporarySnapshot comparison key comparisonRoot
      leftBoundary rightBoundary ordered
  induction orientation generalizing incoming with
  | zigZigLeft =>
      simp at flagEq
  | zigZigRight =>
      simp at flagEq
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
          | leftContext focused rightTree =>
              have bounds := FocusedSpines.key_bounds focused
              have bBounds := b.lower_le_upper
              omega
          | rightContext contextLeft keyFocused =>
              cases keyFocused with
              | atKey leftSpine rightSpine =>
                  have beforeRoot :
                      (({
                        lower := lower
                        root := third
                        upper := upper
                        left := .node a (.node b c)
                        right := d
                        upper_le_n := upper_le_n
                      } : AtNode n).heavyBranch snapshot) = .left := by
                    apply heavyBranch_eq_left_of_key_lt_root
                    · change lower ≤ key.val
                      have aBounds := a.lower_le_upper
                      have bBounds := b.lower_le_upper
                      omega
                    · change key.val < third
                      have cBounds := c.lower_le_upper
                      omega
                  have beforeFirst :
                      (({
                        lower := lower
                        root := first
                        upper := third
                        left := a
                        right := .node b c
                        upper_le_n := by
                          have dBounds := d.lower_le_upper
                          omega
                      } : AtNode n).heavyBranch snapshot) = .right := by
                    apply heavyBranch_eq_right_of_root_lt_key
                    · change first < key.val
                      have bBounds := b.lower_le_upper
                      omega
                    · change key.val < third
                      have cBounds := c.lower_le_upper
                      omega
                  have beforePromoted :
                      (({
                        lower := first + 1
                        root := key.val
                        upper := third
                        left := b
                        right := c
                        upper_le_n := by
                          have dBounds := d.lower_le_upper
                          omega
                      } : AtNode n).heavyBranch snapshot) = .middle := by
                    apply heavyBranch_eq_middle_at_key
                    rfl
                  have afterRoot :
                      (({
                        lower := lower
                        root := key.val
                        upper := upper
                        left := .node a b
                        right := .node c d
                        upper_le_n := upper_le_n
                      } : AtNode n).heavyBranch snapshot) = .middle := by
                    apply heavyBranch_eq_middle_at_key
                    rfl
                  have first_le_n : first ≤ n := by
                    have aBounds := a.lower_le_upper
                    have bBounds := b.lower_le_upper
                    have keyBound := key.isLt
                    omega
                  have afterFirst :
                      (({
                        lower := lower
                        root := first
                        upper := key.val
                        left := a
                        right := b
                        upper_le_n := Nat.le_of_lt key.isLt
                      } : AtNode n).heavyBranch snapshot) = .right := by
                    exact
                      leftSpineGrow_heavy comparison key comparisonRoot
                        leftBoundary rightBoundary ordered base
                        leftSpine a first_le_n
                  have afterThird :
                      (({
                        lower := key.val + 1
                        root := third
                        upper := upper
                        left := c
                        right := d
                        upper_le_n := upper_le_n
                      } : AtNode n).heavyBranch snapshot) = .left := by
                    exact
                      rightSpineGrow_heavy comparison key comparisonRoot
                        leftBoundary rightBoundary ordered base
                        rightSpine d upper_le_n
                  intro identity created
                  have localCreated :=
                    zigZagLeftRight_created_subset_baseIncomingDeltas
                      snapshot a b c d upper_le_n incoming
                        beforeRoot beforeFirst beforePromoted afterRoot
                        afterFirst afterThird created
                  rcases Finset.mem_union.mp localCreated with
                    inLeft | inRight
                  · exact
                      Finset.mem_union.mpr
                        (Or.inl
                          (leftSpine_incomingRightDelta_subset_baseDelta
                            leftSpine inLeft))
                  · exact
                      Finset.mem_union.mpr
                        (Or.inr
                          (rightSpine_incomingLeftDelta_subset_baseDelta
                            rightSpine inRight))
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
      subst second
      cases focused with
      | atKey leftSpine rightSpine =>
          have bBounds := b.lower_le_upper
          omega
      | leftContext focused rightTree =>
          have bounds := FocusedSpines.key_bounds focused
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
                  have beforeRoot :
                      (({
                        lower := lower
                        root := first
                        upper := upper
                        left := a
                        right := .node (.node b c) d
                        upper_le_n := upper_le_n
                      } : AtNode n).heavyBranch snapshot) = .right := by
                    apply heavyBranch_eq_right_of_root_lt_key
                    · change first < key.val
                      have bBounds := b.lower_le_upper
                      omega
                    · change key.val < upper
                      have cBounds := c.lower_le_upper
                      have dBounds := d.lower_le_upper
                      omega
                  have beforeThird :
                      (({
                        lower := first + 1
                        root := third
                        upper := upper
                        left := .node b c
                        right := d
                        upper_le_n := upper_le_n
                      } : AtNode n).heavyBranch snapshot) = .left := by
                    apply heavyBranch_eq_left_of_key_lt_root
                    · change first + 1 ≤ key.val
                      have bBounds := b.lower_le_upper
                      omega
                    · change key.val < third
                      have cBounds := c.lower_le_upper
                      omega
                  have beforePromoted :
                      (({
                        lower := first + 1
                        root := key.val
                        upper := third
                        left := b
                        right := c
                        upper_le_n := by
                          have dBounds := d.lower_le_upper
                          omega
                      } : AtNode n).heavyBranch snapshot) = .middle := by
                    apply heavyBranch_eq_middle_at_key
                    rfl
                  have afterRoot :
                      (({
                        lower := lower
                        root := key.val
                        upper := upper
                        left := .node a b
                        right := .node c d
                        upper_le_n := upper_le_n
                      } : AtNode n).heavyBranch snapshot) = .middle := by
                    apply heavyBranch_eq_middle_at_key
                    rfl
                  have first_le_n : first ≤ n := by
                    have aBounds := a.lower_le_upper
                    have bBounds := b.lower_le_upper
                    have keyBound := key.isLt
                    omega
                  have afterFirst :
                      (({
                        lower := lower
                        root := first
                        upper := key.val
                        left := a
                        right := b
                        upper_le_n := Nat.le_of_lt key.isLt
                      } : AtNode n).heavyBranch snapshot) = .right := by
                    exact
                      leftSpineGrow_heavy comparison key comparisonRoot
                        leftBoundary rightBoundary ordered base
                        leftSpine a first_le_n
                  have afterThird :
                      (({
                        lower := key.val + 1
                        root := third
                        upper := upper
                        left := c
                        right := d
                        upper_le_n := upper_le_n
                      } : AtNode n).heavyBranch snapshot) = .left := by
                    exact
                      rightSpineGrow_heavy comparison key comparisonRoot
                        leftBoundary rightBoundary ordered base
                        rightSpine d upper_le_n
                  intro identity created
                  have localCreated :=
                    zigZagRightLeft_created_subset_baseIncomingDeltas
                      snapshot a b c d upper_le_n incoming
                        beforeRoot beforeThird beforePromoted afterRoot
                        afterFirst afterThird created
                  rcases Finset.mem_union.mp localCreated with
                    inLeft | inRight
                  · exact
                      Finset.mem_union.mpr
                        (Or.inl
                          (leftSpine_incomingRightDelta_subset_baseDelta
                            leftSpine inLeft))
                  · exact
                      Finset.mem_union.mpr
                        (Or.inr
                          (rightSpine_incomingLeftDelta_subset_baseDelta
                            rightSpine inRight))
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
  | @leftContext flag depth keyValue lower pivot upper before after
      innerOrientation contextRight ih =>
      cases focused with
      | atKey leftSpine rightSpine =>
          have stepBounds := doubleOrientationAt_key_bounds innerOrientation
          omega
      | leftContext innerFocused rightTree =>
          have pivot_le_n : pivot ≤ n := by
            have rightBounds := contextRight.lower_le_upper
            omega
          intro identity created
          have localCreated :=
            Splay.Accounting.WholeSplayTemporaryCreationContext.created_leftContext_local
              snapshot before after contextRight upper_le_n incoming created
          exact
            ih innerFocused flagEq keyEq pivot_le_n _ localCreated
      | rightContext leftTree innerFocused =>
          have focusedBounds := FocusedSpines.key_bounds innerFocused
          have stepBounds := doubleOrientationAt_key_bounds innerOrientation
          omega
  | @rightContext flag depth keyValue lower pivot upper
      contextLeft before after innerOrientation ih =>
      cases focused with
      | atKey leftSpine rightSpine =>
          have stepBounds := doubleOrientationAt_key_bounds innerOrientation
          omega
      | leftContext innerFocused rightTree =>
          have focusedBounds := FocusedSpines.key_bounds innerFocused
          have stepBounds := doubleOrientationAt_key_bounds innerOrientation
          omega
      | rightContext leftTree innerFocused =>
          intro identity created
          have localCreated :=
            Splay.Accounting.WholeSplayTemporaryCreationContext.created_rightContext_local
              snapshot contextLeft before after upper_le_n incoming created
          exact
            ih innerFocused flagEq keyEq upper_le_n _ localCreated

/--
Canonical specialization of the generalized contextual zig-zag
classification at the accessed key.
-/
theorem zigZag_created_subset_baseDeltas
    {n lower upper depth : ℕ}
    (comparison : BST 0 n) (key : Fin n)
    (comparisonRoot : comparison.HasRoot key.val)
    (leftBoundary rightBoundary : External n)
    (ordered :
      leftBoundary < valuePos key ∧ valuePos key < rightBoundary)
    (base : SpineBase key leftBoundary rightBoundary)
    (rightBase_le_n : base.rightUpper ≤ n)
    {before after : BST lower upper}
    (focused :
      FocusedSpines
        (temporarySnapshot comparison key comparisonRoot
          leftBoundary rightBoundary ordered)
        key leftBoundary rightBoundary base before)
    (orientation :
      DoubleOrientationAt false
        (depth := depth) (key := key.val) before after)
    (upper_le_n : upper ≤ n)
    (incoming : Option TernaryBranch) :
    (bendsFrom
        (temporarySnapshot comparison key comparisonRoot
          leftBoundary rightBoundary ordered)
        after upper_le_n incoming \
      bendsFrom
        (temporarySnapshot comparison key comparisonRoot
          leftBoundary rightBoundary ordered)
        before upper_le_n incoming) ⊆
      ((bendsFrom
          (temporarySnapshot comparison key comparisonRoot
            leftBoundary rightBoundary ordered)
          base.leftTree (Nat.le_of_lt key.isLt) (some .right) \
        bendsFrom
          (temporarySnapshot comparison key comparisonRoot
            leftBoundary rightBoundary ordered)
          base.leftTree (Nat.le_of_lt key.isLt) none) ∪
       (bendsFrom
          (temporarySnapshot comparison key comparisonRoot
            leftBoundary rightBoundary ordered)
          base.rightTree rightBase_le_n (some .left) \
        bendsFrom
          (temporarySnapshot comparison key comparisonRoot
            leftBoundary rightBoundary ordered)
          base.rightTree rightBase_le_n none)) := by
  exact
    zigZag_created_subset_baseDeltas_general
      comparison key comparisonRoot leftBoundary rightBoundary ordered
      base rightBase_le_n focused orientation rfl rfl upper_le_n incoming

/--
After removing the two administrative base deltas, one contextual
same-direction double rotation creates at most one endpoint identity.

At the root, the remaining identities are confined to the single freshly
assembled hanging node.  An unchanged search context only transports this
residual set, so the same cardinality bound holds at every depth.
-/
private theorem zigZig_created_sdiff_fixedBaseDeltas_card_le_one_general
    {n lower upper depth keyValue : ℕ} {flag : Bool}
    (comparison : BST 0 n) (key : Fin n)
    (comparisonRoot : comparison.HasRoot key.val)
    (leftBoundary rightBoundary : External n)
    (ordered :
      leftBoundary < valuePos key ∧ valuePos key < rightBoundary)
    (base : SpineBase key leftBoundary rightBoundary)
    (rightBase_le_n : base.rightUpper ≤ n)
    {before after : BST lower upper}
    (focused :
      FocusedSpines
        (temporarySnapshot comparison key comparisonRoot
          leftBoundary rightBoundary ordered)
        key leftBoundary rightBoundary base before)
    (orientation :
      DoubleOrientationAt flag
        (depth := depth) (key := keyValue) before after)
    (flagEq : flag = true)
    (keyEq : keyValue = key.val)
    (upper_le_n : upper ≤ n)
    (incoming : Option TernaryBranch) :
    (((bendsFrom
          (temporarySnapshot comparison key comparisonRoot
            leftBoundary rightBoundary ordered)
          after upper_le_n incoming \
        bendsFrom
          (temporarySnapshot comparison key comparisonRoot
            leftBoundary rightBoundary ordered)
          before upper_le_n incoming) \
      fixedBaseDeltas comparison key comparisonRoot
        leftBoundary rightBoundary ordered base rightBase_le_n).card ≤ 1) := by
  let snapshot :=
    temporarySnapshot comparison key comparisonRoot
      leftBoundary rightBoundary ordered
  induction orientation generalizing incoming with
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
          | leftContext keyFocused cTree =>
              cases keyFocused with
              | atKey leftSpine rightSpine =>
                  have beforeRoot :
                      (({
                        lower := lower
                        root := third
                        upper := upper
                        left := .node (.node a b) c
                        right := d
                        upper_le_n := upper_le_n
                      } : AtNode n).heavyBranch snapshot) = .left := by
                    apply heavyBranch_eq_left_of_key_lt_root
                    · change lower ≤ key.val
                      have aBounds := a.lower_le_upper
                      omega
                    · change key.val < third
                      have bBounds := b.lower_le_upper
                      have cBounds := c.lower_le_upper
                      omega
                  have beforeSecond :
                      (({
                        lower := lower
                        root := second
                        upper := third
                        left := .node a b
                        right := c
                        upper_le_n := by
                          have dBounds := d.lower_le_upper
                          omega
                      } : AtNode n).heavyBranch snapshot) = .left := by
                    apply heavyBranch_eq_left_of_key_lt_root
                    · change lower ≤ key.val
                      have aBounds := a.lower_le_upper
                      omega
                    · change key.val < second
                      have bBounds := b.lower_le_upper
                      omega
                  have beforePromoted :
                      (({
                        lower := lower
                        root := key.val
                        upper := second
                        left := a
                        right := b
                        upper_le_n := by
                          have cBounds := c.lower_le_upper
                          have dBounds := d.lower_le_upper
                          omega
                      } : AtNode n).heavyBranch snapshot) = .middle := by
                    apply heavyBranch_eq_middle_at_key
                    rfl
                  have afterRoot :
                      (({
                        lower := lower
                        root := key.val
                        upper := upper
                        left := a
                        right := .node b (.node c d)
                        upper_le_n := upper_le_n
                      } : AtNode n).heavyBranch snapshot) = .middle := by
                    apply heavyBranch_eq_middle_at_key
                    rfl
                  have afterSecond :
                      (({
                        lower := key.val + 1
                        root := second
                        upper := upper
                        left := b
                        right := .node c d
                        upper_le_n := upper_le_n
                      } : AtNode n).heavyBranch snapshot) = .left := by
                    exact
                      rightSpineGrow_heavy comparison key comparisonRoot
                        leftBoundary rightBoundary ordered base
                        rightSpine (.node c d) upper_le_n
                  apply
                    (Finset.card_le_card ?_).trans
                      (Splay.Accounting.WholeSplayTemporaryCreationPersistence.ZigZigWinnerProvenance.assembledNode_created_over_children_le_one
                        snapshot c d upper_le_n)
                  intro identity residual
                  rcases Finset.mem_sdiff.mp residual with
                    ⟨created, notBase⟩
                  have classified :=
                    zigZigLeft_created_subset_baseAndHangingDeltas
                      snapshot a b c d upper_le_n incoming
                        beforeRoot beforeSecond beforePromoted
                        afterRoot afterSecond created
                  rcases Finset.mem_union.mp classified with
                    baseCreated | hangingCreated
                  · exact
                      False.elim
                        (notBase (by
                          simp only [fixedBaseDeltas]
                          exact
                            Finset.mem_union.mpr
                              (Or.inr
                                (rightSpine_incomingLeftDelta_subset_baseDelta
                                  rightSpine baseCreated))))
                  · exact hangingCreated
              | leftContext innerFocused rightTree =>
                  have bounds := FocusedSpines.key_bounds innerFocused
                  omega
              | rightContext leftTree innerFocused =>
                  have bounds := FocusedSpines.key_bounds innerFocused
                  omega
          | rightContext leftTree innerFocused =>
              have bounds := FocusedSpines.key_bounds innerFocused
              have bBounds := b.lower_le_upper
              omega
      | rightContext leftTree innerFocused =>
          have bounds := FocusedSpines.key_bounds innerFocused
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
      | leftContext innerFocused rightTree =>
          have bounds := FocusedSpines.key_bounds innerFocused
          have bBounds := b.lower_le_upper
          have cBounds := c.lower_le_upper
          omega
      | rightContext contextLeft thirdFocused =>
          cases thirdFocused with
          | atKey leftSpine rightSpine =>
              have cBounds := c.lower_le_upper
              omega
          | leftContext innerFocused rightTree =>
              have bounds := FocusedSpines.key_bounds innerFocused
              have cBounds := c.lower_le_upper
              omega
          | rightContext secondLeft keyFocused =>
              cases keyFocused with
              | atKey leftSpine rightSpine =>
                  have beforeRoot :
                      (({
                        lower := lower
                        root := first
                        upper := upper
                        left := a
                        right := .node b (.node c d)
                        upper_le_n := upper_le_n
                      } : AtNode n).heavyBranch snapshot) = .right := by
                    apply heavyBranch_eq_right_of_root_lt_key
                    · change first < key.val
                      have bBounds := b.lower_le_upper
                      have cBounds := c.lower_le_upper
                      omega
                    · change key.val < upper
                      have dBounds := d.lower_le_upper
                      omega
                  have beforeSecond :
                      (({
                        lower := first + 1
                        root := second
                        upper := upper
                        left := b
                        right := .node c d
                        upper_le_n := upper_le_n
                      } : AtNode n).heavyBranch snapshot) = .right := by
                    apply heavyBranch_eq_right_of_root_lt_key
                    · change second < key.val
                      have cBounds := c.lower_le_upper
                      omega
                    · change key.val < upper
                      have dBounds := d.lower_le_upper
                      omega
                  have beforePromoted :
                      (({
                        lower := second + 1
                        root := key.val
                        upper := upper
                        left := c
                        right := d
                        upper_le_n := upper_le_n
                      } : AtNode n).heavyBranch snapshot) = .middle := by
                    apply heavyBranch_eq_middle_at_key
                    rfl
                  have afterRoot :
                      (({
                        lower := lower
                        root := key.val
                        upper := upper
                        left := .node (.node a b) c
                        right := d
                        upper_le_n := upper_le_n
                      } : AtNode n).heavyBranch snapshot) = .middle := by
                    apply heavyBranch_eq_middle_at_key
                    rfl
                  have second_le_n : second ≤ n := by
                    have cBounds := c.lower_le_upper
                    have keyBound := key.isLt
                    omega
                  have afterSecond :
                      (({
                        lower := lower
                        root := second
                        upper := key.val
                        left := .node a b
                        right := c
                        upper_le_n := Nat.le_of_lt key.isLt
                      } : AtNode n).heavyBranch snapshot) = .right := by
                    exact
                      leftSpineGrow_heavy comparison key comparisonRoot
                        leftBoundary rightBoundary ordered base
                        leftSpine (.node a b) second_le_n
                  apply
                    (Finset.card_le_card ?_).trans
                      (Splay.Accounting.WholeSplayTemporaryCreationPersistence.ZigZigWinnerProvenance.assembledNode_created_over_children_le_one
                        snapshot a b second_le_n)
                  intro identity residual
                  rcases Finset.mem_sdiff.mp residual with
                    ⟨created, notBase⟩
                  have classified :=
                    zigZigRight_created_subset_baseAndHangingDeltas
                      snapshot a b c d upper_le_n incoming
                        beforeRoot beforeSecond beforePromoted
                        afterRoot afterSecond created
                  rcases Finset.mem_union.mp classified with
                    baseCreated | hangingCreated
                  · exact
                      False.elim
                        (notBase (by
                          simp only [fixedBaseDeltas]
                          exact
                            Finset.mem_union.mpr
                              (Or.inl
                                (leftSpine_incomingRightDelta_subset_baseDelta
                                  leftSpine baseCreated))))
                  · exact hangingCreated
              | leftContext innerFocused rightTree =>
                  have bounds := FocusedSpines.key_bounds innerFocused
                  omega
              | rightContext leftTree innerFocused =>
                  have bounds := FocusedSpines.key_bounds innerFocused
                  omega
  | zigZagLeftRight =>
      simp at flagEq
  | zigZagRightLeft =>
      simp at flagEq
  | @leftContext flag depth keyValue lower pivot upper before after
      innerOrientation contextRight ih =>
      cases focused with
      | atKey leftSpine rightSpine =>
          have stepBounds := doubleOrientationAt_key_bounds innerOrientation
          omega
      | leftContext innerFocused rightTree =>
          have pivot_le_n : pivot ≤ n := by
            have rightBounds := contextRight.lower_le_upper
            omega
          let contextNode : AtNode n := {
            lower := lower
            root := pivot
            upper := upper
            left := before
            right := contextRight
            upper_le_n := upper_le_n
          }
          let localIncoming :=
            childIncoming (contextNode.heavyBranch snapshot) .left
          apply
            (Finset.card_le_card ?_).trans
              (ih innerFocused flagEq keyEq pivot_le_n localIncoming)
          intro identity residual
          rcases Finset.mem_sdiff.mp residual with
            ⟨created, notBase⟩
          have localCreated :=
            Splay.Accounting.WholeSplayTemporaryCreationContext.created_leftContext_local
              snapshot before after contextRight upper_le_n incoming created
          change
            identity ∈
              (bendsFrom snapshot after pivot_le_n localIncoming \
                bendsFrom snapshot before pivot_le_n localIncoming)
            at localCreated
          exact Finset.mem_sdiff.mpr ⟨localCreated, notBase⟩
      | rightContext leftTree innerFocused =>
          have focusedBounds := FocusedSpines.key_bounds innerFocused
          have stepBounds := doubleOrientationAt_key_bounds innerOrientation
          omega
  | @rightContext flag depth keyValue lower pivot upper
      contextLeft before after innerOrientation ih =>
      cases focused with
      | atKey leftSpine rightSpine =>
          have stepBounds := doubleOrientationAt_key_bounds innerOrientation
          omega
      | leftContext innerFocused rightTree =>
          have focusedBounds := FocusedSpines.key_bounds innerFocused
          have stepBounds := doubleOrientationAt_key_bounds innerOrientation
          omega
      | rightContext leftTree innerFocused =>
          let contextNode : AtNode n := {
            lower := lower
            root := pivot
            upper := upper
            left := contextLeft
            right := before
            upper_le_n := upper_le_n
          }
          let localIncoming :=
            childIncoming (contextNode.heavyBranch snapshot) .right
          apply
            (Finset.card_le_card ?_).trans
              (ih innerFocused flagEq keyEq upper_le_n localIncoming)
          intro identity residual
          rcases Finset.mem_sdiff.mp residual with
            ⟨created, notBase⟩
          have localCreated :=
            Splay.Accounting.WholeSplayTemporaryCreationContext.created_rightContext_local
              snapshot contextLeft before after upper_le_n incoming created
          change
            identity ∈
              (bendsFrom snapshot after upper_le_n localIncoming \
                bendsFrom snapshot before upper_le_n localIncoming)
            at localCreated
          exact Finset.mem_sdiff.mpr ⟨localCreated, notBase⟩

/--
Canonical same-direction specialization at the accessed key.
-/
theorem zigZig_created_sdiff_fixedBaseDeltas_card_le_one
    {n lower upper depth : ℕ}
    (comparison : BST 0 n) (key : Fin n)
    (comparisonRoot : comparison.HasRoot key.val)
    (leftBoundary rightBoundary : External n)
    (ordered :
      leftBoundary < valuePos key ∧ valuePos key < rightBoundary)
    (base : SpineBase key leftBoundary rightBoundary)
    (rightBase_le_n : base.rightUpper ≤ n)
    {before after : BST lower upper}
    (focused :
      FocusedSpines
        (temporarySnapshot comparison key comparisonRoot
          leftBoundary rightBoundary ordered)
        key leftBoundary rightBoundary base before)
    (orientation :
      DoubleOrientationAt true
        (depth := depth) (key := key.val) before after)
    (upper_le_n : upper ≤ n)
    (incoming : Option TernaryBranch) :
    (((bendsFrom
          (temporarySnapshot comparison key comparisonRoot
            leftBoundary rightBoundary ordered)
          after upper_le_n incoming \
        bendsFrom
          (temporarySnapshot comparison key comparisonRoot
            leftBoundary rightBoundary ordered)
          before upper_le_n incoming) \
      fixedBaseDeltas comparison key comparisonRoot
        leftBoundary rightBoundary ordered base rightBase_le_n).card ≤ 1) := by
  exact
    zigZig_created_sdiff_fixedBaseDeltas_card_le_one_general
      comparison key comparisonRoot leftBoundary rightBoundary ordered
      base rightBase_le_n focused orientation rfl rfl upper_le_n incoming

end AutomaticCanonicalPersistence

namespace ChronologicalProvenanceBridge

/--
The genuinely geometric residue after first-creation chronology has been
made automatic.

It is enough to prove that endpoint identities whose first source is a zig
or zig-zag are one of the two base attachments.  First sources of the third
kind are automatically converted to chronological zig-zig winners.  The
last field is the independent local fact that one concrete zig-zig has at
most one nonattachment endpoint winner.
-/
structure FirstSourceProvenance
    {n key : ℕ} {before after : BST 0 n}
    {execution : SplayExecution key before after}
    (transcript : SplayExecutionTranscriptWitness execution)
    (snapshot : Snapshot n)
    (attachment :
      Fin 2 →
        Option
          (CreatedIdentity
            (before := before) (after := after) snapshot)) : Type where
  zig_first_is_attachment :
    ∀ (identity :
        CreatedIdentity (before := before) (after := after) snapshot)
      {stepBefore stepAfter : BST 0 n},
      FirstCreationAt snapshot identity.val transcript.transcript .zig
        stepBefore stepAfter none →
      ∃ side, attachment side = some identity
  zigZag_first_is_attachment :
    ∀ (identity :
        CreatedIdentity (before := before) (after := after) snapshot)
      {stepBefore stepAfter : BST 0 n} {depth : ℕ},
      FirstCreationAt snapshot identity.val transcript.transcript .zigZag
        stepBefore stepAfter (some depth) →
      ∃ side, attachment side = some identity
  one_per_zigZig :
    ∀ slot : Fin transcript.zigZig,
      (persistentCreatedAt transcript snapshot slot \
        attachmentSet attachment).card ≤ 1

namespace FirstSourceProvenance

/--
First-source trichotomy turns the residue above into the finite-set
decomposition expected by `FinalSpinePersistence`.  No separate coverage
premise remains: the zig-zig branch is supplied by
`FirstCreationAt.exists_endpointPersistentWinnerAt_of_zigZig`.
-/
noncomputable def toFinalSpineSetDecomposition
    {n key : ℕ} {before after : BST 0 n}
    {execution : SplayExecution key before after}
    {transcript : SplayExecutionTranscriptWitness execution}
    {snapshot : Snapshot n}
    {attachment :
      Fin 2 →
        Option
          (CreatedIdentity
            (before := before) (after := after) snapshot)}
    (provenance :
      FirstSourceProvenance transcript snapshot attachment)
    (attachment_side :
      ∀ (side : Fin 2)
        (identity :
          CreatedIdentity (before := before) (after := after) snapshot),
        attachment side = some identity →
          if side.val = 0 then identity.val.val < key
          else key < identity.val.val) :
    FinalSpineSetDecomposition transcript snapshot := by
  classical
  refine
    { attachment := attachment
      attachment_side := attachment_side
      cover := ?_
      one_per_slot := provenance.one_per_zigZig }
  intro identity outside
  have notInAttachment :
      identity ∉ attachmentSet attachment :=
    (Finset.mem_sdiff.mp outside).2
  have notAttached :
      ¬ ∃ side, attachment side = some identity := by
    simpa only [mem_attachmentSet_iff] using notInAttachment
  rcases
      createdIdentity_firstCreation_cases
        transcript.transcript snapshot identity with
    ⟨stepBefore, stepAfter, first⟩ |
      ⟨⟨stepBefore, stepAfter, depth, first⟩ |
        ⟨stepBefore, stepAfter, depth, first⟩⟩
  · exact False.elim
      (notAttached
        (provenance.zig_first_is_attachment identity first))
  · obtain ⟨slot, winner⟩ :=
      first.exists_endpointPersistentWinnerAt_of_zigZig
        transcript snapshot identity
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
    exact
      ⟨slot, Finset.mem_sdiff.mpr
        ⟨mem_persistentCreatedAt_iff.mpr winner,
          notInAttachment⟩⟩
  · exact False.elim
      (notAttached
        (provenance.zigZag_first_is_attachment identity first))

/-- Direct proof-relevant persistence constructor from first-source data. -/
noncomputable def toFinalSpinePersistence
    {n key : ℕ} {before after : BST 0 n}
    {execution : SplayExecution key before after}
    {transcript : SplayExecutionTranscriptWitness execution}
    {snapshot : Snapshot n}
    {attachment :
      Fin 2 →
        Option
          (CreatedIdentity
            (before := before) (after := after) snapshot)}
    (provenance :
      FirstSourceProvenance transcript snapshot attachment)
    (attachment_side :
      ∀ (side : Fin 2)
        (identity :
          CreatedIdentity (before := before) (after := after) snapshot),
        attachment side = some identity →
          if side.val = 0 then identity.val.val < key
          else key < identity.val.val) :
    FinalSpinePersistence transcript snapshot :=
  FinalSpineSetDecomposition.toFinalSpinePersistence
    (provenance.toFinalSpineSetDecomposition attachment_side)

end FirstSourceProvenance

end ChronologicalProvenanceBridge

namespace FinalSpineEndpointDecomposition

open Splay.Accounting.WholeSplayTemporaryFinalSpineAttachments

/--
Once the final left spine is known to be nontrivial, membership in the fixed
left-base incoming delta is exactly enough to identify the canonical slot
zero attachment.
-/
theorem attachment_zero_eq_some_of_baseDelta
    {n key baseLower baseUpper : ℕ}
    {before : BST 0 n} {snapshot : Snapshot n}
    {leftBase : BST baseLower key}
    {rightBase : BST (key + 1) baseUpper}
    {left : BST 0 key}
    {right : BST (key + 1) n}
    (leftSpine : LeftSpine snapshot leftBase left)
    (rightSpine : RightSpine snapshot rightBase right)
    (identity :
      CreatedIdentity
        (before := before) (after := .node left right) snapshot)
    (incoming :
      Splay.Accounting.WholeSplayTemporaryFinalSpineBends.LeftSpine.incomingAtBase
        leftSpine = some .right)
    (delta :
      identity.val ∈
        (bendsFrom snapshot leftBase leftSpine.base_le_n (some .right) \
          bendsFrom snapshot leftBase leftSpine.base_le_n none)) :
    WholeSplayTemporaryFinalSpineAttachments.attachment
        leftSpine rightSpine ⟨0, by omega⟩ =
      some identity := by
  apply attachment_zero_eq_some_of_mem_left leftSpine rightSpine
  apply mem_leftCandidates_iff.mpr
  simpa only [incoming] using delta

/--
Symmetric slot-one realization for the fixed right-base incoming delta.
-/
theorem attachment_one_eq_some_of_baseDelta
    {n key baseLower baseUpper : ℕ}
    {before : BST 0 n} {snapshot : Snapshot n}
    {leftBase : BST baseLower key}
    {rightBase : BST (key + 1) baseUpper}
    {left : BST 0 key}
    {right : BST (key + 1) n}
    (leftSpine : LeftSpine snapshot leftBase left)
    (rightSpine : RightSpine snapshot rightBase right)
    (identity :
      CreatedIdentity
        (before := before) (after := .node left right) snapshot)
    (incoming :
      Splay.Accounting.WholeSplayTemporaryFinalSpineBends.RightSpine.incomingAtBase
        rightSpine = some .left)
    (delta :
      identity.val ∈
        (bendsFrom snapshot rightBase rightSpine.base_le_n (some .left) \
          bendsFrom snapshot rightBase rightSpine.base_le_n none)) :
    WholeSplayTemporaryFinalSpineAttachments.attachment
        leftSpine rightSpine ⟨1, by omega⟩ =
      some identity := by
  apply attachment_one_eq_some_of_mem_right leftSpine rightSpine
  apply mem_rightCandidates_iff.mpr
  simpa only [incoming] using delta

/-- The canonical two attachment slots extracted from an end-to-end
two-spine witness. -/
noncomputable def attachment
    {n : ℕ} {snapshot : Snapshot n} {key : Fin n}
    {leftBoundary rightBoundary : External n}
    {before after : BST 0 n}
    (spines :
      ExecutionTwoSpines snapshot key leftBoundary rightBoundary
        before after) :
    Fin 2 →
      Option
        (CreatedIdentity
          (before := before) (after := after) snapshot) :=
  match spines.finalSpines with
  | .atRoot leftSpine rightSpine =>
      WholeSplayTemporaryFinalSpineAttachments.attachment
        (before := before) leftSpine rightSpine

/-- The two non-base components of the final monotone spines. -/
noncomputable def hangingBends
    {n : ℕ} {snapshot : Snapshot n} {key : Fin n}
    {leftBoundary rightBoundary : External n}
    {before after : BST 0 n}
    (spines :
      ExecutionTwoSpines snapshot key leftBoundary rightBoundary
        before after) : Finset (Fin n) :=
  match spines.finalSpines with
  | .atRoot leftSpine rightSpine =>
      leftSpine.hangingBends ∪ rightSpine.hangingBends

/--
After the two canonical base attachments are removed, every endpoint-created
identity lies in a hanging component of one of the final spines.

The immutable `BaseFocus` zipper is essential here: it shows that a bend
already present in either base with no incoming edge belonged to the initial
whole-tree bend set and therefore cannot be endpoint-created.
-/
theorem notAttachment_mem_hangingBends
    {n : ℕ} (comparison : BST 0 n) (key : Fin n)
    (comparisonRoot : comparison.HasRoot key.val)
    (leftBoundary rightBoundary : External n)
    (ordered :
      leftBoundary < valuePos key ∧ valuePos key < rightBoundary)
    {before after : BST 0 n}
    (spines :
      ExecutionTwoSpines
        (temporarySnapshot comparison key comparisonRoot
          leftBoundary rightBoundary ordered)
        key leftBoundary rightBoundary before after)
    (identity :
      CreatedIdentity
        (before := before) (after := after)
        (temporarySnapshot comparison key comparisonRoot
          leftBoundary rightBoundary ordered))
    (notAttached :
      ¬ ∃ side, attachment spines side = some identity) :
    identity.val ∈ hangingBends spines := by
  let snapshot :=
    temporarySnapshot comparison key comparisonRoot
      leftBoundary rightBoundary ordered
  cases spines with
  | mk base baseFocus finalSpines =>
      cases finalSpines with
      | @atRoot leftTree rightTree leftSpine rightSpine =>
          let raw : Fin n := identity.val
          have finalMember :
              raw ∈ bends snapshot (.node leftTree rightTree) := by
            simpa only [raw] using
            (Finset.mem_sdiff.mp identity.property).1
          have decomposed :
              raw ∈
                (bendsFrom snapshot base.leftTree leftSpine.base_le_n
                    (Splay.Accounting.WholeSplayTemporaryFinalSpineBends.LeftSpine.incomingAtBase
                      leftSpine) ∪
                  leftSpine.hangingBends) ∪
                (bendsFrom snapshot base.rightTree rightSpine.base_le_n
                    (Splay.Accounting.WholeSplayTemporaryFinalSpineBends.RightSpine.incomingAtBase
                      rightSpine) ∪
                  rightSpine.hangingBends) := by
            rw [←
              Splay.Accounting.WholeSplayTemporaryFinalSpineBends.temporaryFinalRoot_bends_eq
                comparison key comparisonRoot leftBoundary rightBoundary
                ordered leftSpine rightSpine]
            exact finalMember
          simp only [Finset.mem_union] at decomposed
          rcases decomposed with
              (inLeftBase | inLeftHanging) |
              (inRightBase | inRightHanging)
          · by_cases inOriginal :
                raw ∈
                  bendsFrom snapshot base.leftTree
                    leftSpine.base_le_n none
            · have initialMember :
                  raw ∈ bends snapshot before := by
                apply baseFocus.leftBase_bends_subset_bends
                simpa only using inOriginal
              exact False.elim
                ((Finset.mem_sdiff.mp identity.property).2 (by
                  simpa only [raw] using initialMember))
            · have candidate :
                  identity ∈
                    leftCandidates
                      (before := before) leftSpine rightSpine := by
                exact mem_leftCandidates_iff.mpr
                  (by
                    simpa only [raw] using
                      (Finset.mem_sdiff.mpr
                        ⟨inLeftBase, inOriginal⟩))
              apply False.elim
              apply notAttached
              refine ⟨(⟨0, by omega⟩ : Fin 2), ?_⟩
              exact
                attachment_zero_eq_some_of_mem_left
                  leftSpine rightSpine candidate
          · exact Finset.mem_union.mpr (Or.inl inLeftHanging)
          · by_cases inOriginal :
                raw ∈
                  bendsFrom snapshot base.rightTree
                    rightSpine.base_le_n none
            · have initialMember :
                  raw ∈ bends snapshot before := by
                apply baseFocus.rightBase_bends_subset_bends
                simpa only using inOriginal
              exact False.elim
                ((Finset.mem_sdiff.mp identity.property).2 (by
                  simpa only [raw] using initialMember))
            · have candidate :
                  identity ∈
                    rightCandidates
                      (before := before) leftSpine rightSpine := by
                exact mem_rightCandidates_iff.mpr
                  (by
                    simpa only [raw] using
                      (Finset.mem_sdiff.mpr
                        ⟨inRightBase, inOriginal⟩))
              apply False.elim
              apply notAttached
              refine ⟨(⟨1, by omega⟩ : Fin 2), ?_⟩
              exact
                attachment_one_eq_some_of_mem_right
                  leftSpine rightSpine candidate
          · exact Finset.mem_union.mpr (Or.inr inRightHanging)

end FinalSpineEndpointDecomposition

/-!
The checked canonical example below records why attachment identities must
be excluded from `FinalSpinePersistence.winner_unique`.  A single LL
zig-zig creates two endpoint bends on the final right side.  The bend at
key `1` is the incoming-edge delta of the original right child, while the
bend at key `6` lies in the newly assembled hanging subtree and is the
genuine zig-zig winner.
-/

namespace UnconditionalWinnerUniquenessCounterexample

abbrev E0 : BST 0 0 := .empty 0
abbrev E1 : BST 1 1 := .empty 1
abbrev E2 : BST 2 2 := .empty 2
abbrev E3 : BST 3 3 := .empty 3
abbrev E4 : BST 4 4 := .empty 4
abbrev E5 : BST 5 5 := .empty 5
abbrev E6 : BST 6 6 := .empty 6
abbrev E7 : BST 7 7 := .empty 7

abbrev one : BST 1 2 := .node E1 E2
abbrev oneTwo : BST 1 3 := .node E1 (.node E2 E3)
abbrev four : BST 4 5 := .node E4 E5
abbrev five : BST 5 6 := .node E5 E6
abbrev six : BST 6 7 := .node E6 E7
abbrev fiveSix : BST 4 7 := .node four six
abbrev comparisonThreeRight : BST 3 7 :=
  .node E3 fiveSix
abbrev comparisonRight : BST 1 7 :=
  .node one comparisonThreeRight

/-- Serving tree rooted at the accessed key `0`. -/
abbrev comparison : BST 0 7 :=
  .node E0 comparisonRight

abbrev zeroToThree : BST 0 3 :=
  .node E0 oneTwo
abbrev zeroToFour : BST 0 4 :=
  .node zeroToThree E4
abbrev fiveToSeven : BST 5 7 :=
  .node five E7

/-- The accessed key is the left-left grandchild of the root. -/
abbrev before : BST 0 7 :=
  .node zeroToFour fiveToSeven

abbrev fourToSeven : BST 4 7 :=
  .node E4 fiveToSeven

/-- Result of the unique root LL zig-zig. -/
abbrev after : BST 0 7 :=
  .node E0 (.node oneTwo fourToSeven)

abbrev key : Fin 7 := ⟨0, by omega⟩
abbrev left : External 7 := ⟨0, by omega⟩
abbrev right : External 7 := ⟨5, by omega⟩
abbrev farRight : External 7 := ⟨11, by omega⟩

theorem comparison_hasRoot : comparison.HasRoot key.val :=
  ⟨E0, comparisonRight, rfl⟩

theorem ordered :
    left < valuePos key ∧ valuePos key < right := by
  simp [left, right, key, valuePos]

/--
The temporary positions are the genuine minima of the two actual child
intervals of `key` in `before`: `[0,0]` and `[2,6]` in external order.
-/
abbrev comparisonSnapshot : Snapshot 7 :=
  Snapshot.ofTree comparison

theorem left_child_minimum :
    IsIntervalMin comparisonSnapshot.rank
      (⟨0, by omega⟩ : External 7)
      (⟨0, by omega⟩ : External 7) left := by
  refine ⟨by simp [left], by simp [left], ?_⟩
  intro element lower upper
  have value : element.val = 0 := by
    change 0 ≤ element.val at lower
    change element.val ≤ 0 at upper
    omega
  have equal : element = left := by
    apply Fin.ext
    simpa [left] using value
  subst element
  exact Nat.le_refl _

theorem right_child_minimum :
    IsIntervalMin comparisonSnapshot.rank
      (⟨2, by omega⟩ : External 7)
      (⟨6, by omega⟩ : External 7) right := by
  refine ⟨by simp [right], by simp [right], ?_⟩
  intro element elementLower elementUpper
  change externalDepth comparison 5 ≤
    externalDepth comparison element.val
  rw [externalDepth_node_of_root_lt E0 comparisonRight (by omega)]
  rw [externalDepth_root]
  rw [externalDepth_node_of_root_lt E0 comparisonRight (by
    change 2 ≤ element.val at elementLower
    omega)]
  omega

/--
A fully explicit boundary selection witnessing that `left` and `right` are
the canonical child-subtree minima, not merely ordered artificial points.
-/
def childBoundarySelection :
    BoundaryMinimumSelection comparisonSnapshot key where
  left := left
  right := right
  ordered := ordered
  leftLower := ⟨0, by omega⟩
  leftUpper := ⟨0, by omega⟩
  leftMinimum := left_child_minimum
  leftNeighbor_mem := by simp [key, leftNullPos]
  rightLower := ⟨2, by omega⟩
  rightUpper := ⟨6, by omega⟩
  rightMinimum := right_child_minimum
  rightNeighbor_mem := by simp [key, rightNullPos]

abbrev snapshot : Snapshot 7 :=
  temporarySnapshot comparison key comparison_hasRoot
    left right ordered

/-- The sole splay step. -/
theorem step : DoubleRotationAt 0 key.val before after :=
  .root (.zigZigLeft E0 oneTwo E4 fiveToSeven)

theorem orientation :
    DoubleOrientationAt true
      (depth := 0) (key := key.val) before after :=
  .zigZigLeft E0 oneTwo E4 fiveToSeven

theorem after_hasRoot : after.HasRoot key.val :=
  ⟨E0, .node oneTwo fourToSeven, rfl⟩

theorem execution : SplayExecution key.val before after :=
  .next (.double step) (.done after_hasRoot)

theorem explicitTranscript :
    SplayExecutionTranscript key.val execution
      [.zigZig] 0 1 0 :=
  .zigZig step orientation
    (.done after_hasRoot)
    (.done after_hasRoot)

def transcriptWitness :
    SplayExecutionTranscriptWitness execution where
  kinds := [.zigZig]
  zig := 0
  zigZig := 1
  zigZag := 0
  transcript := explicitTranscript

abbrev nodeAt
    {lower pivot upper : ℕ}
    (leftSubtree : BST lower pivot)
    (rightSubtree : BST (pivot + 1) upper)
    (upper_le : upper ≤ 7) : AtNode 7 where
  lower := lower
  root := pivot
  upper := upper
  left := leftSubtree
  right := rightSubtree
  upper_le_n := upper_le

private theorem heavyBranch_eq_of_min
    {lower pivot upper : ℕ}
    (leftSubtree : BST lower pivot)
    (rightSubtree : BST (pivot + 1) upper)
    (upper_le : upper ≤ 7)
    (candidate : External 7)
    (minimum :
      IsIntervalMin snapshot.rank
        ⟨2 * lower, by
          have := leftSubtree.lower_le_upper
          have := rightSubtree.lower_le_upper
          omega⟩
        ⟨2 * upper, by omega⟩ candidate)
    (branch : TernaryBranch)
    (contains : branch.Contains pivot candidate.val) :
    (nodeAt leftSubtree rightSubtree upper_le).heavyBranch snapshot =
      branch := by
  let node := nodeAt leftSubtree rightSubtree upper_le
  have minimum' :
      IsIntervalMin snapshot.rank
        node.wholeLower node.wholeUpper candidate := by
    simpa [node, nodeAt, AtNode.wholeLower, AtNode.wholeUpper] using
      minimum
  have heavy :
      snapshot.IsHeavyBranch
        node.wholeLower node.wholeUpper pivot branch :=
    ⟨candidate, minimum', contains⟩
  exact
    (snapshot.heavyBranch_unique
      node.wholeLower node.wholeUpper node.whole_nonempty
      pivot heavy).symm

private theorem key_min
    (lower upper : External 7)
    (inside : lower ≤ valuePos key ∧ valuePos key ≤ upper) :
    IsIntervalMin snapshot.rank lower upper (valuePos key) :=
  valuePos_isIntervalMin comparison key comparison_hasRoot
    left right lower upper ordered inside

private theorem right_min
    (lower upper : External 7)
    (inside : lower ≤ right ∧ right ≤ upper)
    (rightSide : valuePos key < lower) :
    IsIntervalMin snapshot.rank lower upper right :=
  right_isIntervalMin comparison key comparison_hasRoot
    left right lower upper ordered inside rightSide

private theorem farRight_comparison_min
    (lower upper : External 7)
    (lowerBound : 8 ≤ lower.val)
    (inside : lower ≤ farRight ∧ farRight ≤ upper) :
    IsIntervalMin comparisonSnapshot.rank lower upper farRight := by
  refine ⟨inside.1, inside.2, ?_⟩
  intro element elementLower elementUpper
  have elementBound : 8 ≤ element.val := by
    change lower.val ≤ element.val at elementLower
    omega
  change externalDepth comparison 11 ≤
    externalDepth comparison element.val
  simp only [comparison, comparisonRight, comparisonThreeRight,
    fiveSix, one, four, six]
  rw [externalDepth_node_of_root_lt E0
    (.node one (.node E3 (.node four six))) (by omega)]
  rw [externalDepth_node_of_root_lt one
    (.node E3 (.node four six)) (by omega)]
  rw [externalDepth_node_of_root_lt E3 (.node four six) (by omega)]
  rw [externalDepth_root]
  rw [externalDepth_node_of_root_lt E0
    (.node one (.node E3 (.node four six))) (by omega)]
  rw [externalDepth_node_of_root_lt one
    (.node E3 (.node four six)) (by omega)]
  rw [externalDepth_node_of_root_lt E3 (.node four six) (by
    omega)]
  omega

private theorem farRight_min
    (lower upper : External 7)
    (lowerBound : 8 ≤ lower.val)
    (inside : lower ≤ farRight ∧ farRight ≤ upper) :
    IsIntervalMin snapshot.rank lower upper farRight := by
  refine ⟨inside.1, inside.2, ?_⟩
  intro element elementLower elementUpper
  have elementBound : 8 ≤ element.val := by
    change lower.val ≤ element.val at elementLower
    omega
  rw [temporarySnapshot_rank,
    twoBoundaryTemporaryRank_eq_truePriority
      comparisonSnapshot left right farRight (by
        constructor <;> intro equal <;>
          have values := congrArg Fin.val equal <;> simp [left, right,
            farRight] at values),
    twoBoundaryTemporaryRank_eq_truePriority
      comparisonSnapshot left right element (by
        constructor <;> intro equal <;>
          subst element <;> simp [left, right] at elementBound)]
  simp only [truePriority]
  exact Nat.mul_le_mul_left 2
    ((farRight_comparison_min lower upper lowerBound inside).2.2
      element elementLower elementUpper)

theorem before_four_heavy :
    (nodeAt zeroToFour fiveToSeven (by omega)).heavyBranch snapshot =
      .left := by
  apply heavyBranch_eq_of_min (candidate := valuePos key)
  · apply key_min
    simp [key, valuePos]
  · simp [TernaryBranch.Contains, key, valuePos]

theorem before_three_heavy :
    (nodeAt zeroToThree E4 (by omega)).heavyBranch snapshot =
      .left := by
  apply heavyBranch_eq_of_min (candidate := valuePos key)
  · apply key_min
    simp [key, valuePos]
  · simp [TernaryBranch.Contains, key, valuePos]

theorem zero_heavy :
    (nodeAt E0 oneTwo (by omega)).heavyBranch snapshot =
      .middle := by
  apply heavyBranch_eq_of_min (candidate := valuePos key)
  · apply key_min
    simp [key, valuePos]
  · simp [TernaryBranch.Contains, key, valuePos]

theorem one_heavy :
    (nodeAt E1 (.node E2 E3) (by omega)).heavyBranch snapshot =
      .right := by
  apply heavyBranch_eq_of_min (candidate := right)
  · apply right_min
    · simp [right]
    · simp [key, right, valuePos]
  · simp [TernaryBranch.Contains, right]

theorem two_heavy :
    (nodeAt E2 E3 (by omega)).heavyBranch snapshot =
      .middle := by
  apply heavyBranch_eq_of_min (candidate := right)
  · apply right_min
    · simp [right]
    · simp [key, right, valuePos]
  · simp [TernaryBranch.Contains, right]

theorem six_heavy :
    (nodeAt five E7 (by omega)).heavyBranch snapshot =
      .left := by
  apply heavyBranch_eq_of_min (candidate := farRight)
  · apply farRight_min
    · simp
    · simp [farRight]
  · simp [TernaryBranch.Contains, farRight]

theorem five_heavy :
    (nodeAt E5 E6 (by omega)).heavyBranch snapshot =
      .middle := by
  apply heavyBranch_eq_of_min (candidate := farRight)
  · apply farRight_min
    · simp
    · simp [farRight]
  · simp [TernaryBranch.Contains, farRight]

theorem bends_before :
    bends snapshot before = ∅ := by
  simp [bends, bendsFrom, before, zeroToFour, zeroToThree,
    oneTwo, fiveToSeven, five,
    before_four_heavy, before_three_heavy, zero_heavy,
    one_heavy, two_heavy, six_heavy, five_heavy,
    bendAt, Turns, childIncoming]

theorem after_three_heavy :
    (nodeAt oneTwo fourToSeven (by omega)).heavyBranch snapshot =
      .left := by
  apply heavyBranch_eq_of_min (candidate := right)
  · apply right_min
    · simp [right]
    · simp [key, right, valuePos]
  · simp [TernaryBranch.Contains, right]

theorem after_zero_heavy :
    (nodeAt E0 (.node oneTwo fourToSeven) (by omega)).heavyBranch
      snapshot = .middle := by
  apply heavyBranch_eq_of_min (candidate := valuePos key)
  · apply key_min
    simp [key, valuePos]
  · simp [TernaryBranch.Contains, key, valuePos]

theorem after_four_heavy :
    (nodeAt E4 fiveToSeven (by omega)).heavyBranch snapshot =
      .right := by
  apply heavyBranch_eq_of_min (candidate := farRight)
  · apply farRight_min
    · simp
    · simp [farRight]
  · simp [TernaryBranch.Contains, farRight]

theorem bends_after :
    bends snapshot after =
      {(⟨1, by omega⟩ : Fin 7), (⟨6, by omega⟩ : Fin 7)} := by
  simp [bends, bendsFrom, after, oneTwo, fourToSeven,
    fiveToSeven, five,
    after_zero_heavy, after_three_heavy, one_heavy, two_heavy,
    after_four_heavy, six_heavy, five_heavy,
    bendAt, Turns, childIncoming]

def createdOne :
    CreatedIdentity (before := before) (after := after) snapshot :=
  ⟨⟨1, by omega⟩, by simp [bends_before, bends_after]⟩

def createdSix :
    CreatedIdentity (before := before) (after := after) snapshot :=
  ⟨⟨6, by omega⟩, by simp [bends_before, bends_after]⟩

abbrev onlySlot : Fin transcriptWitness.zigZig :=
  ⟨0, by simp [transcriptWitness]⟩

theorem soleOccurrence :
    ZigZigOrdinalAt transcriptWitness.transcript onlySlot.val
      before after 0 :=
  .here step orientation (.done after_hasRoot) (.done after_hasRoot)

theorem createdOne_isWinner :
    EndpointPersistentWinnerAt transcriptWitness snapshot
      createdOne onlySlot := by
  exact ⟨before, after, 0, soleOccurrence, createdOne.property⟩

theorem createdSix_isWinner :
    EndpointPersistentWinnerAt transcriptWitness snapshot
      createdSix onlySlot := by
  exact ⟨before, after, 0, soleOccurrence, createdSix.property⟩

/--
The old, unconditional form of `winner_unique` is false even for this
canonical one-zig-zig execution.  Attachments must be excluded from the
uniqueness quantifier.
-/
theorem not_unconditionalWinnerUnique :
    ¬(∀ {slot : Fin transcriptWitness.zigZig}
        {first second :
          CreatedIdentity (before := before) (after := after) snapshot},
      EndpointPersistentWinnerAt transcriptWitness snapshot first slot →
      EndpointPersistentWinnerAt transcriptWitness snapshot second slot →
        first = second) := by
  intro uniqueness
  have equal :
      createdOne = createdSix :=
    uniqueness
      createdOne_isWinner createdSix_isWinner
  have values := congrArg (fun identity => identity.val.val) equal
  norm_num [createdOne, createdSix] at values

private def attachment :
    Fin 2 →
      Option
        (CreatedIdentity (before := before) (after := after) snapshot) :=
  fun side =>
    if side.val = 1 then some createdOne else none

private theorem created_eq_one_or_six
    (identity :
      CreatedIdentity (before := before) (after := after) snapshot) :
    identity = createdOne ∨ identity = createdSix := by
  let raw : Fin 7 := identity.val
  have member :
      raw ∈ bends snapshot after :=
    (Finset.mem_sdiff.mp identity.property).1
  rw [bends_after] at member
  simp only [Finset.mem_insert, Finset.mem_singleton] at member
  rcases member with atOne | atSix
  · left
    apply Subtype.ext
    exact atOne
  · right
    apply Subtype.ext
    exact atSix

private theorem notAttached_eq_createdSix
    (identity :
      CreatedIdentity (before := before) (after := after) snapshot)
    (notAttached :
      ¬ ∃ side, attachment side = some identity) :
    identity = createdSix := by
  rcases created_eq_one_or_six identity with atOne | atSix
  · exfalso
    apply notAttached
    refine ⟨(⟨1, by omega⟩ : Fin 2), ?_⟩
    simp [attachment, atOne]
  · exact atSix

/--
After excluding attachments from winner uniqueness, the same checked example
does admit the geometric classification: key `1` is the right-base
attachment and key `6` is the sole LL hanging-subtree winner.
-/
def correctedPersistence :
    FinalSpinePersistence transcriptWitness snapshot where
  attachment := attachment
  attachment_side := by
    intro side identity attached
    fin_cases side
    · simp [attachment] at attached
    · simp [attachment] at attached
      subst identity
      simp [key, createdOne]
  winner_of_not_attachment := by
    intro identity notAttached
    have atSix := notAttached_eq_createdSix identity notAttached
    subst identity
    exact ⟨onlySlot, createdSix_isWinner⟩
  winner_unique := by
    intro slot first second firstNotAttached secondNotAttached
      firstWinner secondWinner
    exact
      (notAttached_eq_createdSix first firstNotAttached).trans
        (notAttached_eq_createdSix second secondNotAttached).symm

end UnconditionalWinnerUniquenessCounterexample

/--
The empty complete-splay transcript has an automatic persistence
classification for every snapshot.  This is the base case required by a
future two-spine induction.
-/
theorem nonempty_finalSpinePersistence_done
    {n key : ℕ} {tree : BST 0 n}
    (root : tree.HasRoot key)
    (snapshot : Snapshot n)
    (transcript :
      SplayExecutionTranscriptWitness
        (SplayExecution.done root)) :
    Nonempty (FinalSpinePersistence transcript snapshot) := by
  refine ⟨
    { attachment := fun _ => none
      attachment_side := ?_
      winner_of_not_attachment := ?_
      winner_unique := ?_ }⟩
  · intro side identity attached
    simp at attached
  · intro identity notAttached
    have impossible := identity.property
    simp at impossible
  · intro slot first second firstNotAttached secondNotAttached
      firstWinner secondWinner
    have impossible := first.property
    simp at impossible

/-- Chosen constructor form of `nonempty_finalSpinePersistence_done`. -/
noncomputable def finalSpinePersistence_done
    {n key : ℕ} {tree : BST 0 n}
    (root : tree.HasRoot key)
    (snapshot : Snapshot n)
    (transcript :
      SplayExecutionTranscriptWitness
        (SplayExecution.done root)) :
    FinalSpinePersistence transcript snapshot :=
  Classical.choice
    (nonempty_finalSpinePersistence_done root snapshot transcript)

end Splay.Accounting.WholeSplayTemporaryCreationPersistence
