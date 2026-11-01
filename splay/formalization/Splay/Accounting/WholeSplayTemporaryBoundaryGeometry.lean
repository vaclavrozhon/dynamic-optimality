import Splay.Accounting.WholeSplayTemporaryPriorityReduction

namespace Splay.Accounting.WholeSplayTemporaryBoundaryGeometry

open Splay.Rank
open Splay.Tree
open Splay.Tree.BST
open Splay.Lazy.Canonical
open Splay.Accounting.LocalBendGeometry
open Splay.Accounting.JunctionBendReduction
open Splay.Accounting.WholeSplayTemporaryPriorityReduction

/--
A proof-relevant focus on the unique occurrence of `key` in an
interval-indexed BST.

The terminal constructor exposes exactly the two child subtrees of the
accessed node.  The context constructors remember how that node is embedded
in the original tree; no unindexed search-tree decomposition is assumed.
-/
inductive KeyFocus (key : ℕ) :
    {lower upper : ℕ} → BST lower upper → Type
  | root {lower upper : ℕ}
      (left : BST lower key) (right : BST (key + 1) upper) :
      KeyFocus key (.node left right)
  | leftContext {lower root upper : ℕ}
      {left : BST lower root}
      (focus : KeyFocus key left)
      (right : BST (root + 1) upper) :
      KeyFocus key (.node left right)
  | rightContext {lower root upper : ℕ}
      (left : BST lower root)
      {right : BST (root + 1) upper}
      (focus : KeyFocus key right) :
      KeyFocus key (.node left right)

namespace KeyFocus

/-- The focused key lies in the interval indexed by the surrounding tree. -/
theorem key_bounds
    {key lower upper : ℕ} {tree : BST lower upper}
    (focus : KeyFocus key tree) :
    lower ≤ key ∧ key < upper := by
  induction focus with
  | root left right =>
      exact
        ⟨left.lower_le_upper, by
          have bounds := right.lower_le_upper
          omega⟩
  | leftContext focus right ih =>
      exact
        ⟨ih.1, by
          have bounds := right.lower_le_upper
          omega⟩
  | rightContext left focus ih =>
      exact
        ⟨by
          have bounds := left.lower_le_upper
          omega,
          ih.2⟩

/-- Every key in the indexed interval has a canonical proof-relevant focus. -/
noncomputable def ofBounds
    {key lower upper : ℕ} (tree : BST lower upper)
    (lower_le_key : lower ≤ key) (key_lt_upper : key < upper) :
    KeyFocus key tree := by
  induction tree with
  | empty boundary =>
      omega
  | @node lower root upper left right ihLeft ihRight =>
      by_cases equal : key = root
      · subst key
        exact .root left right
      · by_cases inLeft : key < root
        · exact .leftContext
            (ihLeft lower_le_key inLeft) right
        · have inRight : root + 1 ≤ key := by omega
          exact .rightContext left
            (ihRight inRight key_lt_upper)

/-- Every value key of a complete `n`-key tree has a focus. -/
noncomputable def ofFin {n : ℕ} (tree : BST 0 n) (key : Fin n) :
    KeyFocus key.val tree :=
  ofBounds tree (Nat.zero_le _) key.isLt

/--
The child-subtree interval minima at a focused key are the manuscript's
canonical boundary choices `x⁻` and `x⁺`.

The adjacent nulls are literally the upper endpoint of the left child
interval and the lower endpoint of the right child interval.
-/
private noncomputable def boundaryMinimumSelectionRaw
    {n lower upper : ℕ} (snapshot : Snapshot n)
    (tree : BST lower upper) (upper_le_n : upper ≤ n)
    (key : Fin n) (focus : KeyFocus key.val tree) :
    BoundaryMinimumSelection snapshot key := by
  induction focus with
  | @root lower upper left right =>
      have left_le_n : key.val ≤ n := by
        have bounds := right.lower_le_upper
        omega
      let leftLower := subtreeLower left left_le_n
      let leftUpper := subtreeUpper left left_le_n
      let rightLower := subtreeLower right upper_le_n
      let rightUpper := subtreeUpper right upper_le_n
      let leftMinimum :=
        subtreeOwner snapshot left left_le_n
      let rightMinimum :=
        subtreeOwner snapshot right upper_le_n
      have leftMin :
          IsIntervalMin snapshot.rank
            leftLower leftUpper leftMinimum := by
        exact subtreeOwner_isMin snapshot left left_le_n
      have rightMin :
          IsIntervalMin snapshot.rank
            rightLower rightUpper rightMinimum := by
        exact subtreeOwner_isMin snapshot right upper_le_n
      refine {
        left := leftMinimum
        right := rightMinimum
        ordered := ?_
        leftLower := leftLower
        leftUpper := leftUpper
        leftMinimum := leftMin
        leftNeighbor_mem := ?_
        rightLower := rightLower
        rightUpper := rightUpper
        rightMinimum := rightMin
        rightNeighbor_mem := ?_
      }
      · constructor
        · have upperMember := leftMin.2.1
          change leftMinimum.val < (valuePos key).val
          change leftMinimum.val ≤ 2 * key.val at upperMember
          simp only [valuePos]
          omega
        · have lowerMember := rightMin.1
          change (valuePos key).val < rightMinimum.val
          change 2 * (key.val + 1) ≤ rightMinimum.val at lowerMember
          simp only [valuePos]
          omega
      · constructor
        · change 2 * lower ≤ (leftNullPos key).val
          simp only [leftNullPos]
          have bounds := left.lower_le_upper
          omega
        · change (leftNullPos key).val ≤ 2 * key.val
          simp only [leftNullPos]
          omega
      · constructor
        · change 2 * (key.val + 1) ≤ (rightNullPos key).val
          simp only [rightNullPos]
          omega
        · change (rightNullPos key).val ≤ 2 * upper
          simp only [rightNullPos]
          have bounds := right.lower_le_upper
          omega
  | @leftContext lower root upper left focus right ih =>
      have left_le_n : root ≤ n := by
        have bounds := right.lower_le_upper
        omega
      exact ih left_le_n
  | @rightContext lower root upper left right focus ih =>
      exact ih upper_le_n

/--
The boundary selection together with its placement in every surrounding
focus interval.  Packaging the inequalities with the recursive construction
avoids any proof-irrelevance dependence in downstream geometry.
-/
structure FocusedBoundaryMinimumSelection
    {n lower upper : ℕ} (snapshot : Snapshot n)
    (tree : BST lower upper) (upper_le_n : upper ≤ n)
    (key : Fin n) (focus : KeyFocus key.val tree) : Type where
  selection : BoundaryMinimumSelection snapshot key
  leftLower_mem : 2 * lower ≤ selection.left.val
  leftUpper_mem : selection.left.val ≤ 2 * upper
  rightLower_mem : 2 * lower ≤ selection.right.val
  rightUpper_mem : selection.right.val ≤ 2 * upper

/--
Recursive construction of the exact boundary selection and all enclosing
interval-membership facts.
-/
noncomputable def focusedBoundaryMinimumSelectionFrom
    {n lower upper : ℕ} (snapshot : Snapshot n)
    (tree : BST lower upper) (upper_le_n : upper ≤ n)
    (key : Fin n) (focus : KeyFocus key.val tree) :
    FocusedBoundaryMinimumSelection
      snapshot tree upper_le_n key focus := by
  induction focus with
  | @root lower upper left right =>
      let selection :=
        boundaryMinimumSelectionRaw
          snapshot (.node left right) upper_le_n key
            (.root left right)
      have left_le_n : key.val ≤ n := by
        have bounds := right.lower_le_upper
        omega
      have leftMin :=
        subtreeOwner_isMin snapshot left left_le_n
      have rightMin :=
        subtreeOwner_isMin snapshot right upper_le_n
      refine {
        selection := selection
        leftLower_mem := ?_
        leftUpper_mem := ?_
        rightLower_mem := ?_
        rightUpper_mem := ?_
      }
      · change 2 * lower ≤
          (subtreeOwner snapshot left left_le_n).val
        exact leftMin.1
      · change
          (subtreeOwner snapshot left left_le_n).val ≤ 2 * upper
        have member :
            (subtreeOwner snapshot left left_le_n).val ≤
              2 * key.val := leftMin.2.1
        have bounds := right.lower_le_upper
        omega
      · change 2 * lower ≤
          (subtreeOwner snapshot right upper_le_n).val
        have member :
            2 * (key.val + 1) ≤
              (subtreeOwner snapshot right upper_le_n).val :=
          rightMin.1
        have bounds := left.lower_le_upper
        omega
      · change
          (subtreeOwner snapshot right upper_le_n).val ≤ 2 * upper
        exact rightMin.2.1
  | @leftContext lower root upper left focus right ih =>
      have left_le_n : root ≤ n := by
        have bounds := right.lower_le_upper
        omega
      let child := ih left_le_n
      refine {
        selection := child.selection
        leftLower_mem := ?_
        leftUpper_mem := ?_
        rightLower_mem := ?_
        rightUpper_mem := ?_
      }
      · exact child.leftLower_mem
      · have bounds := right.lower_le_upper
        exact child.leftUpper_mem.trans (by omega)
      · exact child.rightLower_mem
      · have bounds := right.lower_le_upper
        exact child.rightUpper_mem.trans (by omega)
  | @rightContext lower root upper left right focus ih =>
      let child := ih upper_le_n
      refine {
        selection := child.selection
        leftLower_mem := ?_
        leftUpper_mem := child.leftUpper_mem
        rightLower_mem := ?_
        rightUpper_mem := child.rightUpper_mem
      }
      · have bounds := left.lower_le_upper
        exact (by omega : 2 * lower ≤ 2 * (root + 1)).trans
          child.leftLower_mem
      · have bounds := left.lower_le_upper
        exact (by omega : 2 * lower ≤ 2 * (root + 1)).trans
          child.rightLower_mem

/-- The boundary selection projected from the placement-aware constructor. -/
noncomputable def boundaryMinimumSelectionFrom
    {n lower upper : ℕ} (snapshot : Snapshot n)
    (tree : BST lower upper) (upper_le_n : upper ≤ n)
    (key : Fin n) (focus : KeyFocus key.val tree) :
    BoundaryMinimumSelection snapshot key :=
  (focusedBoundaryMinimumSelectionFrom
    snapshot tree upper_le_n key focus).selection

/--
Automatic boundary-minimum selection at an arbitrary accessed node of the
pre-splay tree.
-/
noncomputable def boundaryMinimumSelection
    {n : ℕ} (snapshot : Snapshot n)
    (tree : BST 0 n) (key : Fin n) :
    BoundaryMinimumSelection snapshot key :=
  boundaryMinimumSelectionFrom snapshot tree (Nat.le_refl n)
    key (ofFin tree key)

/--
Both automatically selected boundary minima remain inside every surrounding
subtree recorded by the focus.
-/
theorem boundaryMinimumSelectionFrom_mem
    {n lower upper : ℕ} (snapshot : Snapshot n)
    (tree : BST lower upper) (upper_le_n : upper ≤ n)
    (key : Fin n) (focus : KeyFocus key.val tree) :
    let selection :=
      boundaryMinimumSelectionFrom
        snapshot tree upper_le_n key focus
    2 * lower ≤ selection.left.val ∧
      selection.left.val ≤ 2 * upper ∧
      2 * lower ≤ selection.right.val ∧
      selection.right.val ≤ 2 * upper := by
  let focused :=
    focusedBoundaryMinimumSelectionFrom
      snapshot tree upper_le_n key focus
  exact
    ⟨focused.leftLower_mem, focused.leftUpper_mem,
      focused.rightLower_mem, focused.rightUpper_mem⟩

end KeyFocus

/--
Uniqueness of interval minima makes the rank-zero external node of a snapshot
unique globally.
-/
private theorem eq_of_rank_eq_zero
    {n : ℕ} (snapshot : Snapshot n) {zero element : External n}
    (zeroRank : snapshot.rank zero = 0)
    (elementRank : snapshot.rank element = 0) :
    element = zero := by
  let lower : External n := ⟨0, by omega⟩
  let upper : External n := ⟨2 * n, by omega⟩
  have nonempty : lower ≤ upper := by
    simp [lower, upper]
  have zeroMin :
      IsIntervalMin snapshot.rank lower upper zero := by
    refine ⟨?_, ?_, ?_⟩
    · change 0 ≤ zero.val
      omega
    · change zero.val ≤ 2 * n
      omega
    · intro node _ _
      rw [zeroRank]
      omega
  have elementMin :
      IsIntervalMin snapshot.rank lower upper element := by
    refine ⟨?_, ?_, ?_⟩
    · change 0 ≤ element.val
      omega
    · change element.val ≤ 2 * n
      omega
    · intro node _ _
      rw [elementRank]
      omega
  have zeroUnique :=
    snapshot.intervalMin_unique lower upper nonempty zeroMin
  have elementUnique :=
    snapshot.intervalMin_unique lower upper nonempty elementMin
  exact elementUnique.trans zeroUnique.symm

private theorem rank_pos_of_ne_zero
    {n : ℕ} (snapshot : Snapshot n) {zero element : External n}
    (zeroRank : snapshot.rank zero = 0)
    (different : element ≠ zero) :
    0 < snapshot.rank element := by
  by_contra notPositive
  have elementRank : snapshot.rank element = 0 := by omega
  exact different (eq_of_rank_eq_zero snapshot zeroRank elementRank)

/--
If two snapshots have the same minimum on one node interval, they select the
same ternary heavy branch there.
-/
private theorem heavyBranch_eq_of_commonMinimum
    {n : ℕ} (first second : Snapshot n) (node : AtNode n)
    (candidate : External n)
    (firstMin :
      IsIntervalMin first.rank
        node.wholeLower node.wholeUpper candidate)
    (secondMin :
      IsIntervalMin second.rank
        node.wholeLower node.wholeUpper candidate) :
    node.heavyBranch first = node.heavyBranch second := by
  have contains :=
    first.heavyBranch_contains_intervalMin
      node.wholeLower node.wholeUpper node.whole_nonempty node.root
  have candidateEq :=
    first.intervalMin_unique
      node.wholeLower node.wholeUpper node.whole_nonempty firstMin
  rw [← candidateEq] at contains
  exact
    second.heavyBranch_unique
      node.wholeLower node.wholeUpper node.whole_nonempty
      node.root ⟨candidate, secondMin, contains⟩

/--
Pointwise rank agreement on the complete external interval of an indexed
subtree implies equality of all its bends, for every incoming-edge state.
-/
private theorem bendsFrom_eq_of_rank_eqOn
    {n lower upper : ℕ} (first second : Snapshot n)
    (tree : BST lower upper) (upper_le_n : upper ≤ n)
    (incoming : Option TernaryBranch)
    (rankEq :
      ∀ element : External n,
        2 * lower ≤ element.val → element.val ≤ 2 * upper →
          first.rank element = second.rank element) :
    bendsFrom first tree upper_le_n incoming =
      bendsFrom second tree upper_le_n incoming := by
  induction tree generalizing incoming with
  | empty boundary =>
      simp [bendsFrom]
  | @node lower root upper left right ihLeft ihRight =>
      let node : AtNode n := {
        lower := lower
        root := root
        upper := upper
        left := left
        right := right
        upper_le_n := upper_le_n
      }
      have left_le_n : root ≤ n := by
        have bounds := right.lower_le_upper
        omega
      let candidate :=
        first.intervalMin
          node.wholeLower node.wholeUpper node.whole_nonempty
      have firstMin :
          IsIntervalMin first.rank
            node.wholeLower node.wholeUpper candidate :=
        first.intervalMin_isMin _ _ _
      have secondMin :
          IsIntervalMin second.rank
            node.wholeLower node.wholeUpper candidate := by
        refine ⟨firstMin.1, firstMin.2.1, ?_⟩
        intro element elementLower elementUpper
        rw [← rankEq candidate firstMin.1 firstMin.2.1,
          ← rankEq element elementLower elementUpper]
        exact firstMin.2.2 element elementLower elementUpper
      have branchEq :
          node.heavyBranch first = node.heavyBranch second :=
        heavyBranch_eq_of_commonMinimum
          first second node candidate firstMin secondMin
      have leftEq :
          ∀ childIncomingState,
            bendsFrom first left left_le_n childIncomingState =
              bendsFrom second left left_le_n childIncomingState := by
        intro childIncomingState
        apply ihLeft left_le_n childIncomingState
        intro element elementLower elementUpper
        apply rankEq element
        · exact elementLower
        · have bounds := right.lower_le_upper
          omega
      have rightEq :
          ∀ childIncomingState,
            bendsFrom first right upper_le_n childIncomingState =
              bendsFrom second right upper_le_n childIncomingState := by
        intro childIncomingState
        apply ihRight upper_le_n childIncomingState
        intro element elementLower elementUpper
        apply rankEq element
        · have bounds := left.lower_le_upper
          omega
        · exact elementUpper
      simp only [bendsFrom]
      change
        bendAt ⟨root, by
            have bounds := right.lower_le_upper
            omega⟩ incoming (node.heavyBranch first) ∪
            (bendsFrom first left left_le_n
                (childIncoming (node.heavyBranch first) .left) ∪
              bendsFrom first right upper_le_n
                (childIncoming (node.heavyBranch first) .right)) =
          bendAt ⟨root, by
              have bounds := right.lower_le_upper
              omega⟩ incoming (node.heavyBranch second) ∪
            (bendsFrom second left left_le_n
                (childIncoming (node.heavyBranch second) .left) ∪
              bendsFrom second right upper_le_n
                (childIncoming (node.heavyBranch second) .right))
      rw [branchEq, leftEq, rightEq]

/--
Lowering the minimum of one fixed external region does not change any heavy
branch inside that region.  This is the exact local fact needed below for
each child subtree of the accessed node.

Outside the distinguished point, `altered` only has to agree with doubled
true ranks on the region.  The unique true rank-zero point is required to lie
outside the region; this is what makes the artificial priority `1` strictly
smaller than every other rank there.
-/
private theorem bendsFrom_eq_in_minimumRegion
    {n lower upper : ℕ}
    (snapshot altered : Snapshot n)
    (zero special regionLower regionUpper : External n)
    (zeroRank : snapshot.rank zero = 0)
    (zeroOutside :
      zero < regionLower ∨ regionUpper < zero)
    (specialMin :
      IsIntervalMin snapshot.rank
        regionLower regionUpper special)
    (alteredSpecial : altered.rank special = 1)
    (alteredOrdinary :
      ∀ element : External n,
        regionLower ≤ element → element ≤ regionUpper →
          element ≠ special →
            altered.rank element =
              truePriority (snapshot.rank element))
    (tree : BST lower upper) (upper_le_n : upper ≤ n)
    (regionContainsLower :
      regionLower.val ≤ 2 * lower)
    (regionContainsUpper :
      2 * upper ≤ regionUpper.val)
    (incoming : Option TernaryBranch) :
    bendsFrom altered tree upper_le_n incoming =
      bendsFrom snapshot.withTruePriority tree upper_le_n incoming := by
  induction tree generalizing incoming with
  | empty boundary =>
      simp [bendsFrom]
  | @node lower root upper left right ihLeft ihRight =>
      let node : AtNode n := {
        lower := lower
        root := root
        upper := upper
        left := left
        right := right
        upper_le_n := upper_le_n
      }
      have left_le_n : root ≤ n := by
        have bounds := right.lower_le_upper
        omega
      have branchEq :
          node.heavyBranch altered =
            node.heavyBranch snapshot.withTruePriority := by
        by_cases specialInside :
            node.wholeLower ≤ special ∧
              special ≤ node.wholeUpper
        · have trueMin :
              IsIntervalMin snapshot.rank
                node.wholeLower node.wholeUpper special := by
            refine ⟨specialInside.1, specialInside.2, ?_⟩
            intro element elementLower elementUpper
            apply specialMin.2.2 element
            · have nodeLower :
                  regionLower ≤ node.wholeLower := by
                change regionLower.val ≤ 2 * lower
                exact regionContainsLower
              exact nodeLower.trans elementLower
            · have nodeUpper :
                  node.wholeUpper ≤ regionUpper := by
                change 2 * upper ≤ regionUpper.val
                exact regionContainsUpper
              exact elementUpper.trans nodeUpper
          have doubledMin :
              IsIntervalMin snapshot.withTruePriority.rank
                node.wholeLower node.wholeUpper special :=
            (isIntervalMin_withTruePriority_iff
              snapshot node.wholeLower node.wholeUpper special).2
              trueMin
          have artificialMin :
              IsIntervalMin altered.rank
                node.wholeLower node.wholeUpper special := by
            refine ⟨specialInside.1, specialInside.2, ?_⟩
            intro element elementLower elementUpper
            by_cases equal : element = special
            · subst element
              exact Nat.le_refl _
            · have elementInRegionLower :
                  regionLower ≤ element := by
                have nodeLower :
                    regionLower ≤ node.wholeLower := by
                  change regionLower.val ≤ 2 * lower
                  exact regionContainsLower
                exact nodeLower.trans elementLower
              have elementInRegionUpper :
                  element ≤ regionUpper := by
                have nodeUpper :
                    node.wholeUpper ≤ regionUpper := by
                  change 2 * upper ≤ regionUpper.val
                  exact regionContainsUpper
                exact elementUpper.trans nodeUpper
              have elementNeZero : element ≠ zero := by
                intro elementEq
                subst element
                rcases zeroOutside with zeroLeft | zeroRight
                · exact (not_lt_of_ge elementInRegionLower) zeroLeft
                · exact (not_lt_of_ge elementInRegionUpper) zeroRight
              rw [alteredSpecial,
                alteredOrdinary element
                  elementInRegionLower elementInRegionUpper equal]
              have positive :=
                rank_pos_of_ne_zero snapshot zeroRank elementNeZero
              simp only [truePriority]
              omega
          exact
            heavyBranch_eq_of_commonMinimum
              altered snapshot.withTruePriority node special
                artificialMin doubledMin
        · have rankEq :
              ∀ element : External n,
                node.wholeLower ≤ element →
                  element ≤ node.wholeUpper →
                    altered.rank element =
                      snapshot.withTruePriority.rank element := by
            intro element elementLower elementUpper
            have elementNeSpecial : element ≠ special := by
              intro equal
              apply specialInside
              simpa [equal] using And.intro elementLower elementUpper
            have elementInRegionLower :
                regionLower ≤ element := by
              have nodeLower :
                  regionLower ≤ node.wholeLower := by
                change regionLower.val ≤ 2 * lower
                exact regionContainsLower
              exact nodeLower.trans elementLower
            have elementInRegionUpper :
                element ≤ regionUpper := by
              have nodeUpper :
                  node.wholeUpper ≤ regionUpper := by
                change 2 * upper ≤ regionUpper.val
                exact regionContainsUpper
              exact elementUpper.trans nodeUpper
            exact
              alteredOrdinary element
                elementInRegionLower elementInRegionUpper
                elementNeSpecial
          have alteredCanonical :=
            altered.intervalMin_isMin
              node.wholeLower node.wholeUpper node.whole_nonempty
          have doubledCanonical :
              IsIntervalMin snapshot.withTruePriority.rank
                node.wholeLower node.wholeUpper
                (altered.intervalMin
                  node.wholeLower node.wholeUpper
                  node.whole_nonempty) := by
            refine
              ⟨alteredCanonical.1, alteredCanonical.2.1, ?_⟩
            intro element elementLower elementUpper
            rw [← rankEq
                  (altered.intervalMin
                    node.wholeLower node.wholeUpper
                    node.whole_nonempty)
                  alteredCanonical.1 alteredCanonical.2.1,
              ← rankEq element elementLower elementUpper]
            exact
              alteredCanonical.2.2
                element elementLower elementUpper
          exact
            heavyBranch_eq_of_commonMinimum
              altered snapshot.withTruePriority node
                (altered.intervalMin
                  node.wholeLower node.wholeUpper
                  node.whole_nonempty)
                alteredCanonical doubledCanonical
      have leftEq :
          ∀ childIncomingState,
            bendsFrom altered left left_le_n childIncomingState =
              bendsFrom snapshot.withTruePriority left left_le_n
                childIncomingState := by
        intro childIncomingState
        exact ihLeft left_le_n regionContainsLower (by
          have bounds := right.lower_le_upper
          omega) childIncomingState
      have rightEq :
          ∀ childIncomingState,
            bendsFrom altered right upper_le_n childIncomingState =
              bendsFrom snapshot.withTruePriority right upper_le_n
                childIncomingState := by
        intro childIncomingState
        exact ihRight upper_le_n (by
          have bounds := left.lower_le_upper
          omega) regionContainsUpper childIncomingState
      simp only [bendsFrom]
      change
        bendAt ⟨root, by
            have bounds := right.lower_le_upper
            omega⟩ incoming (node.heavyBranch altered) ∪
            (bendsFrom altered left left_le_n
                (childIncoming (node.heavyBranch altered) .left) ∪
              bendsFrom altered right upper_le_n
                (childIncoming (node.heavyBranch altered) .right)) =
          bendAt ⟨root, by
              have bounds := right.lower_le_upper
              omega⟩ incoming
                (node.heavyBranch snapshot.withTruePriority) ∪
            (bendsFrom snapshot.withTruePriority left left_le_n
                (childIncoming
                  (node.heavyBranch snapshot.withTruePriority) .left) ∪
              bendsFrom snapshot.withTruePriority right upper_le_n
                (childIncoming
                  (node.heavyBranch snapshot.withTruePriority) .right))
      rw [branchEq, leftEq, rightEq]

/--
At the accessed node itself, lowering the true minima of its two child
subtree intervals to artificial priority leaves every bend unchanged.
-/
private theorem bendsFrom_twoBoundaryAtRoot_eq
    {n lower upper : ℕ} (snapshot : Snapshot n)
    (key : Fin n)
    (left : BST lower key.val)
    (right : BST (key.val + 1) upper)
    (upper_le_n : upper ≤ n)
    (zeroRank : snapshot.rank (valuePos key) = 0)
    (incoming : Option TernaryBranch) :
    let left_le_n : key.val ≤ n := by
      have _bounds := right.lower_le_upper
      omega
    let leftBoundary :=
      subtreeOwner snapshot left left_le_n
    let rightBoundary :=
      subtreeOwner snapshot right upper_le_n
    let ordered :
        leftBoundary < valuePos key ∧
          valuePos key < rightBoundary := by
      have leftMin :=
        subtreeOwner_isMin snapshot left left_le_n
      have rightMin :=
        subtreeOwner_isMin snapshot right upper_le_n
      constructor
      · change leftBoundary.val < 2 * key.val + 1
        have member : leftBoundary.val ≤ 2 * key.val :=
          leftMin.2.1
        omega
      · change 2 * key.val + 1 < rightBoundary.val
        have member :
            2 * (key.val + 1) ≤ rightBoundary.val :=
          rightMin.1
        omega
    bendsFrom snapshot (.node left right) upper_le_n incoming =
      bendsFrom
        (snapshot.withTwoBoundaryTemporaryPriority
          leftBoundary (valuePos key) rightBoundary
          ordered zeroRank)
        (.node left right) upper_le_n incoming := by
  dsimp only
  let left_le_n : key.val ≤ n := by
    have bounds := right.lower_le_upper
    omega
  let leftLower := subtreeLower left left_le_n
  let leftUpper := subtreeUpper left left_le_n
  let rightLower := subtreeLower right upper_le_n
  let rightUpper := subtreeUpper right upper_le_n
  let leftBoundary :=
    subtreeOwner snapshot left left_le_n
  let rightBoundary :=
    subtreeOwner snapshot right upper_le_n
  have leftMin :
      IsIntervalMin snapshot.rank
        leftLower leftUpper leftBoundary :=
    subtreeOwner_isMin snapshot left left_le_n
  have rightMin :
      IsIntervalMin snapshot.rank
        rightLower rightUpper rightBoundary :=
    subtreeOwner_isMin snapshot right upper_le_n
  have ordered :
      leftBoundary < valuePos key ∧
        valuePos key < rightBoundary := by
    constructor
    · change leftBoundary.val < 2 * key.val + 1
      have member : leftBoundary.val ≤ 2 * key.val :=
        leftMin.2.1
      omega
    · change 2 * key.val + 1 < rightBoundary.val
      have member :
          2 * (key.val + 1) ≤ rightBoundary.val :=
        rightMin.1
      omega
  let artificial :=
    snapshot.withTwoBoundaryTemporaryPriority
      leftBoundary (valuePos key) rightBoundary
      ordered zeroRank
  let node : AtNode n := {
    lower := lower
    root := key.val
    upper := upper
    left := left
    right := right
    upper_le_n := upper_le_n
  }
  have zeroInNode :
      node.wholeLower ≤ valuePos key ∧
        valuePos key ≤ node.wholeUpper := by
    constructor
    · change 2 * lower ≤ 2 * key.val + 1
      have bounds := left.lower_le_upper
      omega
    · change 2 * key.val + 1 ≤ 2 * upper
      have bounds := right.lower_le_upper
      omega
  have trueZeroMin :
      IsIntervalMin snapshot.withTruePriority.rank
        node.wholeLower node.wholeUpper (valuePos key) := by
    refine ⟨zeroInNode.1, zeroInNode.2, ?_⟩
    intro element _ _
    simp only [withTruePriority_rank, truePriority, zeroRank]
    omega
  have artificialZeroRank :
      artificial.rank (valuePos key) = 0 := by
    have ordinary :
        valuePos key ≠ leftBoundary ∧
          valuePos key ≠ rightBoundary := by
      exact ⟨ne_of_gt ordered.1, ne_of_lt ordered.2⟩
    change
      twoBoundaryTemporaryRank snapshot
        leftBoundary rightBoundary (valuePos key) = 0
    rw [twoBoundaryTemporaryRank_eq_truePriority
      snapshot leftBoundary rightBoundary (valuePos key) ordinary,
      zeroRank]
    simp [truePriority]
  have artificialZeroMin :
      IsIntervalMin artificial.rank
        node.wholeLower node.wholeUpper (valuePos key) := by
    refine ⟨zeroInNode.1, zeroInNode.2, ?_⟩
    intro element _ _
    rw [artificialZeroRank]
    omega
  have branchEq :
      node.heavyBranch artificial =
        node.heavyBranch snapshot.withTruePriority :=
    heavyBranch_eq_of_commonMinimum
      artificial snapshot.withTruePriority node (valuePos key)
        artificialZeroMin trueZeroMin
  have leftEq :
      ∀ childIncomingState,
        bendsFrom artificial left left_le_n childIncomingState =
          bendsFrom snapshot.withTruePriority left left_le_n
            childIncomingState := by
    intro childIncomingState
    apply bendsFrom_eq_in_minimumRegion
      snapshot artificial (valuePos key) leftBoundary
        leftLower leftUpper zeroRank
    · right
      -- The zero is to the right of the left child interval.
      change 2 * key.val < 2 * key.val + 1
      omega
    · exact leftMin
    · change
        twoBoundaryTemporaryRank snapshot
          leftBoundary rightBoundary leftBoundary = 1
      exact twoBoundaryTemporaryRank_eq_one_left
        snapshot leftBoundary rightBoundary
    · intro element elementLower elementUpper elementNeLeft
      have elementNeRight : element ≠ rightBoundary := by
        intro equal
        subst element
        have rightLowerMember := rightMin.1
        have leftUpperMember := elementUpper
        change 2 * (key.val + 1) ≤ rightBoundary.val at rightLowerMember
        change rightBoundary.val ≤ 2 * key.val at leftUpperMember
        omega
      change
        twoBoundaryTemporaryRank snapshot
          leftBoundary rightBoundary element =
            truePriority (snapshot.rank element)
      exact
        twoBoundaryTemporaryRank_eq_truePriority
          snapshot leftBoundary rightBoundary element
            ⟨elementNeLeft, elementNeRight⟩
    · simp [leftLower, subtreeLower]
    · simp [leftUpper, subtreeUpper]
  have rightEq :
      ∀ childIncomingState,
        bendsFrom artificial right upper_le_n childIncomingState =
          bendsFrom snapshot.withTruePriority right upper_le_n
            childIncomingState := by
    intro childIncomingState
    apply bendsFrom_eq_in_minimumRegion
      snapshot artificial (valuePos key) rightBoundary
        rightLower rightUpper zeroRank
    · left
      -- The zero is to the left of the right child interval.
      change 2 * key.val + 1 < 2 * (key.val + 1)
      omega
    · exact rightMin
    · change
        twoBoundaryTemporaryRank snapshot
          leftBoundary rightBoundary rightBoundary = 1
      exact twoBoundaryTemporaryRank_eq_one_right
        snapshot leftBoundary rightBoundary
    · intro element elementLower elementUpper elementNeRight
      have elementNeLeft : element ≠ leftBoundary := by
        intro equal
        subst element
        have leftUpperMember := leftMin.2.1
        have rightLowerMember := elementLower
        change leftBoundary.val ≤ 2 * key.val at leftUpperMember
        change 2 * (key.val + 1) ≤ leftBoundary.val at rightLowerMember
        omega
      change
        twoBoundaryTemporaryRank snapshot
          leftBoundary rightBoundary element =
            truePriority (snapshot.rank element)
      exact
        twoBoundaryTemporaryRank_eq_truePriority
          snapshot leftBoundary rightBoundary element
            ⟨elementNeLeft, elementNeRight⟩
    · simp [rightLower, subtreeLower]
    · simp [rightUpper, subtreeUpper]
  have artificialEq :
      bendsFrom artificial (.node left right) upper_le_n incoming =
        bendsFrom snapshot.withTruePriority
          (.node left right) upper_le_n incoming := by
    simp only [bendsFrom]
    change
      bendAt ⟨key.val, by
          have bounds := right.lower_le_upper
          omega⟩ incoming (node.heavyBranch artificial) ∪
          (bendsFrom artificial left left_le_n
              (childIncoming (node.heavyBranch artificial) .left) ∪
            bendsFrom artificial right upper_le_n
              (childIncoming (node.heavyBranch artificial) .right)) =
        bendAt ⟨key.val, by
            have bounds := right.lower_le_upper
            omega⟩ incoming
              (node.heavyBranch snapshot.withTruePriority) ∪
          (bendsFrom snapshot.withTruePriority left left_le_n
              (childIncoming
                (node.heavyBranch snapshot.withTruePriority) .left) ∪
            bendsFrom snapshot.withTruePriority right upper_le_n
              (childIncoming
                (node.heavyBranch snapshot.withTruePriority) .right))
    rw [branchEq, leftEq, rightEq]
  calc
    bendsFrom snapshot (.node left right) upper_le_n incoming =
        bendsFrom snapshot.withTruePriority
          (.node left right) upper_le_n incoming :=
      (bendsFrom_withTruePriority_eq
        snapshot (.node left right) upper_le_n incoming).symm
    _ = bendsFrom artificial
          (.node left right) upper_le_n incoming :=
      artificialEq.symm

/-- The rank-zero separator remains rank zero after installing two markers. -/
private theorem twoBoundary_rank_zero
    {n : ℕ} (snapshot : Snapshot n)
    (zero left right : External n)
    (ordered : left < zero ∧ zero < right)
    (zeroRank : snapshot.rank zero = 0) :
    (snapshot.withTwoBoundaryTemporaryPriority
      left zero right ordered zeroRank).rank zero = 0 := by
  have ordinary : zero ≠ left ∧ zero ≠ right :=
    ⟨ne_of_gt ordered.1, ne_of_lt ordered.2⟩
  change
    twoBoundaryTemporaryRank snapshot left right zero = 0
  rw [twoBoundaryTemporaryRank_eq_truePriority
    snapshot left right zero ordinary, zeroRank]
  simp [truePriority]

/-- A shared rank-zero owner forces equality of the node's heavy branch. -/
private theorem heavyBranch_eq_of_commonZero
    {n : ℕ} (first second : Snapshot n)
    (node : AtNode n) (zero : External n)
    (inside :
      node.wholeLower ≤ zero ∧ zero ≤ node.wholeUpper)
    (firstZero : first.rank zero = 0)
    (secondZero : second.rank zero = 0) :
    node.heavyBranch first = node.heavyBranch second := by
  have firstMin :
      IsIntervalMin first.rank
        node.wholeLower node.wholeUpper zero := by
    refine ⟨inside.1, inside.2, ?_⟩
    intro element _ _
    rw [firstZero]
    omega
  have secondMin :
      IsIntervalMin second.rank
        node.wholeLower node.wholeUpper zero := by
    refine ⟨inside.1, inside.2, ?_⟩
    intro element _ _
    rw [secondZero]
    omega
  exact heavyBranch_eq_of_commonMinimum
    first second node zero firstMin secondMin

/--
Search-context induction: the exact child-interval minima produced by
`boundaryMinimumSelectionFrom` can be lowered before the splay without
changing a bend anywhere in the surrounding tree.
-/
private theorem bendsFrom_twoBoundaryFocus_eq
    {n lower upper : ℕ} (snapshot : Snapshot n)
    (tree : BST lower upper) (upper_le_n : upper ≤ n)
    (key : Fin n) (focus : KeyFocus key.val tree)
    (zeroRank : snapshot.rank (valuePos key) = 0)
    (incoming : Option TernaryBranch) :
    let selection :=
      KeyFocus.boundaryMinimumSelectionFrom
        snapshot tree upper_le_n key focus
    bendsFrom snapshot tree upper_le_n incoming =
      bendsFrom
        (snapshot.withTwoBoundaryTemporaryPriority
          selection.left (valuePos key) selection.right
          selection.ordered zeroRank)
        tree upper_le_n incoming := by
  induction focus generalizing incoming with
  | @root lower upper left right =>
      simpa only [KeyFocus.boundaryMinimumSelectionFrom,
        KeyFocus.focusedBoundaryMinimumSelectionFrom,
        KeyFocus.boundaryMinimumSelectionRaw] using
        bendsFrom_twoBoundaryAtRoot_eq
          snapshot key left right upper_le_n zeroRank incoming
  | @leftContext lower root upper left focus right ih =>
      have left_le_n : root ≤ n := by
        have bounds := right.lower_le_upper
        omega
      let selection :=
        KeyFocus.boundaryMinimumSelectionFrom
          snapshot left left_le_n key focus
      let artificial :=
        snapshot.withTwoBoundaryTemporaryPriority
          selection.left (valuePos key) selection.right
          selection.ordered zeroRank
      let node : AtNode n := {
        lower := lower
        root := root
        upper := upper
        left := left
        right := right
        upper_le_n := upper_le_n
      }
      have keyBounds := focus.key_bounds
      have zeroInside :
          node.wholeLower ≤ valuePos key ∧
            valuePos key ≤ node.wholeUpper := by
        constructor
        · change 2 * lower ≤ 2 * key.val + 1
          omega
        · change 2 * key.val + 1 ≤ 2 * upper
          have bounds := right.lower_le_upper
          omega
      have artificialZero : artificial.rank (valuePos key) = 0 :=
        twoBoundary_rank_zero snapshot (valuePos key)
          selection.left selection.right selection.ordered zeroRank
      have branchEq :
          node.heavyBranch snapshot =
            node.heavyBranch artificial :=
        heavyBranch_eq_of_commonZero snapshot artificial node
          (valuePos key) zeroInside zeroRank artificialZero
      have leftEq :
          ∀ childIncomingState,
            bendsFrom snapshot left left_le_n childIncomingState =
              bendsFrom artificial left left_le_n
                childIncomingState := by
        intro childIncomingState
        simpa only [selection, artificial] using
          ih left_le_n childIncomingState
      have selectionMem :=
        KeyFocus.boundaryMinimumSelectionFrom_mem
          snapshot left left_le_n key focus
      change
        2 * lower ≤ selection.left.val ∧
          selection.left.val ≤ 2 * root ∧
          2 * lower ≤ selection.right.val ∧
          selection.right.val ≤ 2 * root at selectionMem
      have rightEq :
          ∀ childIncomingState,
            bendsFrom snapshot right upper_le_n childIncomingState =
              bendsFrom artificial right upper_le_n
                childIncomingState := by
        intro childIncomingState
        have artificialToDoubled :
            bendsFrom artificial right upper_le_n childIncomingState =
              bendsFrom snapshot.withTruePriority right upper_le_n
                childIncomingState := by
          apply bendsFrom_eq_of_rank_eqOn
          intro element elementLower elementUpper
          have elementNeLeft : element ≠ selection.left := by
            intro equal
            subst element
            have selectedUpper := selectionMem.2.1
            omega
          have elementNeRight : element ≠ selection.right := by
            intro equal
            subst element
            have selectedUpper := selectionMem.2.2.2
            omega
          change
            twoBoundaryTemporaryRank snapshot
              selection.left selection.right element =
                truePriority (snapshot.rank element)
          exact
            twoBoundaryTemporaryRank_eq_truePriority
              snapshot selection.left selection.right element
                ⟨elementNeLeft, elementNeRight⟩
        calc
          bendsFrom snapshot right upper_le_n childIncomingState =
              bendsFrom snapshot.withTruePriority right upper_le_n
                childIncomingState :=
            (bendsFrom_withTruePriority_eq snapshot right
              upper_le_n childIncomingState).symm
          _ = bendsFrom artificial right upper_le_n
                childIncomingState :=
            artificialToDoubled.symm
      simp only [KeyFocus.boundaryMinimumSelectionFrom,
        KeyFocus.focusedBoundaryMinimumSelectionFrom]
      simp only [bendsFrom]
      change
        bendAt ⟨root, by
            have bounds := right.lower_le_upper
            omega⟩ incoming (node.heavyBranch snapshot) ∪
            (bendsFrom snapshot left left_le_n
                (childIncoming (node.heavyBranch snapshot) .left) ∪
              bendsFrom snapshot right upper_le_n
                (childIncoming (node.heavyBranch snapshot) .right)) =
          bendAt ⟨root, by
              have bounds := right.lower_le_upper
              omega⟩ incoming (node.heavyBranch artificial) ∪
            (bendsFrom artificial left left_le_n
                (childIncoming (node.heavyBranch artificial) .left) ∪
              bendsFrom artificial right upper_le_n
                (childIncoming (node.heavyBranch artificial) .right))
      rw [branchEq, leftEq, rightEq]
  | @rightContext lower root upper left right focus ih =>
      let selection :=
        KeyFocus.boundaryMinimumSelectionFrom
          snapshot right upper_le_n key focus
      let artificial :=
        snapshot.withTwoBoundaryTemporaryPriority
          selection.left (valuePos key) selection.right
          selection.ordered zeroRank
      let node : AtNode n := {
        lower := lower
        root := root
        upper := upper
        left := left
        right := right
        upper_le_n := upper_le_n
      }
      have keyBounds := focus.key_bounds
      have zeroInside :
          node.wholeLower ≤ valuePos key ∧
            valuePos key ≤ node.wholeUpper := by
        constructor
        · change 2 * lower ≤ 2 * key.val + 1
          have bounds := left.lower_le_upper
          omega
        · change 2 * key.val + 1 ≤ 2 * upper
          omega
      have artificialZero : artificial.rank (valuePos key) = 0 :=
        twoBoundary_rank_zero snapshot (valuePos key)
          selection.left selection.right selection.ordered zeroRank
      have branchEq :
          node.heavyBranch snapshot =
            node.heavyBranch artificial :=
        heavyBranch_eq_of_commonZero snapshot artificial node
          (valuePos key) zeroInside zeroRank artificialZero
      have rightEq :
          ∀ childIncomingState,
            bendsFrom snapshot right upper_le_n childIncomingState =
              bendsFrom artificial right upper_le_n
                childIncomingState := by
        intro childIncomingState
        simpa only [selection, artificial] using
          ih upper_le_n childIncomingState
      have selectionMem :=
        KeyFocus.boundaryMinimumSelectionFrom_mem
          snapshot right upper_le_n key focus
      change
        2 * (root + 1) ≤ selection.left.val ∧
          selection.left.val ≤ 2 * upper ∧
          2 * (root + 1) ≤ selection.right.val ∧
          selection.right.val ≤ 2 * upper at selectionMem
      have leftEq :
          ∀ childIncomingState,
            bendsFrom snapshot left (by
                have bounds := right.lower_le_upper
                omega) childIncomingState =
              bendsFrom artificial left (by
                have bounds := right.lower_le_upper
                omega) childIncomingState := by
        intro childIncomingState
        have left_le_n : root ≤ n := by
          have bounds := right.lower_le_upper
          omega
        have artificialToDoubled :
            bendsFrom artificial left left_le_n childIncomingState =
              bendsFrom snapshot.withTruePriority left left_le_n
                childIncomingState := by
          apply bendsFrom_eq_of_rank_eqOn
          intro element elementLower elementUpper
          have elementNeLeft : element ≠ selection.left := by
            intro equal
            subst element
            have selectedLower := selectionMem.1
            omega
          have elementNeRight : element ≠ selection.right := by
            intro equal
            subst element
            have selectedLower := selectionMem.2.2.1
            omega
          change
            twoBoundaryTemporaryRank snapshot
              selection.left selection.right element =
                truePriority (snapshot.rank element)
          exact
            twoBoundaryTemporaryRank_eq_truePriority
              snapshot selection.left selection.right element
                ⟨elementNeLeft, elementNeRight⟩
        calc
          bendsFrom snapshot left left_le_n childIncomingState =
              bendsFrom snapshot.withTruePriority left left_le_n
                childIncomingState :=
            (bendsFrom_withTruePriority_eq snapshot left
              left_le_n childIncomingState).symm
          _ = bendsFrom artificial left left_le_n
                childIncomingState :=
            artificialToDoubled.symm
      have left_le_n : root ≤ n := by
        have bounds := right.lower_le_upper
        omega
      simp only [KeyFocus.boundaryMinimumSelectionFrom,
        KeyFocus.focusedBoundaryMinimumSelectionFrom]
      simp only [bendsFrom]
      change
        bendAt ⟨root, by
            have bounds := right.lower_le_upper
            omega⟩ incoming (node.heavyBranch snapshot) ∪
            (bendsFrom snapshot left left_le_n
                (childIncoming (node.heavyBranch snapshot) .left) ∪
              bendsFrom snapshot right upper_le_n
                (childIncoming (node.heavyBranch snapshot) .right)) =
          bendAt ⟨root, by
              have bounds := right.lower_le_upper
              omega⟩ incoming (node.heavyBranch artificial) ∪
            (bendsFrom artificial left left_le_n
                (childIncoming (node.heavyBranch artificial) .left) ∪
              bendsFrom artificial right upper_le_n
                (childIncoming (node.heavyBranch artificial) .right))
      rw [branchEq, leftEq, rightEq]

/--
Installing artificial priorities at the automatically focused boundary
minima preserves the complete pre-splay bend set.

This theorem has no residual tree-geometry premise: the indexed tree focus,
the exact child intervals, and both minima are constructed internally.
-/
theorem bends_eq_twoBoundaryTemporary
    {n : ℕ} (snapshot : Snapshot n)
    (before : BST 0 n) (key : Fin n)
    (zeroRank : snapshot.rank (valuePos key) = 0) :
    let selection :=
      KeyFocus.boundaryMinimumSelection snapshot before key
    bends snapshot before =
      bends
        (snapshot.withTwoBoundaryTemporaryPriority
          selection.left (valuePos key) selection.right
          selection.ordered zeroRank)
        before := by
  simpa only [bends, KeyFocus.boundaryMinimumSelection] using
    bendsFrom_twoBoundaryFocus_eq snapshot before (Nat.le_refl n)
      key (KeyFocus.ofFin before key) zeroRank none

/--
Direct manuscript-facing form for a comparison tree serving `key`.

It is exactly the `before_bends_eq` field required by
`TemporarySplayBendCertificate.ofBoundaryMinima`, with both boundary
vertices selected from the accessed node's actual child-subtree intervals.
-/
theorem before_bends_eq_temporarySnapshot
    {n : ℕ} (comparison : BST 0 n) (key : Fin n)
    (comparisonRoot : comparison.HasRoot key.val)
    (before : BST 0 n) :
    let selection :=
      KeyFocus.boundaryMinimumSelection
        (Snapshot.ofTree comparison) before key
    bends (Snapshot.ofTree comparison) before =
      bends
        (temporarySnapshot comparison key comparisonRoot
          selection.left selection.right selection.ordered)
        before := by
  have zeroRank :=
    ofTree_rank_valuePos_eq_zero_of_hasRoot
      comparison key comparisonRoot
  simpa only [temporarySnapshot] using
    bends_eq_twoBoundaryTemporary
      (Snapshot.ofTree comparison) before key zeroRank

end Splay.Accounting.WholeSplayTemporaryBoundaryGeometry
