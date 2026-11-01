import Splay.Assumptions.StructuralNormalForm
import Splay.Tree.RotationDepthBound

namespace Splay.Accounting.OfflineNormalForm

open Splay.Assumptions.NormalForm
open Splay.Tree

/--
Length, in edges including the final external edge, of the all-left path
starting at the root of an indexed tree.

For an empty tree the relevant external position is already at the root, so
the length is zero.
-/
def leftBoundaryDepth {lower upper : ℕ} : BST lower upper → ℕ
  | .empty _ => 0
  | .node left _ => (leftBoundaryDepth left).succ

/-- The symmetric all-right boundary depth. -/
def rightBoundaryDepth {lower upper : ℕ} : BST lower upper → ℕ
  | .empty _ => 0
  | .node _ right => (rightBoundaryDepth right).succ

/-- Searching for the left interval boundary follows exactly the left spine. -/
@[simp]
theorem externalDepth_lowerBoundary_eq_leftBoundaryDepth
    {lower upper : ℕ} (tree : BST lower upper) :
    tree.externalDepth (2 * lower) = leftBoundaryDepth tree := by
  induction tree with
  | empty =>
      rfl
  | @node lower root upper left right ihLeft ihRight =>
      rw [Splay.Tree.BST.externalDepth_node_of_lt_root left right]
      · simpa [leftBoundaryDepth] using congrArg Nat.succ ihLeft
      · have := left.lower_le_upper
        omega

/-- Searching for the right interval boundary follows exactly the right spine. -/
@[simp]
theorem externalDepth_upperBoundary_eq_rightBoundaryDepth
    {lower upper : ℕ} (tree : BST lower upper) :
    tree.externalDepth (2 * upper) = rightBoundaryDepth tree := by
  induction tree with
  | empty =>
      rfl
  | @node lower root upper left right ihLeft ihRight =>
      rw [Splay.Tree.BST.externalDepth_node_of_root_lt left right]
      · simpa [rightBoundaryDepth] using congrArg Nat.succ ihRight
      · have := right.lower_le_upper
        omega

/--
The exact, non-asymptotic version of bounded proper ribs.

At every value node, the right boundary path of its left subtree and the left
boundary path of its right subtree are bounded.  These are precisely the two
proper ribs leading to the adjacent external/null positions.  The outer
left/right spines of the whole tree are deliberately not constrained.
-/
def HasBoundedMinorRibs :
    {lower upper : ℕ} → BST lower upper → ℕ → Prop
  | _, _, .empty _, _ => True
  | _, _, .node left right, slack =>
      (rightBoundaryDepth left).succ ≤ slack ∧
        (leftBoundaryDepth right).succ ≤ slack ∧
        HasBoundedMinorRibs left slack ∧
        HasBoundedMinorRibs right slack

/--
Interval-polymorphic form of the adjacent-null depth condition.  This form is
suited to structural induction over indexed subtrees.
-/
def HasLocalRelevantNeighborDepthBound
    {lower upper : ℕ} (tree : BST lower upper) (slack : ℕ) : Prop :=
  ∀ key : ℕ, lower ≤ key → key < upper →
    tree.externalDepth (2 * key) ≤ tree.depth key + slack ∧
      tree.externalDepth (2 * key + 2) ≤ tree.depth key + slack

/--
Bounded proper ribs are exactly the adjacent-null depth condition, with no
height or balance assumption.
-/
theorem hasBoundedMinorRibs_iff_localNeighborDepth
    {lower upper slack : ℕ} (tree : BST lower upper) :
    HasBoundedMinorRibs tree slack ↔
      HasLocalRelevantNeighborDepthBound tree slack := by
  induction tree with
  | empty boundary =>
      constructor
      · intro ribs key insideLower insideUpper
        omega
      · intro neighborBound
        simp [HasBoundedMinorRibs]
  | @node lower root upper left right ihLeft ihRight =>
      constructor
      · rintro ⟨leftAtRoot, rightAtRoot, leftRibs, rightRibs⟩
        have leftLocal :
            HasLocalRelevantNeighborDepthBound left slack :=
          ihLeft.mp leftRibs
        have rightLocal :
            HasLocalRelevantNeighborDepthBound right slack :=
          ihRight.mp rightRibs
        intro key insideLower insideUpper
        by_cases atRoot : key = root
        · subst key
          constructor
          · rw [Splay.Tree.BST.externalDepth_node_of_lt_root left right
                (by omega)]
            rw [externalDepth_upperBoundary_eq_rightBoundaryDepth]
            rw [Splay.Tree.BST.depth_root]
            simpa using leftAtRoot
          · rw [Splay.Tree.BST.externalDepth_node_of_root_lt left right
                (by omega)]
            rw [show 2 * root + 2 = 2 * (root + 1) by omega]
            rw [externalDepth_lowerBoundary_eq_leftBoundaryDepth]
            rw [Splay.Tree.BST.depth_root]
            simpa using rightAtRoot
        · by_cases inLeft : key < root
          · obtain ⟨leftNull, rightNull⟩ :=
              leftLocal key insideLower inLeft
            constructor
            · rw [Splay.Tree.BST.externalDepth_node_of_lt_root left right
                  (by omega)]
              rw [Splay.Tree.BST.depth_node_of_lt_root left right inLeft]
              omega
            · rw [Splay.Tree.BST.externalDepth_node_of_lt_root left right
                  (by omega)]
              rw [Splay.Tree.BST.depth_node_of_lt_root left right inLeft]
              omega
          · have inRight : root < key := by omega
            obtain ⟨leftNull, rightNull⟩ :=
              rightLocal key (by omega) insideUpper
            constructor
            · rw [Splay.Tree.BST.externalDepth_node_of_root_lt left right
                  (by omega)]
              rw [Splay.Tree.BST.depth_node_of_root_lt left right inRight]
              omega
            · rw [Splay.Tree.BST.externalDepth_node_of_root_lt left right
                  (by omega)]
              rw [Splay.Tree.BST.depth_node_of_root_lt left right inRight]
              omega
      · intro neighborBound
        have leftLocal :
            HasLocalRelevantNeighborDepthBound left slack := by
          intro key insideLower insideUpper
          have root_lt_upper : root < upper := by
            have := right.lower_le_upper
            omega
          obtain ⟨leftNull, rightNull⟩ :=
            neighborBound key insideLower (by omega)
          constructor
          · rw [Splay.Tree.BST.externalDepth_node_of_lt_root left right
                (by omega)] at leftNull
            rw [Splay.Tree.BST.depth_node_of_lt_root left right insideUpper]
                at leftNull
            omega
          · rw [Splay.Tree.BST.externalDepth_node_of_lt_root left right
                (by omega)] at rightNull
            rw [Splay.Tree.BST.depth_node_of_lt_root left right insideUpper]
                at rightNull
            omega
        have rightLocal :
            HasLocalRelevantNeighborDepthBound right slack := by
          intro key insideLower insideUpper
          have lower_le_root : lower ≤ root :=
            left.lower_le_upper
          obtain ⟨leftNull, rightNull⟩ :=
            neighborBound key (by omega) insideUpper
          have root_lt_key : root < key := by omega
          constructor
          · rw [Splay.Tree.BST.externalDepth_node_of_root_lt left right
                (by omega)] at leftNull
            rw [Splay.Tree.BST.depth_node_of_root_lt left right root_lt_key]
                at leftNull
            omega
          · rw [Splay.Tree.BST.externalDepth_node_of_root_lt left right
                (by omega)] at rightNull
            rw [Splay.Tree.BST.depth_node_of_root_lt left right root_lt_key]
                at rightNull
            omega
        have rootBounds :=
          neighborBound root left.lower_le_upper (by
            have := right.lower_le_upper
            omega)
        refine ⟨?_, ?_, ihLeft.mpr leftLocal, ihRight.mpr rightLocal⟩
        · have leftRootBound := rootBounds.1
          rw [Splay.Tree.BST.externalDepth_node_of_lt_root left right
                (by omega),
              externalDepth_upperBoundary_eq_rightBoundaryDepth,
              Splay.Tree.BST.depth_root] at leftRootBound
          simpa using leftRootBound
        · have rightRootBound := rootBounds.2
          rw [Splay.Tree.BST.externalDepth_node_of_root_lt left right
                (by omega)] at rightRootBound
          rw [show 2 * root + 2 = 2 * (root + 1) by omega,
              externalDepth_lowerBoundary_eq_leftBoundaryDepth,
              Splay.Tree.BST.depth_root] at rightRootBound
          simpa using rightRootBound

/--
On a full comparison tree, the interval-polymorphic condition is definitionally
the repository's structural adjacent-null invariant.
-/
theorem localNeighborDepth_iff_relevantNeighborDepth
    {n slack : ℕ} (tree : BST 0 n) :
    HasLocalRelevantNeighborDepthBound tree slack ↔
      HasRelevantNeighborDepthBound tree slack := by
  constructor
  · intro neighborBound key
    simpa [Splay.Rank.leftNullPos, Splay.Rank.rightNullPos] using
      neighborBound key.val (Nat.zero_le _) key.isLt
  · intro relevant key insideLower insideUpper
    let finiteKey : Fin n := ⟨key, insideUpper⟩
    simpa [finiteKey, Splay.Rank.leftNullPos, Splay.Rank.rightNullPos] using
      relevant finiteKey

/--
Kernel-checked form of the manuscript's riblessness corollary: the exact
proper-rib invariant is equivalent to the structural condition consumed by
the later splay proof.
-/
theorem hasBoundedMinorRibs_iff_relevantNeighborDepth
    {n slack : ℕ} (tree : BST 0 n) :
    HasBoundedMinorRibs tree slack ↔
      HasRelevantNeighborDepthBound tree slack :=
  (hasBoundedMinorRibs_iff_localNeighborDepth tree).trans
    (localNeighborDepth_iff_relevantNeighborDepth tree)

/--
One arbitrary rotation can worsen the adjacent-null slack by at most two.

One unit accounts for an adjacent null moving down, and one for the
corresponding value key moving up.  The manuscript's rib-folding phase must
do better over a long execution—namely keep one fixed slack—but this lemma
closes the exact local rotation arithmetic needed by such a proof.
-/
theorem HasRelevantNeighborDepthBound.rotate
    {n depth slack : ℕ} {before after : BST 0 n}
    (bound : HasRelevantNeighborDepthBound before slack)
    (rotation : Splay.Tree.BST.RotationAt depth before after) :
    HasRelevantNeighborDepthBound after (slack + 2) := by
  intro key
  have beforeBound := bound key
  have leftShift :=
    rotation.externalDepth_within_one
      (Splay.Rank.leftNullPos key).val
  have rightShift :=
    rotation.externalDepth_within_one
      (Splay.Rank.rightNullPos key).val
  have valueShift :=
    rotation.externalDepth_within_one
      (Splay.Rank.valuePos key).val
  have beforeValue :
      before.externalDepth (Splay.Rank.valuePos key).val =
        before.depth key.val :=
    externalDepth_value_eq_depth before (Nat.zero_le _) key.isLt
  have afterValue :
      after.externalDepth (Splay.Rank.valuePos key).val =
        after.depth key.val :=
    externalDepth_value_eq_depth after (Nat.zero_le _) key.isLt
  constructor <;> omega

/-- The same local preservation theorem in exact proper-rib language. -/
theorem HasBoundedMinorRibs.rotate
    {n depth slack : ℕ} {before after : BST 0 n}
    (bound : HasBoundedMinorRibs before slack)
    (rotation : Splay.Tree.BST.RotationAt depth before after) :
    HasBoundedMinorRibs after (slack + 2) := by
  apply (hasBoundedMinorRibs_iff_relevantNeighborDepth after).mpr
  exact
    HasRelevantNeighborDepthBound.rotate
      ((hasBoundedMinorRibs_iff_relevantNeighborDepth before).mp bound)
      rotation

end Splay.Accounting.OfflineNormalForm
