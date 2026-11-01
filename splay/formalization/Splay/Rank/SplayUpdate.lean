import Splay.Rank.RotationUpdate
import Splay.Tree.SplayStep

namespace Splay.Rank

open Splay.Lazy

/--
An exact signed external-depth update between two comparison trees.

Unlike `Snapshot.ofTree`, this local form works for a rotated subtree whose
lower index need not be zero.  It is therefore closed under the contexts in
`Tree.BST.RotationAt`.
-/
def ExactTreeRankUpdate {lower upper : ℕ}
    (before after : Tree.BST lower upper) (shiftAt : ℕ → ℤ) : Prop :=
  ∀ position,
    (after.externalDepth position : ℤ) =
      before.externalDepth position + shiftAt position

/-- Every pointwise shift of one rotation is one of `-1`, `0`, and `1`. -/
def IsUnitRotationShift (shiftAt : ℕ → ℤ) : Prop :=
  ∀ position,
    shiftAt position = -1 ∨
      shiftAt position = 0 ∨
      shiftAt position = 1

/--
A pointwise shift obtained by composing two rotations.  Listing the five
integer values, rather than merely giving bounds, records the exact discrete
classification used by a double splay step.
-/
def IsDoubleRotationShift (shiftAt : ℕ → ℤ) : Prop :=
  ∀ position,
    shiftAt position = -2 ∨
      shiftAt position = -1 ∨
      shiftAt position = 0 ∨
      shiftAt position = 1 ∨
      shiftAt position = 2

namespace IsUnitRotationShift

/-- The pointwise sum of two single-rotation shifts is a double shift. -/
theorem add {firstShift secondShift : ℕ → ℤ}
    (first : IsUnitRotationShift firstShift)
    (second : IsUnitRotationShift secondShift) :
    IsDoubleRotationShift
      (fun position => firstShift position + secondShift position) := by
  intro position
  rcases first position with h | h | h <;>
    rcases second position with h' | h' | h' <;>
    simp_all

end IsUnitRotationShift

namespace ExactTreeRankUpdate

/-- Exact tree-rank updates compose by pointwise addition of their shifts. -/
theorem comp {lower upper : ℕ}
    {before middle after : Tree.BST lower upper}
    {firstShift secondShift : ℕ → ℤ}
    (first : ExactTreeRankUpdate before middle firstShift)
    (second : ExactTreeRankUpdate middle after secondShift) :
    ExactTreeRankUpdate before after
      (fun position => firstShift position + secondShift position) := by
  intro position
  calc
    (after.externalDepth position : ℤ) =
        middle.externalDepth position + secondShift position :=
      second position
    _ =
        (before.externalDepth position + firstShift position) +
          secondShift position := by rw [first position]
    _ =
        before.externalDepth position +
          (firstShift position + secondShift position) :=
      Int.add_assoc _ _ _

/--
An exact full-tree update induces the `HeapView.RankShift` used by the lazy
rank-update interface, whenever the two views carry the corresponding
`Snapshot.ofTree` ranks.
-/
theorem heapViewRankShift {n : ℕ}
    {beforeTree afterTree : Tree.BST 0 n}
    {shiftAt : ℕ → ℤ}
    (update : ExactTreeRankUpdate beforeTree afterTree shiftAt)
    {beforeView afterView : HeapView n}
    (beforeRanks :
      beforeView.rank = (Snapshot.ofTree beforeTree).rank)
    (afterRanks :
      afterView.rank = (Snapshot.ofTree afterTree).rank)
    (element : Element n) :
    HeapView.RankShift beforeView afterView element
      (shiftAt element.val) := by
  unfold HeapView.RankShift
  rw [beforeRanks, afterRanks]
  change
    (afterTree.externalDepth element.val : ℤ) =
      beforeTree.externalDepth element.val + shiftAt element.val
  exact update element.val

end ExactTreeRankUpdate

end Splay.Rank

namespace Splay.Tree.BST.RootRotation

open Splay.Lazy
open Splay.Rank

/--
Every root rotation has an exact three-sector rank classification.  The
witness is definitionally the `shiftAt` function from `RotationUpdate`.
-/
theorem existsExactTreeRankUpdate {lower upper : ℕ}
    {before after : Tree.BST lower upper}
    (step : RootRotation before after) :
    ∃ shiftAt : ℕ → ℤ,
      ExactTreeRankUpdate before after shiftAt ∧
        IsUnitRotationShift shiftAt := by
  cases step with
  | @right promoted demoted upper a b c =>
      let shiftAt :=
        Snapshot.RightRotationRanks.shiftAt promoted demoted
      refine ⟨shiftAt, ?_, ?_⟩
      · intro position
        unfold shiftAt
        unfold Snapshot.RightRotationRanks.shiftAt
        split
        · next inPromoted =>
            have depth :=
              right_externalDepth_promotedSector
                a b c inPromoted
            omega
        · next notPromoted =>
            split
            · next inMiddle =>
                have depth :=
                  right_externalDepth_middleSector
                    a b c (by omega) inMiddle
                omega
            · next inDemoted =>
                have positionInDemoted :
                    2 * demoted + 1 ≤ position := by omega
                have depth :=
                  right_externalDepth_demotedSector
                    (position := position) a b c positionInDemoted
                omega
      · intro position
        unfold shiftAt
        unfold Snapshot.RightRotationRanks.shiftAt
        by_cases inPromoted : position ≤ 2 * promoted + 1
        · simp [inPromoted]
        · by_cases inMiddle : position < 2 * demoted + 1
          · simp [inPromoted, inMiddle]
          · simp [inPromoted, inMiddle]
  | @left promoted demoted upper a b c =>
      let shiftAt :=
        Snapshot.LeftRotationRanks.shiftAt promoted demoted
      refine ⟨shiftAt, ?_, ?_⟩
      · intro position
        unfold shiftAt
        unfold Snapshot.LeftRotationRanks.shiftAt
        split
        · next inDemoted =>
            have depth :=
              left_externalDepth_demotedSector
                a b c inDemoted
            omega
        · next notDemoted =>
            split
            · next inMiddle =>
                have depth :=
                  left_externalDepth_middleSector
                    a b c (by omega) inMiddle
                omega
            · next inPromoted =>
                have positionInPromoted :
                    2 * demoted + 1 ≤ position := by omega
                have depth :=
                  left_externalDepth_promotedSector
                    (position := position) a b c positionInPromoted
                omega
      · intro position
        unfold shiftAt
        unfold Snapshot.LeftRotationRanks.shiftAt
        by_cases inDemoted : position ≤ 2 * promoted + 1
        · simp [inDemoted]
        · by_cases inMiddle : position < 2 * demoted + 1
          · simp [inDemoted, inMiddle]
          · simp [inDemoted, inMiddle]

end Splay.Tree.BST.RootRotation

namespace Splay.Tree.BST.RotationAt

open Splay.Rank

/--
Every rotation at an arbitrary depth has an exact pointwise rank update.
Passing under a context retains the inner three-sector update on the rotated
side and extends it by zero on the untouched side and the enclosing root.
-/
theorem existsExactTreeRankUpdate {depth lower upper : ℕ}
    {before after : Tree.BST lower upper}
    (step : RotationAt depth before after) :
    ∃ shiftAt : ℕ → ℤ,
      ExactTreeRankUpdate before after shiftAt ∧
        IsUnitRotationShift shiftAt := by
  induction step with
  | root rootStep =>
      exact rootStep.existsExactTreeRankUpdate
  | @leftContext depth lower root upper before after step right ih =>
      obtain ⟨innerShift, innerUpdate, innerUnit⟩ := ih
      let shiftAt : ℕ → ℤ := fun position =>
        if position < 2 * root + 1 then innerShift position else 0
      refine ⟨shiftAt, ?_, ?_⟩
      · intro position
        by_cases inLeft : position < 2 * root + 1
        · rw [Tree.BST.externalDepth_node_of_lt_root
              before right inLeft]
          rw [Tree.BST.externalDepth_node_of_lt_root
              after right inLeft]
          have inner := innerUpdate position
          simp only [shiftAt, if_pos inLeft]
          omega
        · by_cases atRoot : position = 2 * root + 1
          · subst position
            simp only [Tree.BST.externalDepth_root]
            simp [shiftAt]
          · have inRight : 2 * root + 1 < position := by omega
            rw [Tree.BST.externalDepth_node_of_root_lt
                before right inRight]
            rw [Tree.BST.externalDepth_node_of_root_lt
                after right inRight]
            simp [shiftAt, inLeft]
      · intro position
        by_cases inLeft : position < 2 * root + 1
        · simpa only [shiftAt, if_pos inLeft] using
            innerUnit position
        · simp [shiftAt, inLeft]
  | @rightContext depth lower root upper left before after step ih =>
      obtain ⟨innerShift, innerUpdate, innerUnit⟩ := ih
      let shiftAt : ℕ → ℤ := fun position =>
        if 2 * root + 1 < position then innerShift position else 0
      refine ⟨shiftAt, ?_, ?_⟩
      · intro position
        by_cases inRight : 2 * root + 1 < position
        · rw [Tree.BST.externalDepth_node_of_root_lt
              left before inRight]
          rw [Tree.BST.externalDepth_node_of_root_lt
              left after inRight]
          have inner := innerUpdate position
          simp only [shiftAt, if_pos inRight]
          omega
        · by_cases atRoot : position = 2 * root + 1
          · subst position
            simp only [Tree.BST.externalDepth_root]
            simp [shiftAt]
          · have inLeft : position < 2 * root + 1 := by omega
            rw [Tree.BST.externalDepth_node_of_lt_root
                left before inLeft]
            rw [Tree.BST.externalDepth_node_of_lt_root
                left after inLeft]
            simp [shiftAt, inRight]
      · intro position
        by_cases inRight : 2 * root + 1 < position
        · simpa only [shiftAt, if_pos inRight] using
            innerUnit position
        · simp [shiftAt, inRight]

end Splay.Tree.BST.RotationAt

namespace Splay.Tree.BST.Zig

open Splay.Lazy
open Splay.Rank

/--
A zig inherits the exact three-sector rank classification of its single root
rotation.
-/
theorem existsExactTreeRankUpdate {key lower upper : ℕ}
    {before after : Tree.BST lower upper}
    (step : Zig key before after) :
    ∃ shiftAt : ℕ → ℤ,
      ExactTreeRankUpdate before after shiftAt ∧
        IsUnitRotationShift shiftAt :=
  step.toRootRotation.existsExactTreeRankUpdate

/--
Full-tree `Snapshot.ofTree` ranks turn the exact zig classification directly
into the lazy model's signed `HeapView.RankShift` relation.
-/
theorem existsHeapViewRankShiftClassification {key n : ℕ}
    {beforeTree afterTree : Tree.BST 0 n}
    (step : Zig key beforeTree afterTree)
    {beforeView afterView : HeapView n}
    (beforeRanks :
      beforeView.rank = (Snapshot.ofTree beforeTree).rank)
    (afterRanks :
      afterView.rank = (Snapshot.ofTree afterTree).rank) :
    ∃ shiftAt : ℕ → ℤ,
      IsUnitRotationShift shiftAt ∧
        ∀ element : Element n,
          HeapView.RankShift beforeView afterView element
            (shiftAt element.val) := by
  obtain ⟨shiftAt, update, unit⟩ :=
    step.existsExactTreeRankUpdate
  refine ⟨shiftAt, unit, ?_⟩
  intro element
  exact
    update.heapViewRankShift beforeRanks afterRanks element

end Splay.Tree.BST.Zig

namespace Splay.Tree.BST.DoubleRotation

open Splay.Lazy
open Splay.Rank

/--
Kernel-checked operational bridge for a double splay step: its intermediate
tree carries one exact unit-shift classification from each constituent
rotation.
-/
theorem existsTwoExactTreeRankUpdates {key lower upper : ℕ}
    {before after : Tree.BST lower upper}
    (step : DoubleRotation key before after) :
    ∃ (middle : Tree.BST lower upper)
        (firstShift secondShift : ℕ → ℤ),
      ExactTreeRankUpdate before middle firstShift ∧
        IsUnitRotationShift firstShift ∧
        ExactTreeRankUpdate middle after secondShift ∧
        IsUnitRotationShift secondShift := by
  obtain ⟨middle, _, _, firstRotation, secondRotation⟩ :=
    step.toTwoRotations
  obtain ⟨firstShift, firstUpdate, firstUnit⟩ :=
    firstRotation.existsExactTreeRankUpdate
  obtain ⟨secondShift, secondUpdate, secondUnit⟩ :=
    secondRotation.existsExactTreeRankUpdate
  exact
    ⟨middle, firstShift, secondShift,
      firstUpdate, firstUnit, secondUpdate, secondUnit⟩

/--
The two constituent updates compose to an exact before-to-after update.  Its
pointwise shift is definitionally `firstShift + secondShift`, hence belongs to
the five-value double-rotation classification.
-/
theorem existsExactTreeRankUpdate {key lower upper : ℕ}
    {before after : Tree.BST lower upper}
    (step : DoubleRotation key before after) :
    ∃ shiftAt : ℕ → ℤ,
      ExactTreeRankUpdate before after shiftAt ∧
        IsDoubleRotationShift shiftAt := by
  obtain
      ⟨middle, firstShift, secondShift,
        firstUpdate, firstUnit, secondUpdate, secondUnit⟩ :=
    step.existsTwoExactTreeRankUpdates
  let shiftAt : ℕ → ℤ := fun position =>
    firstShift position + secondShift position
  refine ⟨shiftAt, ?_, ?_⟩
  · simpa only [shiftAt] using firstUpdate.comp secondUpdate
  · simpa only [shiftAt] using firstUnit.add secondUnit

/--
When the double-rotation pattern is applied to the comparison/rank-source
tree, it yields one exact signed `HeapView.RankShift` for every external
element, with shift in `{-2, -1, 0, 1, 2}`.
-/
theorem existsHeapViewRankShiftClassification {key n : ℕ}
    {beforeTree afterTree : Tree.BST 0 n}
    (step : DoubleRotation key beforeTree afterTree)
    {beforeView afterView : HeapView n}
    (beforeRanks :
      beforeView.rank = (Snapshot.ofTree beforeTree).rank)
    (afterRanks :
      afterView.rank = (Snapshot.ofTree afterTree).rank) :
    ∃ shiftAt : ℕ → ℤ,
      IsDoubleRotationShift shiftAt ∧
        ∀ element : Element n,
          HeapView.RankShift beforeView afterView element
            (shiftAt element.val) := by
  obtain ⟨shiftAt, update, double⟩ :=
    step.existsExactTreeRankUpdate
  refine ⟨shiftAt, double, ?_⟩
  intro element
  exact
    update.heapViewRankShift beforeRanks afterRanks element

end Splay.Tree.BST.DoubleRotation
