import Splay.Accounting.OfflineRibRepresentation

/-!
# Height distortion under rib replacement

The payload at inorder position `i` need not pay the entire stack height.
Bounded ribs instead put it at depth at most a constant times `i + 1`.
The two frontier profiles below retain this positional information. They
yield a linear height distortion for the existing physical folded stacks.
-/

namespace Splay.Accounting.OfflineConnectedSupport

open Splay.Tree OfflineNormalForm OfflineNormalForm.RibStack

namespace SupportFrontier

/-- Maximum payload height plus `slope` times its rank from the left. -/
def risingHeight (slope : ℕ) {lower upper : ℕ} : SupportFrontier lower upper → ℕ
  | .last tree => tree.height
  | .next tree tail => max tree.height (tail.risingHeight slope + slope)

/-- Maximum payload height plus `slope` times its rank from the right. -/
def fallingHeight (slope : ℕ) {lower upper : ℕ} : SupportFrontier lower upper → ℕ
  | .last tree => tree.height
  | .next tree tail => max (tree.height + slope * (tail.card + 1)) (tail.fallingHeight slope)

theorem risingHeight_append {lower root upper : ℕ} (slope : ℕ)
    (left : SupportFrontier lower root) (right : SupportFrontier (root + 1) upper) :
    (left.append right).risingHeight slope =
      max (left.risingHeight slope) (right.risingHeight slope + slope * (left.card + 1)) := by
  induction left with
  | last tree => simp [append, risingHeight, card]
  | next tree tail ih =>
      simp only [append, risingHeight, card, ih, Nat.mul_add, Nat.mul_one]
      omega

theorem fallingHeight_append {lower root upper : ℕ} (slope : ℕ)
    (left : SupportFrontier lower root) (right : SupportFrontier (root + 1) upper) :
    (left.append right).fallingHeight slope =
      max (left.fallingHeight slope + slope * (right.card + 1)) (right.fallingHeight slope) := by
  induction left with
  | last tree => rfl
  | next tree tail ih =>
      simp only [append, fallingHeight, card_append, ih, Nat.mul_add, Nat.mul_one]
      omega

end SupportFrontier

namespace Substitution

/-- Bounded proper ribs control the depth of each payload by its inorder
position, with the initial left spine charged only once. -/
theorem height_le_risingHeight {templateLower templateUpper lower upper slack : ℕ}
    {template : BST templateLower templateUpper} {actual : BST lower upper}
    (substitution : Substitution template actual) (ribs : HasBoundedMinorRibs template slack) :
    actual.height ≤ substitution.selected.frontier.risingHeight slack + leftBoundaryDepth template := by
  induction substitution with
  | leaf => simp [selected, RootPrefix.frontier, SupportFrontier.risingHeight, leftBoundaryDepth]
  | node left right ihL ihR =>
      have leftBound := ihL ribs.2.2.1
      have rightBound := ihR ribs.2.2.2
      have rightSpine := ribs.2.1
      have shift : slack ≤ slack * (left.selected.frontier.card + 1) := by
        nlinarith
      simp only [selected, RootPrefix.frontier, SupportFrontier.risingHeight_append,
        BST.height, leftBoundaryDepth]
      omega

/-- Symmetric positional bound, measured from the right end of the frontier. -/
theorem height_le_fallingHeight {templateLower templateUpper lower upper slack : ℕ}
    {template : BST templateLower templateUpper} {actual : BST lower upper}
    (substitution : Substitution template actual) (ribs : HasBoundedMinorRibs template slack) :
    actual.height ≤ substitution.selected.frontier.fallingHeight slack + rightBoundaryDepth template := by
  induction substitution with
  | leaf => simp [selected, RootPrefix.frontier, SupportFrontier.fallingHeight, rightBoundaryDepth]
  | node left right ihL ihR =>
      have leftBound := ihL ribs.2.2.1
      have rightBound := ihR ribs.2.2.2
      have leftSpine := ribs.1
      have shift : slack ≤ slack * (right.selected.frontier.card + 1) := by
        nlinarith
      simp only [selected, RootPrefix.frontier, SupportFrontier.fallingHeight_append,
        BST.height, rightBoundaryDepth]
      omega

end Substitution

theorem RibSpineMap.positionalHeight_le
    {Relation : Bool → {lo hi : ℕ} → BST lo hi → BST lo hi → Type}
    {lower upper limit : ℕ} {side : Bool} {before : BST lower upper}
    {frontier : SupportFrontier lower upper}
    (mapped : RibSpineMap @Relation side before frontier) (fits : before.size ≤ limit)
    (convert : ∀ {lo hi : ℕ} {source target : BST lo hi}, Relation (!side) source target →
      source.size < limit → target.height ≤ 13 * source.height) :
    (if side then frontier.fallingHeight 7 else frontier.risingHeight 7) ≤ 13 * before.height - 6 := by
  induction mapped with
  | empty side boundary =>
      cases side <;> simp [SupportFrontier.risingHeight, SupportFrontier.fallingHeight, BST.height]
  | right payload rest ih =>
      have payloadBound := convert payload (by simp only [BST.size] at fits; omega)
      have restBound := ih (by simp only [BST.size] at fits; omega) convert
      simp only [Bool.false_eq_true, if_false, SupportFrontier.risingHeight, BST.height] at *
      omega
  | left rest payload ih =>
      have payloadBound := convert payload (by simp only [BST.size] at fits; omega)
      have restBound := ih (by simp only [BST.size] at fits; omega) convert
      simp only [if_true, SupportFrontier.fallingHeight_append, SupportFrontier.fallingHeight,
        SupportFrontier.card, Nat.zero_add, Nat.mul_one, BST.height] at *
      omega

/-- Rib replacement has a constant height distortion. This sharpens the
earlier estimate that multiplied the source height by a logarithm. All stack
histories are covered; no canonical rebuilding or new balancing is assumed. -/
theorem RibRepresentation.height_le_thirteen {capacity lower upper : ℕ} {side : Bool}
    {before after : BST lower upper} (representation : RibRepresentation capacity side before after) :
    after.height ≤ 13 * before.height := by
  generalize sizeEq : before.size = count
  induction count using Nat.strong_induction_on generalizing lower upper side with
  | h count ih =>
      by_cases empty : before.height = 0
      · have sourceSize : before.size = 0 := by
          cases before with
          | empty => rfl
          | node left right => simp [BST.height] at empty
        have sourceInterval := before.size_add_lower_eq_upper
        have targetInterval := after.size_add_lower_eq_upper
        have targetHeight := after.height_le_size
        omega
      · cases representation with
        | minimum mapped stack =>
            have positional := mapped.positionalHeight_le (limit := count) (by omega)
              (fun child smaller => ih _ smaller child rfl)
            have height := stack.filling.height_le_risingHeight stack.shaped.geometry.1
            rw [stack.frontier_eq] at height
            have boundary := stack.shaped.geometry.2.1
            simp only [Bool.false_eq_true, if_false] at positional
            omega
        | maximum mapped stack =>
            have positional := mapped.positionalHeight_le (limit := count) (by omega)
              (fun child smaller => ih _ smaller child rfl)
            have height := stack.filling.height_le_fallingHeight
              (stack.reflection.ribs_iff.mpr stack.shaped.geometry.1)
            rw [stack.frontier_eq] at height
            have boundary := stack.shaped.geometry.2.1
            have reflected := stack.reflection.boundary_eq
            simp only [if_true] at positional
            omega

end Splay.Accounting.OfflineConnectedSupport
