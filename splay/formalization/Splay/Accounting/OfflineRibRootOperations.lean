import Splay.Accounting.OfflineRibPotential
import Splay.Accounting.OfflineRibHeight

namespace Splay.Accounting.OfflineConnectedSupport

open Splay.Tree OfflineNormalForm OfflineNormalForm.RibStack

def ribUnitCost (capacity : ℕ) : ℕ := 64 * (Nat.clog 2 (capacity + 1) + 1) ^ 2

private theorem push_le_unit {capacity : ℕ} (digits : List Digits.Digit) (fits : Digits.value digits ≤ capacity) :
    64 * Digits.pushCost 0 digits ≤ ribUnitCost capacity := by
  have cost := Digits.pushCost_le_logSquared digits
  have levels := Nat.clog_mono_right 2 (Nat.add_le_add_right fits 1)
  have powers := Nat.pow_le_pow_left (Nat.add_le_add_right levels 1) 2
  dsimp [ribUnitCost]
  omega

private theorem pop_le_unit {capacity : ℕ} (digits : List Digits.Digit) (fits : Digits.value digits ≤ capacity) :
    64 * Digits.popCost 0 digits ≤ ribUnitCost capacity := by
  have cost := Digits.popCost_le_logSquared digits
  have levels := Nat.clog_mono_right 2 (Nat.add_le_add_right fits 1)
  have powers := Nat.pow_le_pow_left (Nat.add_le_add_right levels 1) 2
  dsimp [ribUnitCost]
  omega

namespace RibRepresentation

def empty (capacity : ℕ) (side : Bool) (boundary : ℕ) :
    RibRepresentation capacity side (.empty boundary) (.empty boundary) :=
  match side with
  | false => .minimum (.empty false boundary) (FoldedMinimumStack.empty capacity boundary)
  | true => .maximum (.empty true boundary) (FoldedMaximumStack.empty capacity boundary)

theorem exists_join {capacity lower root upper : ℕ}
    {left actualLeft : BST lower root} {right actualRight : BST (root + 1) upper}
    (side : Bool) (leftRep : RibRepresentation capacity true left actualLeft)
    (rightRep : RibRepresentation capacity false right actualRight) (fits : (BST.node left right).size ≤ capacity) :
    ∃ (after : BST lower upper) (result : RibRepresentation capacity side (.node left right) after) (cost : ℕ),
      HasSupportedPath (.node actualLeft actualRight) after cost cost ∧ cost ≤ ribUnitCost capacity ∧
      cost + result.potential ≤ leftRep.potential + rightRep.potential + 448 := by
  cases side with
  | false =>
      cases rightRep with
      | minimum mapped stack =>
          have card := mapped.card_le_size
          obtain ⟨next, _, path, amortized⟩ := stack.exists_push actualLeft (by simp only [BST.size] at fits; omega)
          let result := RibRepresentation.minimum (.right leftRep mapped) next
          refine ⟨_, result, 64 * Digits.pushCost 0 stack.digits, path, ?_, ?_⟩
          · apply push_le_unit
            rw [stack.value_eq_card]
            simp only [BST.size] at fits
            omega
          · simp only [result, potential, RibSpineMap.ribPotential,
              FoldedMinimumStack.potential] at amortized ⊢
            omega
  | true =>
      cases leftRep with
      | maximum mapped stack =>
          have card := mapped.card_le_size
          obtain ⟨next, _, path, amortized⟩ := stack.exists_push actualRight (by simp only [BST.size] at fits; omega)
          let result := RibRepresentation.maximum (.left mapped rightRep) next
          refine ⟨_, result, 64 * Digits.pushCost 0 stack.digits, path, ?_, ?_⟩
          · apply push_le_unit
            rw [stack.value_eq_card]
            simp only [BST.size] at fits
            omega
          · simp only [result, potential, RibSpineMap.ribPotential,
              FoldedMaximumStack.potential] at amortized ⊢
            omega

theorem exists_split_node {capacity lower root upper : ℕ} {side : Bool}
    {left : BST lower root} {right : BST (root + 1) upper} {actual : BST lower upper}
    (representation : RibRepresentation capacity side (.node left right) actual) :
    ∃ (actualLeft : BST lower root) (actualRight : BST (root + 1) upper)
      (leftRep : RibRepresentation capacity true left actualLeft)
      (rightRep : RibRepresentation capacity false right actualRight) (cost : ℕ),
      HasSupportedPath actual (.node actualLeft actualRight) cost cost ∧ cost ≤ ribUnitCost capacity ∧
      cost + leftRep.potential + rightRep.potential ≤ representation.potential + 448 := by
  cases representation with
  | minimum mapped stack =>
      cases mapped with
      | right payload rest =>
          obtain ⟨next, path, amortized⟩ := stack.exists_pop_next _ _
          let result := RibRepresentation.minimum rest next
          refine ⟨_, _, payload, result, 64 * Digits.popCost 0 stack.digits, path, ?_, ?_⟩
          · apply pop_le_unit
            rw [stack.value_eq_card]
            have room := stack.virtualLower_add_card
            omega
          · simp only [result, potential, RibSpineMap.ribPotential,
              FoldedMinimumStack.potential] at amortized ⊢
            omega
  | maximum mapped stack =>
      cases mapped with
      | left rest payload =>
          obtain ⟨next, path, amortized⟩ := stack.exists_pop_last _ _
          let result := RibRepresentation.maximum rest next
          refine ⟨_, _, result, payload, 64 * Digits.popCost 0 stack.digits, path, ?_, ?_⟩
          · apply pop_le_unit
            rw [stack.value_eq_card]
            have room := stack.virtualLower_add_card
            omega
          · simp only [result, potential, RibSpineMap.ribPotential,
              FoldedMaximumStack.potential] at amortized ⊢
            omega

private theorem empty_interval {boundary : ℕ} (tree : BST boundary boundary) : tree = .empty boundary := by
  cases tree with
  | empty => rfl
  | node left right => have lo := left.lower_le_upper; have hi := right.lower_le_upper; omega

/-- Reorienting a hanging subtree requires only its two root stack operations. -/
theorem exists_reorient {capacity lower upper : ℕ} {side : Bool} {before actual : BST lower upper}
    (targetSide : Bool) (representation : RibRepresentation capacity side before actual) (fits : before.size ≤ capacity) :
    ∃ (after : BST lower upper) (result : RibRepresentation capacity targetSide before after) (cost : ℕ),
      HasSupportedPath actual after cost cost ∧ cost ≤ 2 * ribUnitCost capacity ∧
      cost + result.potential ≤ representation.potential + 896 := by
  cases before with
  | empty =>
      let result := empty capacity targetSide lower
      have credit := result.potential_le_size
      refine ⟨.empty lower, result, 0, ?_, by omega, ?_⟩
      · rw [empty_interval actual]
        exact .refl _
      · simp only [BST.size] at credit
        omega
  | node left right =>
      obtain ⟨actualLeft, actualRight, leftRep, rightRep, c₁, p₁, b₁, a₁⟩ := representation.exists_split_node
      obtain ⟨after, result, c₂, p₂, b₂, a₂⟩ := exists_join targetSide leftRep rightRep fits
      exact ⟨after, result, c₁ + c₂, p₁.trans p₂, by omega, by omega⟩

end RibRepresentation

end Splay.Accounting.OfflineConnectedSupport
