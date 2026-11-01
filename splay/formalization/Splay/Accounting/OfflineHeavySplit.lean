import Splay.Accounting.OfflineHeavyJoin
import Splay.Accounting.RibStackExactPop

namespace Splay.Accounting.OfflineConnectedSupport

open Splay.Tree FrontierFolding OfflineNormalForm.RibStack

private theorem empty_interval {boundary : ℕ} (tree : BST boundary boundary) :
    tree = .empty boundary := by
  cases tree with
  | empty => rfl
  | node left right =>
      have lo := left.lower_le_upper
      have hi := right.lower_le_upper
      omega

namespace HeavyRepresentation

/-- Expose the original root by popping exactly one path stack. The two
resulting children retain their actual representation histories. -/
theorem exists_split {capacity lower upper : ℕ} {before after : BST lower upper}
    (representation : HeavyRepresentation capacity before after) (positive : 0 < before.size) :
    ∃ (root : ℕ) (left : BST lower root) (right : BST (root + 1) upper)
      (actualLeft : BST lower root) (actualRight : BST (root + 1) upper)
      (leftRep : HeavyRepresentation capacity left actualLeft)
      (rightRep : HeavyRepresentation capacity right actualRight) (cost : ℕ),
      before = .node left right ∧ HasSupportedPath after (.node actualLeft actualRight) cost cost ∧
      cost ≤ heavyUnitCost capacity ∧
      cost + leftRep.potential + rightRep.potential ≤ representation.potential + 115 := by
  cases representation with
  | empty => simp [BST.size] at positive
  | path mapped long leftStack rightStack =>
      cases mapped with
      | hole =>
          refine ⟨_, .empty _, .empty _, .empty _, .empty _, .empty _, .empty _, 0, rfl, ?_, Nat.zero_le _, ?_⟩
          · rw [empty_interval leftStack.tree, empty_interval rightStack.tree]
            exact .refl _
          · simp [potential]
      | low payload tail =>
          rename_i originalPayload actualPayload original replacement
          obtain ⟨stack, path, amortized⟩ := MinimumStack.exists_pop_next actualPayload
            (replacement.expose (leafSplit _)).leftSelected.frontier leftStack
          let result : HeavyRepresentation capacity _ _ :=
            .path tail long.2 stack rightStack
          refine ⟨_, _, _, _, _, payload, result, 16 * Digits.popCost 0 leftStack.digits + 3,
            rfl, ?_, ?_, ?_⟩
          · exact ((path.leftContext rightStack.tree).trans
              (HasSupportedPath.rootRight actualPayload stack.tree rightStack.tree)).mono
                (by omega) (by omega)
          · apply counterPop_le_unit
            rw [leftStack.value_eq_card]
            have room := leftStack.virtualLower_add_card
            omega
          · simp only [result, potential, Context.PayloadMap.heavyPotential,
              MinimumStack.potential, MaximumStack.potential] at amortized ⊢
            omega
      | high initial payload =>
          rename_i original replacement originalPayload actualPayload
          obtain ⟨stack, path, amortized⟩ := MaximumStack.exists_pop_last
            (replacement.expose (leafSplit _)).rightSelected.frontier actualPayload rightStack
          let result : HeavyRepresentation capacity _ _ :=
            .path initial long.2 leftStack stack
          refine ⟨_, _, _, _, _, result, payload, 16 * Digits.popCost 0 rightStack.digits + 3,
            rfl, ?_, ?_, ?_⟩
          · exact ((path.rightContext leftStack.tree).trans
              (HasSupportedPath.rootLeft leftStack.tree stack.tree actualPayload)).mono
                (by omega) (by omega)
          · apply counterPop_le_unit
            rw [rightStack.value_eq_card]
            have room := rightStack.virtualLower_add_card
            omega
          · simp only [result, potential, Context.PayloadMap.heavyPotential,
              MinimumStack.potential, MaximumStack.potential] at amortized ⊢
            omega

/-- The exposed children are those of the given original node. -/
theorem exists_split_node {capacity lower root upper : ℕ}
    {left : BST lower root} {right : BST (root + 1) upper} {after : BST lower upper}
    (representation : HeavyRepresentation capacity (.node left right) after) :
    ∃ (actualLeft : BST lower root) (actualRight : BST (root + 1) upper)
      (leftRep : HeavyRepresentation capacity left actualLeft)
      (rightRep : HeavyRepresentation capacity right actualRight) (cost : ℕ),
      HasSupportedPath after (.node actualLeft actualRight) cost cost ∧
      cost ≤ heavyUnitCost capacity ∧
      cost + leftRep.potential + rightRep.potential ≤ representation.potential + 115 := by
  obtain ⟨key, originalLeft, originalRight, actualLeft, actualRight, leftRep, rightRep,
    cost, same, path, bound, amortized⟩ := representation.exists_split (by simp [BST.size])
  cases same
  exact ⟨actualLeft, actualRight, leftRep, rightRep, cost, path, bound, amortized⟩

end HeavyRepresentation

end Splay.Accounting.OfflineConnectedSupport
