import Splay.Accounting.LogHeightRibReplacement
import Splay.Accounting.OfflineRibRootOperations

/-!
# Rib stack capacity controlled by source height

A spine has at most as many nodes as the source tree has levels. Reserving
virtual stack keys for that height, instead of the total universe size,
keeps the physical support of each update small enough for sharp simulation.
-/

namespace Splay.Accounting.OfflineConnectedSupport

open Splay.Tree OfflineNormalForm OfflineNormalForm.RibStack

theorem _root_.Splay.Tree.BST.RootRotation.height_le_add_one {lower upper : ℕ}
    {before after : BST lower upper} (rotation : BST.RootRotation before after) :
    after.height ≤ before.height + 1 := by
  cases rotation <;> simp only [BST.height] <;> omega

theorem _root_.Splay.Tree.BST.RotationAt.height_le_add_one {lower upper depth : ℕ}
    {before after : BST lower upper} (rotation : BST.RotationAt depth before after) :
    after.height ≤ before.height + 1 := by
  induction rotation with
  | root rotation => exact rotation.height_le_add_one
  | leftContext rotation right ih => simp only [BST.height]; omega
  | rightContext left rotation ih => simp only [BST.height]; omega

private theorem push_le_unit_of_height {capacity : ℕ} (digits : List Digits.Digit) (fits : Digits.value digits ≤ capacity) :
    64 * Digits.pushCost 0 digits ≤ ribUnitCost capacity := by
  have cost := Digits.pushCost_le_logSquared digits
  have levels := Nat.clog_mono_right 2 (Nat.add_le_add_right fits 1)
  have powers := Nat.pow_le_pow_left (Nat.add_le_add_right levels 1) 2
  dsimp [ribUnitCost]
  omega

theorem RibSpineMap.exists_map_of_height
    {Relation : Bool → {lo hi : ℕ} → BST lo hi → BST lo hi → Type}
    {lower upper limit height : ℕ} (side : Bool) (before : BST lower upper)
    (fits : before.size ≤ limit) (heightBound : before.height ≤ height)
    (realize : ∀ {lo hi : ℕ} (source : BST lo hi), source.size < limit → source.height < height →
      ∃ target : BST lo hi, Nonempty (Relation (!side) source target)) :
    ∃ frontier : SupportFrontier lower upper, Nonempty (RibSpineMap @Relation side before frontier) := by
  induction before generalizing side with
  | empty => exact ⟨_, ⟨.empty side _⟩⟩
  | node left right ihL ihR =>
      simp only [BST.size] at fits
      simp only [BST.height] at heightBound
      cases side with
      | false =>
          obtain ⟨actualLeft, ⟨payload⟩⟩ := realize left (by omega) (by omega)
          obtain ⟨tail, ⟨mapped⟩⟩ := ihR false (by omega) (by omega) realize
          exact ⟨.next actualLeft tail, ⟨.right payload mapped⟩⟩
      | true =>
          obtain ⟨initial, ⟨mapped⟩⟩ := ihL true (by omega) (by omega) realize
          obtain ⟨actualRight, ⟨payload⟩⟩ := realize right (by omega) (by omega)
          exact ⟨initial.append (.last actualRight), ⟨.left mapped payload⟩⟩

namespace RibRepresentation

/-- Initializing a rib stack needs capacity only for the longest source
spine. The existing potential bound remains linear in the number of keys. -/
theorem exists_representation_of_height {lower upper : ℕ} (capacity : ℕ) (side : Bool)
    (before : BST lower upper) (fits : before.height ≤ capacity) :
    ∃ after : BST lower upper, Nonempty (RibRepresentation capacity side before after) := by
  generalize sizeEq : before.size = count
  induction count using Nat.strong_induction_on generalizing lower upper side with
  | h count ih =>
      cases side with
      | false =>
          obtain ⟨frontier, ⟨mapped⟩⟩ := RibSpineMap.exists_map_of_height
            (Relation := @RibRepresentation capacity) false before (limit := count)
            (height := capacity) (by omega) fits
            (fun child smaller short => ih child.size smaller true child (by omega) rfl)
          obtain ⟨stack⟩ := FoldedMinimumStack.exists_initial capacity frontier
            (mapped.card_le_height.trans fits)
          exact ⟨stack.tree, ⟨.minimum mapped stack⟩⟩
      | true =>
          obtain ⟨frontier, ⟨mapped⟩⟩ := RibSpineMap.exists_map_of_height
            (Relation := @RibRepresentation capacity) true before (limit := count)
            (height := capacity) (by omega) fits
            (fun child smaller short => ih child.size smaller false child (by omega) rfl)
          obtain ⟨stack⟩ := FoldedMaximumStack.exists_initial capacity frontier
            (mapped.card_le_height.trans fits)
          exact ⟨stack.tree, ⟨.maximum mapped stack⟩⟩

theorem exists_join_of_height {capacity lower root upper : ℕ}
    {left actualLeft : BST lower root} {right actualRight : BST (root + 1) upper}
    (side : Bool) (leftRep : RibRepresentation capacity true left actualLeft)
    (rightRep : RibRepresentation capacity false right actualRight) (fits : (BST.node left right).height ≤ capacity) :
    ∃ (after : BST lower upper) (result : RibRepresentation capacity side (.node left right) after) (cost : ℕ),
      HasSupportedPath (.node actualLeft actualRight) after cost cost ∧ cost ≤ ribUnitCost capacity ∧
      cost + result.potential ≤ leftRep.potential + rightRep.potential + 448 := by
  cases side with
  | false =>
      cases rightRep with
      | minimum mapped stack =>
          have card := mapped.card_le_height
          obtain ⟨next, _, path, amortized⟩ := stack.exists_push actualLeft (by simp only [BST.height] at fits; omega)
          let result := RibRepresentation.minimum (.right leftRep mapped) next
          refine ⟨_, result, 64 * Digits.pushCost 0 stack.digits, path, ?_, ?_⟩
          · apply push_le_unit_of_height
            rw [stack.value_eq_card]
            simp only [BST.height] at fits
            omega
          · simp only [result, potential, RibSpineMap.ribPotential,
              FoldedMinimumStack.potential] at amortized ⊢
            omega
  | true =>
      cases leftRep with
      | maximum mapped stack =>
          have card := mapped.card_le_height
          obtain ⟨next, _, path, amortized⟩ := stack.exists_push actualRight (by simp only [BST.height] at fits; omega)
          let result := RibRepresentation.maximum (.left mapped rightRep) next
          refine ⟨_, result, 64 * Digits.pushCost 0 stack.digits, path, ?_, ?_⟩
          · apply push_le_unit_of_height
            rw [stack.value_eq_card]
            simp only [BST.height] at fits
            omega
          · simp only [result, potential, RibSpineMap.ribPotential,
              FoldedMaximumStack.potential] at amortized ⊢
            omega

private theorem empty_interval_of_height {boundary : ℕ} (tree : BST boundary boundary) : tree = .empty boundary := by
  cases tree with
  | empty => rfl
  | node left right => have lo := left.lower_le_upper; have hi := right.lower_le_upper; omega

/-- Reorienting a hanging subtree requires only its two root stack operations. -/
theorem exists_reorient_of_height {capacity lower upper : ℕ} {side : Bool} {before actual : BST lower upper}
    (targetSide : Bool) (representation : RibRepresentation capacity side before actual) (fits : before.height ≤ capacity) :
    ∃ (after : BST lower upper) (result : RibRepresentation capacity targetSide before after) (cost : ℕ),
      HasSupportedPath actual after cost cost ∧ cost ≤ 2 * ribUnitCost capacity ∧
      cost + result.potential ≤ representation.potential + 896 := by
  cases before with
  | empty =>
      let result := empty capacity targetSide lower
      have credit := result.potential_le_size
      refine ⟨.empty lower, result, 0, ?_, by omega, ?_⟩
      · rw [empty_interval_of_height actual]
        exact .refl _
      · simp only [BST.size] at credit
        omega
  | node left right =>
      obtain ⟨actualLeft, actualRight, leftRep, rightRep, c₁, p₁, b₁, a₁⟩ := representation.exists_split_node
      obtain ⟨after, result, c₂, p₂, b₂, a₂⟩ := exists_join_of_height targetSide leftRep rightRep fits
      exact ⟨after, result, c₁ + c₂, p₁.trans p₂, by omega, by omega⟩

/-- The middle hanging subtree changes spine orientation under a rotation;
its two root operations account for that change explicitly. -/
theorem exists_rootRotation_of_height {capacity lower upper : ℕ} {side : Bool} {before after actual : BST lower upper}
    (rotation : BST.RootRotation before after) (representation : RibRepresentation capacity side before actual)
    (fits : before.height + 1 ≤ capacity) :
    ∃ (resultTree : BST lower upper) (result : RibRepresentation capacity side after resultTree) (cost : ℕ),
      HasSupportedPath actual resultTree cost cost ∧ cost ≤ 6 * ribUnitCost capacity + 6 ∧
      cost + result.potential ≤ representation.potential + 2694 := by
  cases rotation with
  | left a b c =>
      obtain ⟨actualA, actualBC, repA, repBC, c₁, p₁, b₁, a₁⟩ := representation.exists_split_node
      obtain ⟨actualB, actualC, repB, repC, c₂, p₂, b₂, a₂⟩ := repBC.exists_split_node
      obtain ⟨changedB, changedRepB, cM, pM, bM, aM⟩ := repB.exists_reorient_of_height false
        (by simp only [BST.height] at fits; omega)
      obtain ⟨actualAB, repAB, c₃, p₃, b₃, a₃⟩ := exists_join_of_height true repA changedRepB
        (by simp only [BST.height] at fits ⊢; omega)
      obtain ⟨resultTree, result, c₄, p₄, b₄, a₄⟩ := exists_join_of_height side repAB repC
        (by simp only [BST.height] at fits ⊢; omega)
      refine ⟨resultTree, result, c₁ + c₂ + cM + c₃ + c₄ + 6, ?_, by omega, by omega⟩
      exact (((((p₁.trans (p₂.rightContext actualA)).trans
        ((pM.leftContext actualC).rightContext actualA)).trans
        (HasSupportedPath.rootLeft actualA changedB actualC)).trans
        (p₃.leftContext actualC)).trans p₄).mono (by omega) (by omega)
  | right a b c =>
      obtain ⟨actualAB, actualC, repAB, repC, c₁, p₁, b₁, a₁⟩ := representation.exists_split_node
      obtain ⟨actualA, actualB, repA, repB, c₂, p₂, b₂, a₂⟩ := repAB.exists_split_node
      obtain ⟨changedB, changedRepB, cM, pM, bM, aM⟩ := repB.exists_reorient_of_height true
        (by simp only [BST.height] at fits; omega)
      obtain ⟨actualBC, repBC, c₃, p₃, b₃, a₃⟩ := exists_join_of_height false changedRepB repC
        (by simp only [BST.height] at fits ⊢; omega)
      obtain ⟨resultTree, result, c₄, p₄, b₄, a₄⟩ := exists_join_of_height side repA repBC
        (by simp only [BST.height] at fits ⊢; omega)
      refine ⟨resultTree, result, c₁ + c₂ + cM + c₃ + c₄ + 6, ?_, by omega, by omega⟩
      exact (((((p₁.trans (p₂.leftContext actualC)).trans
        ((pM.rightContext actualA).leftContext actualC)).trans
        (HasSupportedPath.rootRight actualA changedB actualC)).trans
        (p₃.rightContext actualA)).trans p₄).mono (by omega) (by omega)

theorem exists_rotation_of_height {capacity lower upper depth : ℕ} {side : Bool} {before after actual : BST lower upper}
    (rotation : BST.RotationAt depth before after) (representation : RibRepresentation capacity side before actual)
    (fits : before.height + 1 ≤ capacity) :
    ∃ (resultTree : BST lower upper) (result : RibRepresentation capacity side after resultTree) (cost : ℕ),
      HasSupportedPath actual resultTree cost cost ∧
      cost ≤ (6 * ribUnitCost capacity + 6) * (depth + 1) ∧
      cost + result.potential ≤ representation.potential + 2694 * (depth + 1) := by
  induction rotation generalizing side with
  | root rotation => simpa using representation.exists_rootRotation_of_height rotation fits
  | leftContext rotation right ih =>
      obtain ⟨actualLeft, actualRight, leftRep, rightRep, c₁, p₁, b₁, a₁⟩ := representation.exists_split_node
      obtain ⟨changed, changedRep, c₂, p₂, b₂, a₂⟩ := ih leftRep (by simp only [BST.height] at fits; omega)
      obtain ⟨resultTree, result, c₃, p₃, b₃, a₃⟩ := exists_join_of_height side changedRep rightRep
        (by have rotated := rotation.height_le_add_one; simp only [BST.height] at fits ⊢; omega)
      refine ⟨resultTree, result, c₁ + c₂ + c₃ + 1, ?_, ?_, by omega⟩
      · exact ((p₁.trans (p₂.leftContext actualRight)).trans p₃).mono (by omega) (by omega)
      · nlinarith
  | rightContext left rotation ih =>
      obtain ⟨actualLeft, actualRight, leftRep, rightRep, c₁, p₁, b₁, a₁⟩ := representation.exists_split_node
      obtain ⟨changed, changedRep, c₂, p₂, b₂, a₂⟩ := ih rightRep (by simp only [BST.height] at fits; omega)
      obtain ⟨resultTree, result, c₃, p₃, b₃, a₃⟩ := exists_join_of_height side leftRep changedRep
        (by have rotated := rotation.height_le_add_one; simp only [BST.height] at fits ⊢; omega)
      refine ⟨resultTree, result, c₁ + c₂ + c₃ + 1, ?_, ?_, by omega⟩
      · exact ((p₁.trans (p₂.rightContext actualLeft)).trans p₃).mono (by omega) (by omega)
      · nlinarith

end RibRepresentation

end Splay.Accounting.OfflineConnectedSupport
