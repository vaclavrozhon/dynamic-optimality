import Splay.Accounting.OfflineRibSpineFamily

namespace Splay.Accounting.OfflineConnectedSupport

open Splay.Tree OfflineNormalForm OfflineNormalForm.RibStack

/-- Alternating spine replacements with the actual folded stack at each spine. -/
inductive RibRepresentation (capacity : ℕ) : Bool → {lower upper : ℕ} → BST lower upper → BST lower upper → Type
  | minimum {lower upper : ℕ} {before : BST lower upper} {frontier : SupportFrontier lower upper}
      (payloads : RibSpineMap (@RibRepresentation capacity) false before frontier)
      (stack : FoldedMinimumStack capacity frontier) :
      RibRepresentation capacity false before stack.tree
  | maximum {lower upper : ℕ} {before : BST lower upper} {frontier : SupportFrontier lower upper}
      (payloads : RibSpineMap (@RibRepresentation capacity) true before frontier)
      (stack : FoldedMaximumStack capacity frontier) :
      RibRepresentation capacity true before stack.tree

namespace RibRepresentation

theorem exists_representation {lower upper : ℕ} (capacity : ℕ) (side : Bool) (before : BST lower upper)
    (fits : before.size ≤ capacity) :
    ∃ after : BST lower upper, Nonempty (RibRepresentation capacity side before after) := by
  generalize sizeEq : before.size = count
  induction count using Nat.strong_induction_on generalizing lower upper side with
  | h count ih =>
      cases side with
      | false =>
          obtain ⟨frontier, ⟨mapped⟩⟩ := RibSpineMap.exists_map (Relation := @RibRepresentation capacity)
            false before (limit := count) (by omega) (fun child smaller => ih child.size smaller true child (by omega) rfl)
          obtain ⟨stack⟩ := FoldedMinimumStack.exists_initial capacity frontier (mapped.card_le_size.trans fits)
          exact ⟨stack.tree, ⟨.minimum mapped stack⟩⟩
      | true =>
          obtain ⟨frontier, ⟨mapped⟩⟩ := RibSpineMap.exists_map (Relation := @RibRepresentation capacity)
            true before (limit := count) (by omega) (fun child smaller => ih child.size smaller false child (by omega) rfl)
          obtain ⟨stack⟩ := FoldedMaximumStack.exists_initial capacity frontier (mapped.card_le_size.trans fits)
          exact ⟨stack.tree, ⟨.maximum mapped stack⟩⟩

/-- The extreme payload identities prevent spine bounds from accumulating
through the recursive substitutions. Every proper rib has slack nineteen. -/
theorem geometry {capacity lower upper : ℕ} {side : Bool} {before after : BST lower upper}
    (representation : RibRepresentation capacity side before after) :
    HasBoundedMinorRibs after 19 ∧
      leftBoundaryDepth after ≤ (if side then 6 else 12) ∧
      rightBoundaryDepth after ≤ (if side then 12 else 6) := by
  generalize sizeEq : before.size = count
  induction count using Nat.strong_induction_on generalizing lower upper side with
  | h count ih =>
      cases representation with
      | minimum mapped stack =>
            have payloads := mapped.transfer (limit := count) (height := before.height)
              (property := fun tree => HasBoundedMinorRibs tree 19 ∧ leftBoundaryDepth tree ≤ 6 ∧ rightBoundaryDepth tree ≤ 12)
              (by omega) le_rfl (fun boundary => ⟨trivial, by simp [leftBoundaryDepth], by simp [rightBoundaryDepth]⟩)
              (fun child smaller _ => by simpa using ih _ smaller child rfl)
            have ribs := stack.ribs (boundary := 12)
              (payloads.imp (fun tree geometry => ⟨by omega, geometry.2.2⟩))
              (payloads.imp (fun tree geometry => geometry.1)) (by decide)
            have left := SupportFrontier.firstLeftBoundary_le (payloads.imp (fun tree geometry => geometry.2.1))
            have right := mapped.outer_empty
            simp only [Bool.false_eq_true, if_false] at right
            have bounds := stack.boundaries
            exact ⟨ribs, by simp only [Bool.false_eq_true, if_false]; omega,
              by simp only [Bool.false_eq_true, if_false]; omega⟩
      | maximum mapped stack =>
            have payloads := mapped.transfer (limit := count) (height := before.height)
              (property := fun tree => HasBoundedMinorRibs tree 19 ∧ leftBoundaryDepth tree ≤ 12 ∧ rightBoundaryDepth tree ≤ 6)
              (by omega) le_rfl (fun boundary => ⟨trivial, by simp [leftBoundaryDepth], by simp [rightBoundaryDepth]⟩)
              (fun child smaller _ => by simpa using ih _ smaller child rfl)
            have ribs := stack.ribs (boundary := 12)
              (payloads.imp (fun tree geometry => ⟨geometry.2.1, by omega⟩))
              (payloads.imp (fun tree geometry => geometry.1)) (by decide)
            have left := mapped.outer_empty
            simp only [if_true] at left
            have right := SupportFrontier.lastRightBoundary_le (payloads.imp (fun tree geometry => geometry.2.2))
            have bounds := stack.boundaries
            exact ⟨ribs, by simp only [if_true]; omega, by simp only [if_true]; omega⟩

end RibRepresentation

end Splay.Accounting.OfflineConnectedSupport
