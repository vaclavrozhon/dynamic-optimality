import Splay.Accounting.OfflineRibRepresentation

namespace Splay.Accounting.OfflineConnectedSupport

open Splay.Tree OfflineNormalForm OfflineNormalForm.RibStack

theorem RibSpineMap.card_le_height {Relation : Bool → {lo hi : ℕ} → BST lo hi → BST lo hi → Type}
    {lower upper : ℕ} {side : Bool} {before : BST lower upper} {frontier : SupportFrontier lower upper}
    (mapped : RibSpineMap @Relation side before frontier) : frontier.card ≤ before.height := by
  induction mapped with
  | empty => rfl
  | right payload rest ih => simp only [SupportFrontier.card, BST.height]; omega
  | left rest payload ih => simp only [SupportFrontier.card_append, SupportFrontier.card, BST.height]; omega

private theorem height_step {height count capacity actual : ℕ}
    (spine : count ≤ height) (fits : count ≤ capacity)
    (bound : actual ≤ 5 * Nat.clog 2 (count + 1) + (height - 1) * (5 * Nat.clog 2 (capacity + 1))) :
    actual ≤ height * (5 * Nat.clog 2 (capacity + 1)) := by
  by_cases positive : 0 < height
  · have previous : height - 1 + 1 = height := by omega
    have levels := Nat.clog_mono_right 2 (Nat.add_le_add_right fits 1)
    nlinarith
  · have hZero : height = 0 := by omega
    have cZero : count = 0 := by omega
    simpa [hZero, cZero] using bound

/-- Replacing ribs multiplies height by at most one logarithmic factor.
The earlier quadratic-logarithmic normalizer therefore remains polylogarithmic. -/
theorem RibRepresentation.height_le {capacity lower upper : ℕ} {side : Bool} {before after : BST lower upper}
    (representation : RibRepresentation capacity side before after) (fits : before.size ≤ capacity) :
    after.height ≤ before.height * (5 * Nat.clog 2 (capacity + 1)) := by
  generalize sizeEq : before.size = count
  induction count using Nat.strong_induction_on generalizing lower upper side with
  | h count ih =>
      cases representation with
      | minimum mapped stack =>
          have payloads := mapped.transfer (limit := count) (height := before.height)
            (property := fun tree => tree.height ≤ (before.height - 1) * (5 * Nat.clog 2 (capacity + 1)))
            (by omega) le_rfl (fun boundary => by change 0 ≤ _; omega)
            (fun child smaller smallerHeight => by
              have bounded := ih _ smaller child (by omega) rfl
              exact bounded.trans (Nat.mul_le_mul_right _ (by omega)))
          exact height_step mapped.card_le_height (mapped.card_le_size.trans fits) (stack.height_le payloads)
      | maximum mapped stack =>
          have payloads := mapped.transfer (limit := count) (height := before.height)
            (property := fun tree => tree.height ≤ (before.height - 1) * (5 * Nat.clog 2 (capacity + 1)))
            (by omega) le_rfl (fun boundary => by change 0 ≤ _; omega)
            (fun child smaller smallerHeight => by
              have bounded := ih _ smaller child (by omega) rfl
              exact bounded.trans (Nat.mul_le_mul_right _ (by omega)))
          exact height_step mapped.card_le_height (mapped.card_le_size.trans fits) (stack.height_le payloads)

end Splay.Accounting.OfflineConnectedSupport
