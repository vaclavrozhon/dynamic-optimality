import Splay.Accounting.OfflineRibRepresentation

namespace Splay.Accounting.OfflineConnectedSupport

open Splay.Tree OfflineNormalForm OfflineNormalForm.RibStack

mutual

def RibRepresentation.potential {capacity lower upper : ℕ} {side : Bool} {before after : BST lower upper}
    (representation : RibRepresentation capacity side before after) : ℕ :=
  match representation with
  | .minimum mapped stack => stack.potential + mapped.ribPotential
  | .maximum mapped stack => stack.potential + mapped.ribPotential

def RibSpineMap.ribPotential {capacity lower upper : ℕ} {side : Bool}
    {before : BST lower upper} {frontier : SupportFrontier lower upper}
    (mapped : RibSpineMap (@RibRepresentation capacity) side before frontier) : ℕ :=
  match mapped with
  | .empty _ _ => 0
  | .right payload rest => payload.potential + rest.ribPotential
  | .left rest payload => rest.ribPotential + payload.potential

end

theorem RibSpineMap.potential_le_of {capacity lower upper limit : ℕ} {side : Bool}
    {before : BST lower upper} {frontier : SupportFrontier lower upper}
    (mapped : RibSpineMap (@RibRepresentation capacity) side before frontier) (fits : before.size ≤ limit)
    (bound : ∀ {lo hi : ℕ} {direction : Bool} {source target : BST lo hi},
      (representation : RibRepresentation capacity direction source target) → source.size < limit →
      representation.potential ≤ 256 * source.size) :
    mapped.ribPotential + 256 * frontier.card ≤ 256 * before.size := by
  induction mapped with
  | empty => simp [RibSpineMap.ribPotential, SupportFrontier.card, BST.size]
  | right payload rest ih =>
      simp only [BST.size] at fits
      have side := bound payload (by omega)
      have tail := ih (by omega)
      simp only [RibSpineMap.ribPotential, SupportFrontier.card, BST.size]
      omega
  | left rest payload ih =>
      simp only [BST.size] at fits
      have initial := ih (by omega)
      have side := bound payload (by omega)
      simp only [RibSpineMap.ribPotential, SupportFrontier.card_append, SupportFrontier.card, BST.size]
      omega

theorem RibRepresentation.potential_le_size {capacity lower upper : ℕ} {side : Bool} {before after : BST lower upper}
    (representation : RibRepresentation capacity side before after) : representation.potential ≤ 256 * before.size := by
  generalize sizeEq : before.size = count
  induction count using Nat.strong_induction_on generalizing lower upper side with
  | h count ih =>
      cases representation with
      | minimum mapped stack =>
          have all := mapped.potential_le_of (limit := count) (by omega) (fun child smaller => ih _ smaller child rfl)
          have current := stack.potential_le_card
          simp only [RibRepresentation.potential]
          omega
      | maximum mapped stack =>
          have all := mapped.potential_le_of (limit := count) (by omega) (fun child smaller => ih _ smaller child rfl)
          have current := stack.potential_le_card
          simp only [RibRepresentation.potential]
          omega

end Splay.Accounting.OfflineConnectedSupport
