import DynamicOptimality.MultiFinger.PhysicalEndpointDemote

/-! Every source endpoint edit has its actual persistent deque kernel.
The result is independent of the source depth, the sizes of the untouched
hanging subtrees, and the shape of the global top-splay skeleton. -/

namespace DynamicOptimality.MultiFinger.Hand

open ChaCha.MTR
open Pointer (MarkedTree)
open PhysicalHand

variable {α : Type*}

theorem EndpointEdit.implemented_both {before after : Hand α}
    (edit : EndpointEdit before after) : Implemented before after ∧ Implemented after before := by
  induction edit with
  | stump left right key => exact ⟨stump_promote left right key,stump_demote left right key⟩
  | outer_left frames left right key parent sibling =>
      exact ⟨outer_left_promote frames left right key parent sibling,
        outer_left_demote frames left right key parent sibling⟩
  | outer_right frames left right key parent sibling =>
      exact ⟨outer_right_promote frames left right key parent sibling,
        outer_right_demote frames left right key parent sibling⟩
  | inner_left frames left right key parent sibling =>
      exact ⟨inner_left_promote frames left right key parent sibling,
        inner_left_demote frames left right key parent sibling⟩
  | inner_right frames left right key parent sibling =>
      exact ⟨inner_right_promote frames left right key parent sibling,
        inner_right_demote frames left right key parent sibling⟩
  | reverse _ ih => exact ⟨ih.2,ih.1⟩
  | left _ frames key right ih => exact ⟨ih.1.left frames key right,ih.2.left frames key right⟩
  | right _ frames left key ih => exact ⟨ih.1.right frames left key,ih.2.right frames left key⟩

/-- One source edit changes one region with at most three exposed markers.
Its raw kernel and the persistent queue potential obey the uniform
amortized allowance 14. The global top-tree cost is supplied separately
by `RegionStep.realize`. -/
theorem EndpointEdit.realize {before after : Hand α} (edit : EndpointEdit before after)
    {physical : MarkedTree α} {credit : Nat} (valid : Realizes before physical credit) :
    ∃ next : MarkedTree α, ∃ nextCredit count : Nat,
      Realizes after next nextCredit ∧ RegionStep physical next count ∧
      count+nextCredit ≤ credit+14 :=
  edit.implemented_both.1 physical credit valid

end DynamicOptimality.MultiFinger.Hand
