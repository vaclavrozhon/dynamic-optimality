import Greedy.ClosedAccess

/-! Access links preserve the slot and ancestry of every frozen fragment. -/

namespace Greedy.ClosedFamilies

open Splay.Rank GreedyMerge.OrderedBlocks GreedyMerge.Primitives
open GreedyMerge.ActualLinks GreedyMerge.HeapAllocation

theorem linkState_descendant {n : ℕ} (states : HeapSides n) (source winner loser : External n)
    (sourceSide targetSide : Bool) (entry : Entry) (owner : External n) (side : Bool)
    (block : Frozen) (member : block ∈
      (linkState states source winner loser sourceSide targetSide entry owner side).shrinking) :
    ∃ old, old ∈ (states owner side).shrinking ∧ Descends block old := by
  unfold linkState at member
  split_ifs at member
  · exact ⟨block, member, descends_refl _⟩
  · obtain ⟨old, oldMem, rfl⟩ := List.mem_map.mp member
    exact ⟨old, oldMem, erase_descends old loser.val⟩
  · exact ⟨block, member, descends_refl _⟩

theorem runLinks_descendant {n : ℕ} (source : External n)
    (sourceSide : External n × External n → Bool) (reader : ℕ → States n → ℕ → ℤ)
    (clock : ℕ) (states : HeapSides n) (events : List (External n × External n))
    (owner : External n) (side : Bool) (block : Frozen)
    (member : block ∈ (runLinks source sourceSide reader clock states events owner side).shrinking) :
    ∃ old, old ∈ (states owner side).shrinking ∧ Descends block old := by
  induction events generalizing clock states with
  | nil => exact ⟨block, member, descends_refl _⟩
  | cons event rest ih =>
      obtain ⟨middle, middleMem, desc⟩ := ih (clock+1) _ member
      obtain ⟨old, oldMem, earlier⟩ := linkState_descendant states source event.1 event.2
        (sourceSide event) (targetSide event) (arrivalEntry (reader clock states) event.1 event.2 clock)
        owner side middle middleMem
      exact ⟨old, oldMem, descends_trans desc earlier⟩

end Greedy.ClosedFamilies
