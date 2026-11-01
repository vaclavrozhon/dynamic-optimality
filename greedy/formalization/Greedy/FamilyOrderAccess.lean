import Greedy.FamilyOrder
import ActualLinkRuns

/-! Access links only delete frozen memberships; their new entries grow. -/

namespace Greedy.FamilyOrder

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.HeapAllocation GreedyMerge.ActualLinks

theorem linkState_ordered {n : ℕ} (states : HeapSides n) (source winner loser : External n)
    (sourceSide targetSide : Bool) (entry : Entry) (ordered : HeapOrdered states) :
    HeapOrdered (linkState states source winner loser sourceSide targetSide entry) := by
  have erased := erase_ordered (fun _ => loser.val) (table states) ordered
  apply ordered.local_steps
  · intro slot
    dsimp only [table, linkState]
    split_ifs
    · exact ordered.localOrder slot
    · exact erased.localOrder slot
    · exact ordered.localOrder slot
  · intro slot block member
    dsimp only [table, linkState] at member
    split_ifs at member
    · exact ⟨block, member, descends_refl _⟩
    · obtain ⟨old, oldMem, rfl⟩ := List.mem_map.mp member
      exact ⟨old, oldMem, erase_descends old loser.val⟩
    · exact ⟨block, member, descends_refl _⟩

theorem runLinks_ordered {n : ℕ} (source : External n)
    (sourceSide : External n × External n → Bool) (reader : ℕ → States n → ℕ → ℤ)
    (clock : ℕ) (states : HeapSides n) (events : List (External n × External n)) (ordered : HeapOrdered states) :
    HeapOrdered (runLinks source sourceSide reader clock states events) := by
  induction events generalizing clock states with
  | nil => exact ordered
  | cons event rest ih =>
      exact ih (clock+1) _ (linkState_ordered states source event.1 event.2 (sourceSide event) (targetSide event)
        (arrivalEntry (reader clock states) event.1 event.2 clock) ordered)

end Greedy.FamilyOrder
