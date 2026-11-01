import Greedy.FamilyOrderTransport

/-! Actual junction movement first splits, then transports whole fragments. -/

namespace Greedy.FamilyOrder

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.HeapAllocation
open GreedyMerge.HistoryProcess

theorem junction_ordered {n : ℕ} (oldOwner newOwner : External n) (different : oldOwner ≠ newOwner)
    (lo hi start : ℕ) (states : HeapSides n) (ordered : HeapOrdered states) (inventory : HeapInventory states start) :
    HeapOrdered (allocateJunction oldOwner newOwner lo hi start states).states := by
  let names := (allocateJunction oldOwner newOwner lo hi start states).names
  let cutStates : HeapSides n := fun owner side => if owner = oldOwner then
    cutState side (junctionCut side lo hi) (names side) (states owner side) else states owner side
  have cutOrder : HeapOrdered cutStates := by
    apply ordered.local_steps
    · intro slot
      dsimp only [table, cutStates]
      split_ifs
      · exact cutList_history_valid _ _ _ _ (ordered.localOrder slot)
      · exact ordered.localOrder slot
    · intro slot block member
      dsimp only [table, cutStates] at member
      split_ifs at member
      · exact cutList_descends _ _ _ _ block member
      · exact ⟨block, member, descends_refl _⟩
  apply heap_transport cutOrder (allocateJunction_inventory oldOwner newOwner different lo hi start states inventory)
  intro owner side block member
  rw [allocateJunction_eq] at member
  unfold moveJunction at member
  split_ifs at member with old new
  · refine ⟨oldOwner, side, block, ?_, descends_refl _, rfl⟩
    simp only [cutStates, ↓reduceIte]
    exact (List.mem_filter.mp member).1
  · change block ∈ (states newOwner side).shrinking ++ _ at member
    rcases List.mem_append.mp member with own | moved
    · refine ⟨newOwner, side, block, ?_, descends_refl _, rfl⟩
      simpa only [cutStates, if_neg different.symm] using own
    · refine ⟨oldOwner, side, block, ?_, descends_refl _, rfl⟩
      simp only [cutStates, ↓reduceIte]
      exact (List.mem_filter.mp moved).1
  · refine ⟨owner, side, block, ?_, descends_refl _, rfl⟩
    simpa only [cutStates, if_neg old] using member

end Greedy.FamilyOrder
