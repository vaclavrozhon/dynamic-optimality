import Greedy.InstancePreparation

/-! Whole-fragment movement preserves every old instance's inherited property. -/

namespace Greedy.ClosedInstances

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.HeapAllocation

theorem junction_closed {n id : ℕ} {property : Frozen → Prop}
    (oldOwner newOwner : External n) (lo hi start : ℕ) (states : HeapSides n)
    (closed : HeapClosed id property states) (hereditary : ClosedFamilies.Hereditary property) (past : id < start) :
    HeapClosed id property (allocateJunction oldOwner newOwner lo hi start states).states := by
  have names (side : Bool) : id < (allocateJunction oldOwner newOwner lo hi start states).names side := by
    cases side
    · exact past
    · rw [allocateJunction_second_name]; omega
  apply heap_old_descendants closed hereditary (GrowthJournal.junction_grower oldOwner newOwner lo hi start states)
  intro owner side block member same
  rw [allocateJunction_eq] at member
  unfold moveJunction at member
  split_ifs at member with old new
  · obtain ⟨original, originalMem, sameId, descendant⟩ := separateOuter_old_descendant side (junctionCut side lo hi) _
      (states oldOwner side) block (List.mem_append_left _ member) (same.symm ▸ names side)
    exact ⟨oldOwner, side, original, originalMem, sameId.symm.trans same, descendant⟩
  · change block ∈ (states newOwner side).shrinking ++ _ at member
    rcases List.mem_append.mp member with own | moved
    · exact ⟨newOwner, side, block, own, same, descends_refl _⟩
    · obtain ⟨original, originalMem, sameId, descendant⟩ := separateOuter_old_descendant side (junctionCut side lo hi) _
        (states oldOwner side) block (List.mem_append_right _ moved) (same.symm ▸ names side)
      exact ⟨oldOwner, side, original, originalMem, sameId.symm.trans same, descendant⟩
  · exact ⟨owner, side, block, member, same, descends_refl _⟩

end Greedy.ClosedInstances
