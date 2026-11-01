import Greedy.FamilyOrder
import FreshComparatorExecution

/-!
Fragments can move or lose members without changing their identities.
Global live-identity uniqueness prevents a movement from duplicating an
old fragment, so disjoint historical intervals remain disjoint.
-/

namespace Greedy.FamilyOrder

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.HeapAllocation
open GreedyMerge.HistoryProcess

theorem Ordered.transport {slots next : ℕ} {before after : Fin slots → SideState}
    (ordered : Ordered before) (inventory : GreedyMerge.FreshIds.Inventory after next)
    (descendants : ∀ slot block, block ∈ (after slot).shrinking →
      ∃ oldSlot old, old ∈ (before oldSlot).shrinking ∧ Descends block old ∧ block.id = old.id) :
    Ordered after := by
  have separated (first second : Fin slots) (left right : Frozen)
      (leftMem : left ∈ (after first).shrinking) (rightMem : right ∈ (after second).shrinking)
      (different : left.id ≠ right.id) : Separated left right := by
    obtain ⟨oldFirst, oldLeft, oldLeftMem, leftDescends, leftId⟩ := descendants first left leftMem
    obtain ⟨oldSecond, oldRight, oldRightMem, rightDescends, rightId⟩ := descendants second right rightMem
    apply separated_descendants leftDescends rightDescends
    by_cases same : oldFirst = oldSecond
    · subst oldSecond
      apply separated_of_members _ (ordered.localOrder oldFirst).1 oldLeft oldRight oldLeftMem oldRightMem
      intro equal
      exact different (leftId.trans ((congrArg Frozen.id equal).trans rightId.symm))
    · exact ordered.between oldFirst oldSecond same oldLeft oldLeftMem oldRight oldRightMem
  refine ⟨?_, ?_⟩
  · intro slot
    have unique := (List.nodup_append.mp (inventory.localUnique slot)).1
    refine ⟨(List.Nodup.of_map Frozen.id unique).pairwise_of_forall_ne ?_, ?_⟩
    · intro left leftMem right rightMem different
      exact separated slot slot left right leftMem rightMem
        (fun equal => different (List.inj_on_of_nodup_map unique leftMem rightMem equal))
    · intro block member
      obtain ⟨oldSlot, old, oldMem, descendant, _⟩ := descendants slot block member
      obtain ⟨orientation, history⟩ := (ordered.localOrder oldSlot).2 old oldMem
      exact ⟨orientation, descends_preserves_history_orientation descendant orientation history⟩
  · intro first second different left leftMem right rightMem
    apply separated first second left right leftMem rightMem
    intro equal
    exact different (inventory.locations first second left.id
      (List.mem_append_left _ (List.mem_map.mpr ⟨left, leftMem, rfl⟩))
      (List.mem_append_left _ (List.mem_map.mpr ⟨right, rightMem, equal.symm⟩)))

theorem heap_transport {n next : ℕ} {before after : HeapSides n}
    (ordered : HeapOrdered before) (inventory : HeapInventory after next)
    (descendants : ∀ owner side block, block ∈ (after owner side).shrinking →
      ∃ oldOwner oldSide old, old ∈ (before oldOwner oldSide).shrinking ∧ Descends block old ∧ block.id = old.id) :
    HeapOrdered after := by
  apply ordered.transport inventory
  intro slot block member
  obtain ⟨oldOwner, oldSide, old, oldMem, descendant, identity⟩ := descendants _ _ block member
  exact ⟨encode n (oldOwner, oldSide), old, by simpa [table] using oldMem, descendant, identity⟩

theorem rebase_ordered {n next : ℕ} (before after : BST 0 n) (states : HeapSides n)
    (ordered : HeapOrdered states) (inventory : HeapInventory states next) :
    HeapOrdered (rebaseAll before after states) := by
  apply heap_transport ordered (GreedyMerge.HeapAllocation.rebaseAll_inventory before after states next inventory)
  intro owner side block member
  obtain ⟨old, oldMem, rfl⟩ := List.mem_map.mp member
  exact ⟨owner, side, old, oldMem, ⟨rfl, rfl, List.Sublist.refl _⟩, rfl⟩

end Greedy.FamilyOrder
