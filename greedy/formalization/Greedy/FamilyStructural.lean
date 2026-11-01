import Greedy.FamilyConversions
import Greedy.GrowthStructural

/-! Frozen descendants preserve family-name bounds and grower exclusivity. -/

namespace Greedy.FamilyNames

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.HeapAllocation

theorem Inventory.descendants {slots next : ℕ} {before after : Fin slots → SideState}
    (inventory : Inventory before next)
    (growers : ∀ slot, (after slot).grower = (before slot).grower)
    (descendants : ∀ slot block, block ∈ (after slot).shrinking →
      ∃ oldSlot old, old ∈ (before oldSlot).shrinking ∧ Descends block old) : Inventory after next := by
  refine ⟨?_, ?_, ?_⟩
  · intro slot family member
    rcases List.mem_append.mp member with frozen | growing
    · obtain ⟨block, blockMem, rfl⟩ := List.mem_map.mp frozen
      obtain ⟨oldSlot, old, oldMem, descendant⟩ := descendants slot block blockMem
      rw [descendant.1]
      exact inventory.below oldSlot old.family (frozen_mem _ _ oldMem)
    · exact inventory.below slot family (List.mem_append_right _ (by simpa only [growers] using growing))
  · intro first second left right firstPresent secondPresent same
    rw [growers] at firstPresent secondPresent
    exact inventory.growing first second left right firstPresent secondPresent same
  · intro first second block grower member present same
    obtain ⟨oldSlot, old, oldMem, descendant⟩ := descendants first block member
    rw [growers] at present
    exact inventory.sealed oldSlot second old grower oldMem present (descendant.1.symm.trans same)

theorem heap_descendants {n next : ℕ} {before after : HeapSides n}
    (inventory : HeapFamilyInventory before next)
    (growers : ∀ owner side, (after owner side).grower = (before owner side).grower)
    (descendants : ∀ owner side block, block ∈ (after owner side).shrinking →
      ∃ oldOwner oldSide old, old ∈ (before oldOwner oldSide).shrinking ∧ Descends block old) :
    HeapFamilyInventory after next := by
  apply inventory.descendants (after := table after) (fun slot => growers _ _)
  intro slot block member
  obtain ⟨oldOwner, oldSide, old, oldMem, descendant⟩ := descendants _ _ block member
  exact ⟨encode n (oldOwner, oldSide), old, by simpa [table] using oldMem, descendant⟩

theorem allocateCuts_inventory {n : ℕ} (cuts : List (ℕ × ℕ)) (start : ℕ) (states : HeapSides n)
    (inventory : HeapFamilyInventory states start) :
    HeapFamilyInventory (allocateCuts cuts start states).states (allocateCuts cuts start states).next := by
  have changed := heap_descendants inventory (after := (allocateCuts cuts start states).states)
    (GrowthJournal.allocateCuts_grower cuts start states) ?_
  · exact changed.advance _ (allocateCuts_next cuts start states)
  intro owner side block member
  have exactState := congrArg Prod.fst (allocateCuts_eq cuts start states)
  dsimp only at exactState
  rw [← exactState] at member
  obtain ⟨old, oldMem, descendant⟩ := prepareCuts_descends (allocateCuts cuts start states).names cuts 0 states owner side block member
  exact ⟨owner, side, old, oldMem, descendant⟩

theorem rebase_inventory {n next : ℕ} (before after : BST 0 n) (states : HeapSides n)
    (inventory : HeapFamilyInventory states next) : HeapFamilyInventory (rebaseAll before after states) next := by
  apply heap_descendants inventory (after := rebaseAll before after states) (fun _ _ => rfl)
  intro owner side block member
  obtain ⟨old, oldMem, rfl⟩ := List.mem_map.mp member
  exact ⟨owner, side, old, oldMem, rfl, rfl, List.Sublist.refl _⟩

theorem junction_inventory {n : ℕ} (oldOwner newOwner : External n) (lo hi start : ℕ) (states : HeapSides n)
    (inventory : HeapFamilyInventory states start) :
    HeapFamilyInventory (allocateJunction oldOwner newOwner lo hi start states).states
      (allocateJunction oldOwner newOwner lo hi start states).next := by
  have changed := heap_descendants inventory (after := (allocateJunction oldOwner newOwner lo hi start states).states)
    (GrowthJournal.junction_grower oldOwner newOwner lo hi start states) ?_
  · exact changed.advance _ (allocateJunction_monotone oldOwner newOwner lo hi start states)
  intro owner side block member
  rw [allocateJunction_eq] at member
  unfold moveJunction at member
  split_ifs at member with old new
  · obtain ⟨original, originalMem, descendant⟩ := separateOuter_descends side (junctionCut side lo hi) _
      (states oldOwner side) block (List.mem_append_left _ member)
    exact ⟨oldOwner, side, original, originalMem, descendant⟩
  · change block ∈ (states newOwner side).shrinking ++ _ at member
    rcases List.mem_append.mp member with previous | moved
    · exact ⟨newOwner, side, block, previous, descends_refl _⟩
    · obtain ⟨original, originalMem, descendant⟩ := separateOuter_descends side (junctionCut side lo hi) _
        (states oldOwner side) block (List.mem_append_right _ moved)
      exact ⟨oldOwner, side, original, originalMem, descendant⟩
  · exact ⟨owner, side, block, member, descends_refl _⟩

end Greedy.FamilyNames
