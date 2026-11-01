import Greedy.FamilyConversions
import ActualLinkRuns
import FrozenFamilyHistory

/-! Appending memberships changes no family name; source deletion inherits it. -/

namespace Greedy.FamilyNames

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.ActualLinks GreedyMerge.HeapAllocation

theorem Inventory.inherited {slots next : ℕ} {before after : Fin slots → SideState}
    (inventory : Inventory before next)
    (growers : ∀ slot grower, (after slot).grower = some grower →
      ∃ old, (before slot).grower = some old ∧ grower.family = old.family)
    (descendants : ∀ slot block, block ∈ (after slot).shrinking →
      ∃ oldSlot old, old ∈ (before oldSlot).shrinking ∧ Descends block old) : Inventory after next := by
  refine ⟨?_, ?_, ?_⟩
  · intro slot family member
    rcases List.mem_append.mp member with frozen | growing
    · obtain ⟨block, blockMem, rfl⟩ := List.mem_map.mp frozen
      obtain ⟨oldSlot, old, oldMem, descendant⟩ := descendants slot block blockMem
      rw [descendant.1]
      exact inventory.below oldSlot old.family (frozen_mem _ _ oldMem)
    · obtain ⟨grower, growerMem, rfl⟩ := List.mem_map.mp growing
      obtain ⟨old, present, same⟩ := growers slot grower (by simpa using growerMem)
      rw [same]
      exact inventory.below slot old.family (grower_mem _ _ present)
  · intro first second left right firstPresent secondPresent same
    obtain ⟨oldLeft, leftPresent, leftFamily⟩ := growers first left firstPresent
    obtain ⟨oldRight, rightPresent, rightFamily⟩ := growers second right secondPresent
    exact inventory.growing first second oldLeft oldRight leftPresent rightPresent (leftFamily.symm.trans (same.trans rightFamily))
  · intro first second block grower member present same
    obtain ⟨oldSlot, old, oldMem, descendant⟩ := descendants first block member
    obtain ⟨oldGrower, oldPresent, growerFamily⟩ := growers second grower present
    exact inventory.sealed oldSlot second old oldGrower oldMem oldPresent (descendant.1.symm.trans (same.trans growerFamily))

theorem linkState_inventory {n next : ℕ} (states : HeapSides n) (source winner loser : External n)
    (sourceSide targetSide : Bool) (entry : Entry) (inventory : HeapFamilyInventory states next) :
    HeapFamilyInventory (linkState states source winner loser sourceSide targetSide entry) next := by
  apply inventory.inherited
  · intro slot grower present
    change (linkState states source winner loser sourceSide targetSide entry
      ((encode n).symm slot).1 ((encode n).symm slot).2).grower = some grower at present
    unfold linkState at present
    split_ifs at present
    · cases old : (table states slot).grower with
      | none => simp [appendGrower, show (states ((encode n).symm slot).1 ((encode n).symm slot).2).grower = none from old] at present
      | some previous =>
          have same : grow entry previous = grower := by
            simpa only [appendGrower, show (states ((encode n).symm slot).1 ((encode n).symm slot).2).grower = some previous from old,
              Option.map_some, Option.some.injEq] using present
          exact ⟨previous, rfl, by rw [← same]; rfl⟩
    · exact ⟨grower, present, rfl⟩
    · exact ⟨grower, present, rfl⟩
  · intro slot block member
    change block ∈ (linkState states source winner loser sourceSide targetSide entry
      ((encode n).symm slot).1 ((encode n).symm slot).2).shrinking at member
    unfold linkState at member
    split_ifs at member
    · exact ⟨slot, block, member, descends_refl _⟩
    · obtain ⟨old, oldMem, rfl⟩ := List.mem_map.mp member
      exact ⟨slot, old, oldMem, erase_descends old loser.val⟩
    · exact ⟨slot, block, member, descends_refl _⟩

theorem runLinks_inventory {n next : ℕ} (source : External n)
    (sourceSide : External n × External n → Bool) (reader : ℕ → States n → ℕ → ℤ)
    (clock : ℕ) (states : HeapSides n) (events : List (External n × External n))
    (inventory : HeapFamilyInventory states next) :
    HeapFamilyInventory (runLinks source sourceSide reader clock states events) next := by
  induction events generalizing clock states with
  | nil => exact inventory
  | cons event rest ih =>
      exact ih (clock+1) _ (linkState_inventory states source event.1 event.2 (sourceSide event) (targetSide event)
        (arrivalEntry (reader clock states) event.1 event.2 clock) inventory)

end Greedy.FamilyNames
