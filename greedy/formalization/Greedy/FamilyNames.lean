import FreshInventory
import HeapFreshAllocation

/-!
# Fresh family names and exclusive growing families

A growing family's name occurs in no frozen block and in no other
grower. Sealing that grower retires its exclusive growing status and
starts a fresh empty family. Instance names and family names are separate.
-/

namespace Greedy.FamilyNames

open GreedyMerge.OrderedBlocks GreedyMerge.Primitives
open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical

def names (state : SideState) : List ℕ :=
  state.shrinking.map Frozen.family ++ state.grower.toList.map Grower.family

structure Inventory {slots : ℕ} (states : Fin slots → SideState) (next : ℕ) : Prop where
  below : ∀ slot family, family ∈ names (states slot) → family < next
  growing : ∀ first second left right, (states first).grower = some left →
    (states second).grower = some right → left.family = right.family → first = second
  sealed : ∀ first second block grower, block ∈ (states first).shrinking →
    (states second).grower = some grower → block.family ≠ grower.family

theorem frozen_mem (state : SideState) (block : Frozen) (member : block ∈ state.shrinking) :
    block.family ∈ names state := List.mem_append_left _ (List.mem_map.mpr ⟨block, member, rfl⟩)

theorem grower_mem (state : SideState) (grower : Grower) (present : state.grower = some grower) :
    grower.family ∈ names state := by simp [names, present]

theorem Inventory.advance {slots next : ℕ} {states : Fin slots → SideState}
    (inventory : Inventory states next) (later : ℕ) (bound : next ≤ later) : Inventory states later :=
  ⟨fun slot family member => (inventory.below slot family member).trans_le bound, inventory.growing, inventory.sealed⟩

def sealedState (state : SideState) (grower : Grower) (owner fresh base : ℕ) : SideState :=
  ⟨state.shrinking ++ [freeze grower.id base grower], some (emptyGrower owner fresh fresh)⟩

theorem seal_names (state : SideState) (grower : Grower) (present : state.grower = some grower)
    (owner fresh base : ℕ) : names (sealedState state grower owner fresh base) = names state ++ [fresh] := by
  simp [names, sealedState, present, freeze, emptyGrower, List.append_assoc]

theorem seal_inventory {slots next : ℕ} (states : Fin slots → SideState) (selected : Fin slots)
    (grower : Grower) (present : (states selected).grower = some grower) (owner fresh base : ℕ)
    (inventory : Inventory states next) (newName : next ≤ fresh) :
    Inventory (Function.update states selected (sealedState (states selected) grower owner fresh base)) (fresh+1) := by
  have frozenBound (slot : Fin slots) (block : Frozen) (member : block ∈ (states slot).shrinking) : block.family < fresh :=
    (inventory.below slot block.family (frozen_mem _ _ member)).trans_le newName
  have growerBound (slot : Fin slots) (old : Grower) (someOld : (states slot).grower = some old) : old.family < fresh :=
    (inventory.below slot old.family (grower_mem _ _ someOld)).trans_le newName
  refine ⟨?_, ?_, ?_⟩
  · intro slot family member
    by_cases same : slot = selected
    · subst slot
      rw [Function.update_self, seal_names _ _ present] at member
      rcases List.mem_append.mp member with old | freshMem
      · exact (inventory.below selected family old).trans_le (by omega)
      · have equal := List.mem_singleton.mp freshMem
        omega
    · rw [Function.update_of_ne same] at member
      exact (inventory.below slot family member).trans_le (by omega)
  · intro first second left right firstPresent secondPresent equal
    by_cases firstEq : first = selected
    · subst first
      have leftEq : emptyGrower owner fresh fresh = left := by simpa [sealedState] using firstPresent
      by_cases secondEq : second = selected
      · exact secondEq.symm
      · rw [Function.update_of_ne secondEq] at secondPresent
        have rightBound := growerBound second right secondPresent
        rw [← leftEq] at equal
        change fresh = right.family at equal
        omega
    · rw [Function.update_of_ne firstEq] at firstPresent
      by_cases secondEq : second = selected
      · subst second
        have rightEq : emptyGrower owner fresh fresh = right := by simpa [sealedState] using secondPresent
        have leftBound := growerBound first left firstPresent
        rw [← rightEq] at equal
        change left.family = fresh at equal
        omega
      · rw [Function.update_of_ne secondEq] at secondPresent
        exact inventory.growing first second left right firstPresent secondPresent equal
  · intro first second block current member currentPresent equal
    by_cases secondEq : second = selected
    · subst second
      have currentEq : emptyGrower owner fresh fresh = current := by simpa [sealedState] using currentPresent
      rw [← currentEq] at equal
      change block.family = fresh at equal
      by_cases firstEq : first = selected
      · subst first
        rw [Function.update_self] at member
        change block ∈ (states selected).shrinking ++ [freeze grower.id base grower] at member
        rcases List.mem_append.mp member with old | born
        · have bound := frozenBound selected block old
          omega
        · have blockEq := List.mem_singleton.mp born
          rw [blockEq] at equal
          have bound := growerBound selected grower present
          change grower.family = fresh at equal
          omega
      · rw [Function.update_of_ne firstEq] at member
        have bound := frozenBound first block member
        omega
    · rw [Function.update_of_ne secondEq] at currentPresent
      by_cases firstEq : first = selected
      · subst first
        rw [Function.update_self] at member
        change block ∈ (states selected).shrinking ++ [freeze grower.id base grower] at member
        rcases List.mem_append.mp member with old | born
        · exact inventory.sealed selected second block current old currentPresent equal
        · have blockEq := List.mem_singleton.mp born
          rw [blockEq] at equal
          exact secondEq (inventory.growing selected second grower current present currentPresent equal).symm
      · rw [Function.update_of_ne firstEq] at member
        exact inventory.sealed first second block current member currentPresent equal

theorem convert_inventory {slots next : ℕ} (states : Fin slots → SideState) (selected : Fin slots)
    (owner fresh base : ℕ) (inventory : Inventory states next) (newName : next ≤ fresh) :
    Inventory (Function.update states selected (convert owner fresh fresh base (states selected))) (fresh+1) := by
  cases present : (states selected).grower with
  | none => simpa [convert, present] using inventory.advance (fresh+1) (by omega)
  | some grower =>
      by_cases empty : grower.members = []
      · simpa [convert, present, empty] using inventory.advance (fresh+1) (by omega)
      · simpa only [convert, present, empty, ↓reduceIte, sealedState] using
          seal_inventory states selected grower present owner fresh base inventory newName

end Greedy.FamilyNames
