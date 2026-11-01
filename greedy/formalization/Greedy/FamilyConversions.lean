import Greedy.FamilyNames

/-! Family-name freshness for simultaneous concrete grower conversions. -/

namespace Greedy.FamilyNames

open GreedyMerge.OrderedBlocks GreedyMerge.Primitives
open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical

def conversionPrefix {slots : ℕ} (owner base : Fin slots → ℕ) (selected : Fin slots → Bool)
    (start : ℕ) (states : Fin slots → SideState) (count : ℕ) : Fin slots → SideState :=
  fun slot => if slot.val < count ∧ selected slot then
    convert (owner slot) (start+slot.val) (start+slot.val) (base slot) (states slot) else states slot

theorem conversionPrefix_succ {slots : ℕ} (owner base : Fin slots → ℕ) (selected : Fin slots → Bool)
    (start : ℕ) (states : Fin slots → SideState) (count : ℕ) (inside : count < slots) :
    conversionPrefix owner base selected start states (count+1) =
      Function.update (conversionPrefix owner base selected start states count) ⟨count, inside⟩
        (if selected ⟨count, inside⟩ then convert (owner ⟨count, inside⟩) (start+count) (start+count)
          (base ⟨count, inside⟩) (states ⟨count, inside⟩) else states ⟨count, inside⟩) := by
  funext slot
  by_cases same : slot = ⟨count, inside⟩
  · subst slot
    simp [conversionPrefix]
  · rw [Function.update_of_ne same]
    have different : slot.val ≠ count := fun equal => same (Fin.ext equal)
    have bounded : slot.val < count+1 ↔ slot.val < count := by omega
    simp only [conversionPrefix, bounded]

theorem conversionPrefix_inventory {slots : ℕ} (owner base : Fin slots → ℕ) (selected : Fin slots → Bool)
    (start : ℕ) (states : Fin slots → SideState) (inventory : Inventory states start)
    (count : ℕ) (inside : count ≤ slots) : Inventory (conversionPrefix owner base selected start states count) (start+count) := by
  induction count with
  | zero =>
      have equal : conversionPrefix owner base selected start states 0 = states := by
        funext slot
        simp [conversionPrefix]
      rw [equal, Nat.add_zero]
      exact inventory
  | succ count ih =>
      have countInside : count < slots := by omega
      have before := ih (by omega)
      have unchanged : conversionPrefix owner base selected start states count ⟨count, countInside⟩ = states ⟨count, countInside⟩ := by
        simp [conversionPrefix]
      rw [conversionPrefix_succ owner base selected start states count countInside]
      by_cases chosen : selected ⟨count, countInside⟩ = true
      · rw [if_pos chosen]
        have step := convert_inventory (conversionPrefix owner base selected start states count) ⟨count, countInside⟩
          (owner ⟨count, countInside⟩) (start+count) (base ⟨count, countInside⟩) before (le_refl _)
        rw [unchanged] at step
        simpa only [Nat.succ_eq_add_one, Nat.add_assoc] using step
      · rw [if_neg chosen, ← unchanged, Function.update_eq_self]
        exact before.advance _ (by omega)

theorem freshConversions_inventory {slots : ℕ} (owner base : Fin slots → ℕ) (selected : Fin slots → Bool)
    (start : ℕ) (states : Fin slots → SideState) (inventory : Inventory states start) :
    Inventory (GreedyMerge.FreshIds.freshConversions owner base selected start states).1 (start+slots) := by
  have complete := conversionPrefix_inventory owner base selected start states inventory slots (le_refl _)
  have equal : conversionPrefix owner base selected start states slots =
      (GreedyMerge.FreshIds.freshConversions owner base selected start states).1 := by
    funext slot
    simp [conversionPrefix, GreedyMerge.FreshIds.freshConversions, slot.isLt]
  rwa [equal] at complete

open GreedyMerge.HeapAllocation

abbrev HeapFamilyInventory {n : ℕ} (states : HeapSides n) (next : ℕ) := Inventory (table states) next

theorem convertHeap_inventory {n : ℕ} (rank : ℕ → ℕ) (selected : External n → Bool → Bool)
    (start : ℕ) (states : HeapSides n) (inventory : HeapFamilyInventory states start) :
    HeapFamilyInventory (convertHeap rank selected start states).1 (start + Fintype.card (Place n)) := by
  dsimp only [convertHeap]
  simp only [HeapFamilyInventory, table_heap]
  exact freshConversions_inventory _ _ _ start (table states) inventory

theorem initial_inventory {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n) (K : ℤ) :
    HeapFamilyInventory (GreedyMerge.InitialBlocks.state snapshot tree K) (2*(2*n+1)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro slot family member
    have equal : family = GreedyMerge.InitialBlocks.slot ((encode n).symm slot).1 ((encode n).symm slot).2 := by
      simpa [table, GreedyMerge.InitialBlocks.state, names] using member
    rw [equal]
    exact List.mem_range.mp (GreedyMerge.InitialBlocks.slot_mem_birthIds _ _)
  · intro first second left right firstPresent secondPresent equal
    have firstEqual := Option.some.inj firstPresent
    have secondEqual := Option.some.inj secondPresent
    rw [← firstEqual, ← secondEqual] at equal
    obtain ⟨sameOwner, sameSide⟩ := GreedyMerge.InitialBlocks.slot_injective _ _ _ _ equal
    exact (encode n).symm.injective (Prod.ext sameOwner sameSide)
  · intro first second block grower member _
    simp [table, GreedyMerge.InitialBlocks.state] at member

end Greedy.FamilyNames
