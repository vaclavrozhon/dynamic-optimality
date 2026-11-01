import Greedy.FamilyNames
import FrozenFamilyHistory
import FreshPortRestoration

/-! Fresh singleton families never collide with a still-growing family. -/

namespace Greedy.FamilyNames

open GreedyMerge.OrderedBlocks GreedyMerge.Primitives

theorem Inventory.additions {slots next later : ℕ} {before after : Fin slots → SideState}
    (inventory : Inventory before next) (advance : next ≤ later)
    (growers : ∀ slot, (after slot).grower = (before slot).grower)
    (origins : ∀ slot block, block ∈ (after slot).shrinking →
      (∃ oldSlot old, old ∈ (before oldSlot).shrinking ∧ Descends block old) ∨
      (next ≤ block.family ∧ block.family < later)) : Inventory after later := by
  refine ⟨?_, ?_, ?_⟩
  · intro slot family member
    rcases List.mem_append.mp member with frozen | growing
    · obtain ⟨block, blockMem, rfl⟩ := List.mem_map.mp frozen
      rcases origins slot block blockMem with ⟨oldSlot, old, oldMem, descendant⟩ | fresh
      · rw [descendant.1]
        exact (inventory.below oldSlot old.family (frozen_mem _ _ oldMem)).trans_le advance
      · exact fresh.2
    · exact (inventory.below slot family (List.mem_append_right _ (by simpa only [growers] using growing))).trans_le advance
  · intro first second left right firstPresent secondPresent same
    rw [growers] at firstPresent secondPresent
    exact inventory.growing first second left right firstPresent secondPresent same
  · intro first second block grower member present same
    rw [growers] at present
    rcases origins first block member with ⟨oldSlot, old, oldMem, descendant⟩ | fresh
    · exact inventory.sealed oldSlot second old grower oldMem present (descendant.1.symm.trans same)
    · have bound := inventory.below second grower.family (grower_mem _ _ present)
      omega

theorem installPaid_inventory {slots next : ℕ} (states : Fin slots → SideState) (selected : Fin slots)
    (owner : ℕ) (side : Bool) (splitStart id family base : ℕ) (entry : Entry)
    (inventory : Inventory states next) (fresh : next ≤ family) :
    Inventory (Function.update states selected
      (installPaid owner side splitStart id family base entry (states selected))) (family+1) := by
  apply inventory.additions (by omega)
  · intro slot
    by_cases same : slot = selected
    · subst slot; simp [installPaid]
    · rw [Function.update_of_ne same]
  · intro slot block member
    by_cases same : slot = selected
    · subst slot
      rw [Function.update_self] at member
      change block ∈ (separateOuter side entry.key splitStart (states selected)).1 ++
        [singleton id family owner base entry] ++ (separateOuter side entry.key splitStart (states selected)).2 at member
      have old (inherited : block ∈ (separateOuter side entry.key splitStart (states selected)).1 ++
          (separateOuter side entry.key splitStart (states selected)).2) :
          ∃ oldSlot original, original ∈ (states oldSlot).shrinking ∧ Descends block original := by
        obtain ⟨original, originalMem, descendant⟩ := separateOuter_descends side entry.key splitStart (states selected) block inherited
        exact ⟨selected, original, originalMem, descendant⟩
      rcases List.mem_append.mp member with first | last
      · rcases List.mem_append.mp first with inherited | born
        · exact Or.inl (old (List.mem_append_left _ inherited))
        · have equal := List.mem_singleton.mp born
          subst block
          exact Or.inr ⟨fresh, Nat.lt_succ_self _⟩
      · exact Or.inl (old (List.mem_append_right _ last))
    · rw [Function.update_of_ne same] at member
      exact Or.inl ⟨slot, block, member, descends_refl _⟩

theorem freshPaidSlot_inventory {slots : ℕ} (slot : Fin slots) (owner base : ℕ) (side : Bool)
    (start : ℕ) (entry : Entry) (states : Fin slots → SideState) (inventory : Inventory states start) :
    Inventory (GreedyMerge.FreshIds.freshPaidSlot slot owner base side start entry states).1
      (GreedyMerge.FreshIds.freshPaidSlot slot owner base side start entry states).2 := by
  let converted := convert owner start start base (states slot)
  let paid := start+1+2*converted.shrinking.length
  have first := convert_inventory states slot owner start base inventory (le_refl _)
  have second := installPaid_inventory (Function.update states slot converted) slot owner side (start+1) paid paid base entry first
    (show start+1 ≤ paid by dsimp [paid]; omega)
  simp only [Function.update_self, Function.update_idem] at second
  exact second

end Greedy.FamilyNames
