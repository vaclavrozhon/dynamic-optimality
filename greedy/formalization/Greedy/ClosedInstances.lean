import Greedy.ClosedFamilies

/-!
Frozen instance properties persist while the instance keeps its id.
Fresh splits retire that id; they do not append members to the old instance.
-/

namespace Greedy.ClosedInstances

open Splay.Rank GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.HeapAllocation

structure Closed {Slot : Type*} (id : ℕ) (property : Frozen → Prop) (states : Slot → SideState) : Prop where
  growing : ∀ slot grower, (states slot).grower = some grower → grower.id ≠ id
  frozen : ∀ slot block, block ∈ (states slot).shrinking → block.id = id → property block

abbrev HeapClosed {n : ℕ} (id : ℕ) (property : Frozen → Prop) (states : HeapSides n) := Closed id property (table states)

theorem instance_closed {slots next : ℕ} (states : Fin slots → SideState)
    (inventory : GreedyMerge.FreshIds.Inventory states next) (slot : Fin slots) (block : Frozen)
    (member : block ∈ (states slot).shrinking) (property : Frozen → Prop)
    (holds : ∀ current fragment, fragment ∈ (states current).shrinking → fragment.id = block.id → property fragment) :
    Closed block.id property states := by
  refine ⟨?_, holds⟩
  intro current grower present same
  have blockId : block.id ∈ liveIds (states slot) := List.mem_append_left _ (List.mem_map.mpr ⟨block, member, rfl⟩)
  have growerId : block.id ∈ liveIds (states current) := by
    simp [liveIds, present, same]
  have location := inventory.locations slot current block.id blockId growerId
  subst current
  have disjoint := (List.nodup_append.mp (inventory.localUnique slot)).2.2
  exact disjoint block.id (List.mem_map.mpr ⟨block, member, rfl⟩) block.id (by simp [present, same]) rfl

theorem Closed.inherited {Slot : Type*} {id : ℕ} {property : Frozen → Prop} {before after : Slot → SideState}
    (closed : Closed id property before) (hereditary : ClosedFamilies.Hereditary property)
    (growers : ∀ slot grower, (after slot).grower = some grower →
      ∃ oldSlot old, (before oldSlot).grower = some old ∧ grower.id = old.id)
    (fragments : ∀ slot block, block ∈ (after slot).shrinking →
      ∃ oldSlot old, old ∈ (before oldSlot).shrinking ∧ block.id = old.id ∧ Descends block old) : Closed id property after := by
  refine ⟨?_, ?_⟩
  · intro slot grower present equal
    obtain ⟨oldSlot, old, oldPresent, same⟩ := growers slot grower present
    exact closed.growing oldSlot old oldPresent (same.symm.trans equal)
  · intro slot block member equal
    obtain ⟨oldSlot, old, oldMem, same, descendant⟩ := fragments slot block member
    exact hereditary descendant (closed.frozen oldSlot old oldMem (same.symm.trans equal))

theorem Closed.additions {Slot : Type*} {id : ℕ} {property : Frozen → Prop} {before after : Slot → SideState}
    (closed : Closed id property before) (hereditary : ClosedFamilies.Hereditary property)
    (growers : ∀ slot grower, (after slot).grower = some grower →
      (∃ oldSlot old, (before oldSlot).grower = some old ∧ grower.id = old.id) ∨ id < grower.id)
    (fragments : ∀ slot block, block ∈ (after slot).shrinking →
      (∃ oldSlot old, old ∈ (before oldSlot).shrinking ∧ block.id = old.id ∧ Descends block old) ∨ id < block.id) :
    Closed id property after := by
  refine ⟨?_, ?_⟩
  · intro slot grower present equal
    rcases growers slot grower present with ⟨oldSlot, old, oldPresent, same⟩ | fresh
    · exact closed.growing oldSlot old oldPresent (same.symm.trans equal)
    · omega
  · intro slot block member equal
    rcases fragments slot block member with ⟨oldSlot, old, oldMem, same, descendant⟩ | fresh
    · exact hereditary descendant (closed.frozen oldSlot old oldMem (same.symm.trans equal))
    · omega

theorem cutList_old_descendant (side : Bool) (cut fresh : ℕ) (blocks : List Frozen)
    (piece : Frozen) (member : piece ∈ cutList side cut fresh blocks) (old : piece.id < fresh) :
    ∃ before, before ∈ blocks ∧ piece.id = before.id ∧ Descends piece before := by
  classical
  induction blocks generalizing fresh with
  | nil => simp [cutList] at member
  | cons block rest ih =>
      rcases List.mem_append.mp member with head | tail
      · by_cases crossing : Straddles cut block
        · simp only [cutBlock, if_pos crossing, List.mem_cons, List.not_mem_nil, or_false] at head
          rcases head with rfl | rfl <;> simp only [GreedyMerge.OrderedBlocks.splitLeft, GreedyMerge.OrderedBlocks.splitRight] at old <;> omega
        · have equal : piece = block := by simpa only [cutBlock, if_neg crossing, List.mem_singleton] using head
          exact ⟨block, List.mem_cons_self, congrArg Frozen.id equal, equal ▸ descends_refl block⟩
      · obtain ⟨before, beforeMem, same, descendant⟩ := ih (fresh+2) tail (by omega)
        exact ⟨before, List.mem_cons_of_mem _ beforeMem, same, descendant⟩

theorem heap_old_descendants {n id : ℕ} {property : Frozen → Prop} {before after : HeapSides n}
    (closed : HeapClosed id property before) (hereditary : ClosedFamilies.Hereditary property)
    (growers : ∀ owner side, (after owner side).grower = (before owner side).grower)
    (fragments : ∀ owner side block, block ∈ (after owner side).shrinking → block.id = id →
      ∃ oldOwner oldSide old, old ∈ (before oldOwner oldSide).shrinking ∧ old.id = id ∧ Descends block old) :
    HeapClosed id property after := by
  refine ⟨?_, ?_⟩
  · intro slot grower present
    exact closed.growing slot grower ((growers _ _).symm.trans present)
  · intro slot block member same
    obtain ⟨oldOwner, oldSide, old, oldMem, oldId, descendant⟩ := fragments _ _ block member same
    exact hereditary descendant (closed.frozen (encode n (oldOwner, oldSide)) old (by simpa [table] using oldMem) oldId)

end Greedy.ClosedInstances
