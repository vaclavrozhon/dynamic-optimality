import Greedy.FamilyOrderConversions
import Greedy.FamilyOrderAccess

/-!
# Properties of a family after its grower has closed

`Closed family property states` says that no current grower uses this
family and every frozen fragment of it has `property`. A hereditary
property passes to literal descendants. This interface will preserve cut
separation after a complete consolidation, including across later births
of other families.
-/

namespace Greedy.ClosedFamilies

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.HeapAllocation

def Hereditary (property : Frozen → Prop) : Prop :=
  ∀ {before after : Frozen}, Descends after before → property before → property after

structure Closed {Slot : Type*} (family : ℕ) (property : Frozen → Prop) (states : Slot → SideState) : Prop where
  growing : ∀ slot grower, (states slot).grower = some grower → grower.family ≠ family
  frozen : ∀ slot block, block ∈ (states slot).shrinking → block.family = family → property block

theorem family_closed {slots next : ℕ} (states : Fin slots → SideState) (names : FamilyNames.Inventory states next)
    (slot : Fin slots) (block : Frozen) (member : block ∈ (states slot).shrinking)
    (property : Frozen → Prop)
    (holds : ∀ current fragment, fragment ∈ (states current).shrinking → fragment.family = block.family → property fragment) :
    Closed block.family property states :=
  ⟨fun current grower present => (names.sealed slot current block grower member present).symm, holds⟩

theorem Closed.inherited {Slot : Type*} {family : ℕ} {property : Frozen → Prop} {before after : Slot → SideState}
    (closed : Closed family property before) (hereditary : Hereditary property)
    (growers : ∀ slot grower, (after slot).grower = some grower →
      ∃ oldSlot old, (before oldSlot).grower = some old ∧ grower.family = old.family)
    (fragments : ∀ slot block, block ∈ (after slot).shrinking →
      ∃ oldSlot old, old ∈ (before oldSlot).shrinking ∧ Descends block old) : Closed family property after := by
  refine ⟨?_, ?_⟩
  · intro slot grower present equal
    obtain ⟨oldSlot, old, oldPresent, same⟩ := growers slot grower present
    exact closed.growing oldSlot old oldPresent (same.symm.trans equal)
  · intro slot block member equal
    obtain ⟨oldSlot, old, oldMem, descendant⟩ := fragments slot block member
    exact hereditary descendant (closed.frozen oldSlot old oldMem (descendant.1.symm.trans equal))

theorem Closed.additions {Slot : Type*} {family : ℕ} {property : Frozen → Prop} {before after : Slot → SideState}
    (closed : Closed family property before) (hereditary : Hereditary property)
    (growers : ∀ slot grower, (after slot).grower = some grower →
      (∃ oldSlot old, (before oldSlot).grower = some old ∧ grower.family = old.family) ∨ family < grower.family)
    (fragments : ∀ slot block, block ∈ (after slot).shrinking →
      (∃ oldSlot old, old ∈ (before oldSlot).shrinking ∧ Descends block old) ∨ family < block.family) :
    Closed family property after := by
  refine ⟨?_, ?_⟩
  · intro slot grower present equal
    rcases growers slot grower present with ⟨oldSlot, old, oldPresent, same⟩ | fresh
    · exact closed.growing oldSlot old oldPresent (same.symm.trans equal)
    · omega
  · intro slot block member equal
    rcases fragments slot block member with ⟨oldSlot, old, oldMem, descendant⟩ | fresh
    · exact hereditary descendant (closed.frozen oldSlot old oldMem (descendant.1.symm.trans equal))
    · omega

theorem conversions_closed {Slot : Type*} (family : ℕ) (property : Frozen → Prop)
    (owner fresh id base : Slot → ℕ) (selected : Slot → Bool) (states : Slot → SideState)
    (closed : Closed family property states) (newNames : ∀ slot, family < fresh slot) :
    Closed family property (fun slot => if selected slot then
      convert (owner slot) (fresh slot) (id slot) (base slot) (states slot) else states slot) := by
  refine ⟨?_, ?_⟩
  · intro slot grower present
    split_ifs at present
    · cases old : (states slot).grower with
      | none => simp [convert, old] at present
      | some previous =>
          by_cases empty : previous.members = []
          · exact closed.growing slot grower (by simpa [convert, old, empty] using present)
          · have same : emptyGrower (owner slot) (fresh slot) (id slot) = grower := by simpa [convert, old, empty] using present
            rw [← same]
            exact (Nat.ne_of_lt (newNames slot)).symm
    · exact closed.growing slot grower present
  · intro slot block member equal
    split_ifs at member
    · rcases FamilyOrder.convert_frozen_origin _ _ _ _ _ block member with old | ⟨grower, present, rfl⟩
      · exact closed.frozen slot block old equal
      · exact False.elim (closed.growing slot grower present equal)
    · exact closed.frozen slot block member equal

abbrev HeapClosed {n : ℕ} (family : ℕ) (property : Frozen → Prop) (states : HeapSides n) :=
  Closed family property (table states)

theorem convertHeap_closed {n : ℕ} (family start : ℕ) (property : Frozen → Prop)
    (rank : ℕ → ℕ) (selected : External n → Bool → Bool) (states : HeapSides n)
    (closed : HeapClosed family property states) (past : family < start) :
    HeapClosed family property (convertHeap rank selected start states).1 := by
  dsimp only [convertHeap]
  simp only [HeapClosed, table_heap]
  apply conversions_closed family property _ _ _ _ _ (table states) closed
  intro slot
  exact past.trans_le (Nat.le_add_right _ _)

end Greedy.ClosedFamilies
