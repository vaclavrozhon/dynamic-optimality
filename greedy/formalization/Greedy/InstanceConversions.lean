import Greedy.ClosedInstances

/-! Conversions cannot reopen an existing frozen instance. -/

namespace Greedy.ClosedInstances

open Splay.Rank GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.HeapAllocation

theorem conversions_closed {Slot : Type*} (id : ℕ) (property : Frozen → Prop)
    (owner family fresh base : Slot → ℕ) (selected : Slot → Bool) (states : Slot → SideState)
    (closed : Closed id property states) (newIds : ∀ slot, id < fresh slot) :
    Closed id property (fun slot => if selected slot then convert (owner slot) (family slot) (fresh slot) (base slot) (states slot) else states slot) := by
  refine ⟨?_, ?_⟩
  · intro slot grower present
    split_ifs at present
    · cases old : (states slot).grower with
      | none => simp [convert, old] at present
      | some previous =>
          by_cases empty : previous.members = []
          · exact closed.growing slot grower (by simpa [convert, old, empty] using present)
          · have same : emptyGrower (owner slot) (family slot) (fresh slot) = grower := by simpa [convert, old, empty] using present
            rw [← same]
            exact (Nat.ne_of_lt (newIds slot)).symm
    · exact closed.growing slot grower present
  · intro slot block member equal
    split_ifs at member
    · rcases FamilyOrder.convert_frozen_origin _ _ _ _ _ block member with old | ⟨grower, present, rfl⟩
      · exact closed.frozen slot block old equal
      · exact False.elim (closed.growing slot grower present equal)
    · exact closed.frozen slot block member equal

theorem convertHeap_closed {n : ℕ} (id start : ℕ) (property : Frozen → Prop)
    (rank : ℕ → ℕ) (selected : External n → Bool → Bool) (states : HeapSides n)
    (closed : HeapClosed id property states) (past : id < start) :
    HeapClosed id property (convertHeap rank selected start states).1 := by
  dsimp only [convertHeap]
  simp only [HeapClosed, table_heap]
  apply conversions_closed id property _ _ _ _ _ (table states) closed
  intro slot
  exact past.trans_le (Nat.le_add_right _ _)

theorem Closed.with_property {Slot : Type*} {id : ℕ} {oldProperty : Frozen → Prop} {states : Slot → SideState}
    (closed : Closed id oldProperty states) (property : Frozen → Prop)
    (holds : ∀ slot block, block ∈ (states slot).shrinking → block.id = id → property block) : Closed id property states :=
  ⟨closed.growing, holds⟩

end Greedy.ClosedInstances
