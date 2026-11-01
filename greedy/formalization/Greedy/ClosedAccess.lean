import Greedy.ClosedFamilies

/-! A later access cannot append to an already closed family. -/

namespace Greedy.ClosedFamilies

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.ActualLinks GreedyMerge.HeapAllocation

theorem linkState_closed {n family : ℕ} {property : Frozen → Prop} (states : HeapSides n)
    (source winner loser : External n) (sourceSide targetSide : Bool) (entry : Entry)
    (closed : HeapClosed family property states) (hereditary : Hereditary property) :
    HeapClosed family property (linkState states source winner loser sourceSide targetSide entry) := by
  apply closed.inherited hereditary
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
          exact ⟨slot, previous, old, by rw [← same]; rfl⟩
    · exact ⟨slot, grower, present, rfl⟩
    · exact ⟨slot, grower, present, rfl⟩
  · intro slot block member
    change block ∈ (linkState states source winner loser sourceSide targetSide entry
      ((encode n).symm slot).1 ((encode n).symm slot).2).shrinking at member
    unfold linkState at member
    split_ifs at member
    · exact ⟨slot, block, member, descends_refl _⟩
    · obtain ⟨old, oldMem, rfl⟩ := List.mem_map.mp member
      exact ⟨slot, old, oldMem, erase_descends old loser.val⟩
    · exact ⟨slot, block, member, descends_refl _⟩

theorem runLinks_closed {n family : ℕ} {property : Frozen → Prop} (source : External n)
    (sourceSide : External n × External n → Bool) (reader : ℕ → States n → ℕ → ℤ)
    (clock : ℕ) (states : HeapSides n) (events : List (External n × External n))
    (closed : HeapClosed family property states) (hereditary : Hereditary property) :
    HeapClosed family property (runLinks source sourceSide reader clock states events) := by
  induction events generalizing clock states with
  | nil => exact closed
  | cons event rest ih =>
      exact ih (clock+1) _ (linkState_closed states source event.1 event.2 (sourceSide event) (targetSide event)
        (arrivalEntry (reader clock states) event.1 event.2 clock) closed hereditary)

end Greedy.ClosedFamilies
