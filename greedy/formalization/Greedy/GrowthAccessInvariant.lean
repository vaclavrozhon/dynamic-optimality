import Greedy.GrowthInvariant

/-! Actual access links retain historical coverage of every frozen fragment. -/

namespace Greedy.GrowthJournal

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.HeapAllocation
open GreedyMerge.GrowthBook GreedyMerge.GrowthWindows GreedyMerge.ActualLinks

theorem append_creator (owner : ℕ) (entry : Entry) (state : SideState)
    (creators : ∀ grower, state.grower = some grower → grower.creator = owner) :
    ∀ grower, (appendGrower entry state).grower = some grower → grower.creator = owner := by
  intro grower present
  cases old : state.grower with
  | none => simp [appendGrower, old] at present
  | some previous =>
      have equal : grow entry previous = grower := by simpa [appendGrower, old] using present
      rw [← equal]
      exact creators previous old

theorem linkBook_invariant {n clock next : ℕ} (states : HeapSides n) (books : HeapBooks n)
    (source winner loser : External n) (sourceSide targetSide : Bool) (entry : Entry)
    (time : entry.joined = clock) (inv : Invariant clock next states books) :
    Invariant (clock+1) next (linkState states source winner loser sourceSide targetSide entry)
      (linkBook winner targetSide clock books) := by
  refine ⟨linkBook_good clock next states books source winner loser sourceSide targetSide entry time inv.good, ?_, ?_⟩
  · intro owner side grower present
    unfold linkState at present
    split_ifs at present
    · exact append_creator owner.val entry (states owner side) (inv.creators owner side) grower present
    · exact inv.creators owner side grower present
    · exact inv.creators owner side grower present
  · intro owner side block member
    have extension := linkBook_extends winner targetSide clock books
    unfold linkState at member
    split_ifs at member
    · exact (inv.covered owner side block member).mono extension
    · exact (erase_covered books loser.val (states owner side) (inv.covered owner side) block member).mono extension
    · exact (inv.covered owner side block member).mono extension

theorem runBook_invariant {n : ℕ} (source : External n)
    (sourceSide : External n × External n → Bool) (reader : ℕ → States n → ℕ → ℤ)
    (clock next : ℕ) (states : HeapSides n) (books : HeapBooks n)
    (events : List (External n × External n)) (inv : Invariant clock next states books) :
    Invariant (clock+events.length) next (runLinks source sourceSide reader clock states events)
      (runBook clock books events) := by
  induction events generalizing clock states books with
  | nil => simpa [runLinks, runBook] using inv
  | cons event rest ih =>
      have head := linkBook_invariant (clock := clock) states books source event.1 event.2 (sourceSide event) (targetSide event)
        (arrivalEntry (reader clock states) event.1 event.2 clock) rfl inv
      have tail := ih (clock+1) _ _ head
      simpa only [runLinks, runBook, List.length_cons, Nat.add_assoc, Nat.add_comm 1] using tail

end Greedy.GrowthJournal
