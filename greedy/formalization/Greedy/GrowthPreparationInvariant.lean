import Greedy.GrowthStructural

/-! Frozen-family coverage throughout the literal fresh preparation program. -/

namespace Greedy.GrowthJournal

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.HeapAllocation
open GreedyMerge.GrowthBook GreedyMerge.GrowthWindows

theorem preparationBooks_invariant {n : ℕ} (before after : BST 0 n) (clock start : ℕ)
    (ports : List ℕ) (owners : Finset (External n)) (states : HeapSides n) (books : HeapBooks n)
    (inv : Invariant clock start states books) :
    Invariant clock (start + Fintype.card (Place n)*(ports.length+2))
      (preparedForCuts before after start ports owners states)
      (preparationBooks before after start ports owners states books) := by
  classical
  let names := sequenceNames (n:=n) start
  let growing := prepareAllGrowers before after (names 0) (names 0) states
  let growingBooks := convertHeapBooks
    (fun owner side => decide (GrowerMismatch before after owner (states owner side))) start states books
  let detached := (detachPorts before names names ports 1 growing).1
  let detachedBooks := detachBooks before start ports 1 growing growingBooks
  have grown : Invariant clock (start + Fintype.card (Place n)*1) growing growingBooks := by
    have converted := convertHeap_invariant before.externalDepth
      (fun owner side => decide (GrowerMismatch before after owner (states owner side))) start states books inv
    rw [← prepareAllGrowers_fresh_eq] at converted
    simpa only [growing, growingBooks, names, sequenceNames, Nat.mul_zero, Nat.add_zero, Nat.mul_one, slot_count] using converted
  have removed := detachBooks_invariant before clock start ports 1 growing growingBooks grown
  have sealed := convertHeap_invariant before.externalDepth (fun owner _ => decide (owner ∈ owners))
    (start + Fintype.card (Place n)*(ports.length+1)) detached detachedBooks
    (by simpa only [Nat.add_comm] using removed)
  rw [← sealOwners_fresh_eq] at sealed
  simpa only [preparedForCuts, preparationBooks, names, sequenceNames, slot_count,
    Nat.mul_add, Nat.mul_two, Nat.mul_one, Nat.add_assoc, growing, growingBooks, detached, detachedBooks] using sealed

theorem allocated_preparation_invariant {n depth : ℕ} {before after : BST 0 n}
    (profile : RotationCutProfile before after depth) (clock start : ℕ) (ports : List ℕ)
    (owners : Finset (External n)) (states : HeapSides n) (books : HeapBooks n)
    (inv : Invariant clock start states books) :
    let result := allocateComparatorPreparation profile ports owners start states
    Invariant clock result.next result.states (preparationBooks before after start ports owners states books) :=
  allocateCuts_invariant profile.entries _ _ _
    (preparationBooks_invariant before after clock start ports owners states books inv)

end Greedy.GrowthJournal
