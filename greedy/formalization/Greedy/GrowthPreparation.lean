import LinkGrowthBook
import FreshFullPreparation

/-!
# Historical grower books through actual comparator preparation

Preparatory conversions close their current membership batch using the
same fresh family name as the concrete allocator. Deletions and cuts
preserve the current grower. The full per-slot journal retains its closed
batches, so chronological growth windows are not reconstructed from a
final live-state snapshot.
-/

namespace Greedy.GrowthJournal

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.HeapAllocation
open GreedyMerge.GrowthBook GreedyMerge.GrowthWindows

theorem heap_advance {n clock next : ℕ} {states : HeapSides n} {books : HeapBooks n}
    (good : HeapGood clock next states books) (newClock newNext : ℕ)
    (later : clock ≤ newClock) (more : next ≤ newNext) : HeapGood newClock newNext states books :=
  fun owner side => (good owner side).advance newClock newNext later more

theorem heap_grower_congr {n clock next : ℕ} {first second : HeapSides n} {books : HeapBooks n}
    (good : HeapGood clock next first books)
    (same : ∀ owner side, (first owner side).grower = (second owner side).grower) : HeapGood clock next second books :=
  fun owner side => (good owner side).grower_congr (same owner side)

theorem detachAll_grower {n : ℕ} (before : BST 0 n) (key start : ℕ) (states : HeapSides n)
    (owner : External n) (side : Bool) :
    (detachAll before key (conversionNames start) (conversionNames start) states owner side).grower =
      ((convertHeap before.externalDepth (fun owner side => growerHasKey key (states owner side)) start states).1 owner side).grower := by
  rw [convertHeap_apply]
  rfl

theorem detachAll_good {n : ℕ} (before : BST 0 n) (key clock start : ℕ)
    (states : HeapSides n) (books : HeapBooks n) (good : HeapGood clock start states books) :
    HeapGood clock (start + Fintype.card (Place n))
      (detachAll before key (conversionNames start) (conversionNames start) states)
      (convertHeapBooks (fun owner side => growerHasKey key (states owner side)) start states books) := by
  have converted := convertHeap_good before.externalDepth (fun owner side => growerHasKey key (states owner side))
    clock start states books good
  rw [← slot_count] at converted
  exact heap_grower_congr converted (fun owner side => (detachAll_grower before key start states owner side).symm)

noncomputable def detachBooks {n : ℕ} (before : BST 0 n) (start : ℕ) :
    List ℕ → ℕ → HeapSides n → HeapBooks n → HeapBooks n
  | [], _, _, books => books
  | key :: rest, stage, states, books =>
      let changed := detachAll before key (sequenceNames start stage) (sequenceNames start stage) states
      let nextBooks := convertHeapBooks (fun owner side => growerHasKey key (states owner side))
        (start + Fintype.card (Place n)*stage) states books
      detachBooks before start rest (stage+1) changed nextBooks

theorem detachBooks_good {n : ℕ} (before : BST 0 n) (clock start : ℕ)
    (ports : List ℕ) (stage : ℕ) (states : HeapSides n) (books : HeapBooks n)
    (good : HeapGood clock (start + Fintype.card (Place n)*stage) states books) :
    HeapGood clock (start + Fintype.card (Place n)*(stage+ports.length))
      (detachPorts before (sequenceNames start) (sequenceNames start) ports stage states).1
      (detachBooks before start ports stage states books) := by
  induction ports generalizing stage states books with
  | nil => simpa only [List.length_nil, Nat.add_zero, detachPorts, detachBooks] using good
  | cons key rest ih =>
      have head := detachAll_good before key clock (start + Fintype.card (Place n)*stage) states books good
      have step : HeapGood clock (start + Fintype.card (Place n)*(stage+1))
          (detachAll before key (sequenceNames start stage) (sequenceNames start stage) states)
          (convertHeapBooks (fun owner side => growerHasKey key (states owner side))
            (start + Fintype.card (Place n)*stage) states books) := by
        simpa only [sequenceNames, Nat.mul_add, Nat.mul_one, Nat.add_assoc] using head
      have tail := ih (stage+1) _ _ step
      simpa only [detachPorts, detachBooks, List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using tail

noncomputable def preparationBooks {n : ℕ} (before after : BST 0 n) (start : ℕ)
    (ports : List ℕ) (owners : Finset (External n)) (states : HeapSides n) (books : HeapBooks n) : HeapBooks n := by
  classical
  let names : NameSupply n := sequenceNames start
  let growing := prepareAllGrowers before after (names 0) (names 0) states
  let growingBooks := convertHeapBooks
    (fun owner side => decide (GrowerMismatch before after owner (states owner side))) start states books
  let detached := (detachPorts before names names ports 1 growing).1
  let detachedBooks := detachBooks before start ports 1 growing growingBooks
  exact convertHeapBooks (fun owner _ => decide (owner ∈ owners))
    (start + Fintype.card (Place n)*(ports.length+1)) detached detachedBooks

theorem preparationBooks_good {n : ℕ} (before after : BST 0 n) (clock start : ℕ)
    (ports : List ℕ) (owners : Finset (External n)) (states : HeapSides n) (books : HeapBooks n)
    (good : HeapGood clock start states books) :
    HeapGood clock (start + Fintype.card (Place n)*(ports.length+2))
      (preparedForCuts before after start ports owners states)
      (preparationBooks before after start ports owners states books) := by
  classical
  let names := sequenceNames (n:=n) start
  let growing := prepareAllGrowers before after (names 0) (names 0) states
  let growingBooks := convertHeapBooks
    (fun owner side => decide (GrowerMismatch before after owner (states owner side))) start states books
  let detached := (detachPorts before names names ports 1 growing).1
  let detachedBooks := detachBooks before start ports 1 growing growingBooks
  have grown : HeapGood clock (start + Fintype.card (Place n)*1) growing growingBooks := by
    have converted := convertHeap_good before.externalDepth
      (fun owner side => decide (GrowerMismatch before after owner (states owner side))) clock start states books good
    rw [← prepareAllGrowers_fresh_eq] at converted
    simpa only [growing, growingBooks, names, sequenceNames, Nat.mul_zero, Nat.add_zero, Nat.mul_one, slot_count] using converted
  have removed := detachBooks_good before clock start ports 1 growing growingBooks grown
  have sealed := convertHeap_good before.externalDepth (fun owner _ => decide (owner ∈ owners))
    clock (start + Fintype.card (Place n)*(ports.length+1)) detached detachedBooks
    (by simpa only [Nat.add_comm] using removed)
  rw [← sealOwners_fresh_eq] at sealed
  simpa only [preparedForCuts, preparationBooks, names, sequenceNames, slot_count,
    Nat.mul_add, Nat.mul_two, Nat.mul_one, Nat.add_assoc, growing, growingBooks, detached, detachedBooks] using sealed

theorem prepareCuts_grower {n : ℕ} (names : NameSupply n) (cuts : List (ℕ × ℕ)) (stage : ℕ)
    (states : HeapSides n) (owner : External n) (side : Bool) :
    ((prepareCuts names cuts stage states).1 owner side).grower = (states owner side).grower := by
  induction cuts generalizing stage states with
  | nil => rfl
  | cons cut rest ih =>
      change ((prepareCuts names rest (stage+1) (cutAllOwners cut.1 (names stage) states)).1 owner side).grower = _
      rw [ih]
      rfl

theorem allocateCuts_grower {n : ℕ} (cuts : List (ℕ × ℕ)) (start : ℕ)
    (states : HeapSides n) (owner : External n) (side : Bool) :
    ((allocateCuts cuts start states).states owner side).grower = (states owner side).grower := by
  have exactState := congrArg (fun result => (result.1 owner side).grower) (allocateCuts_eq cuts start states)
  rw [prepareCuts_grower] at exactState
  exact exactState.symm

theorem allocated_preparation_good {n depth : ℕ} {before after : BST 0 n}
    (profile : RotationCutProfile before after depth) (clock start : ℕ) (ports : List ℕ)
    (owners : Finset (External n)) (states : HeapSides n) (books : HeapBooks n)
    (good : HeapGood clock start states books) :
    let result := allocateComparatorPreparation profile ports owners start states
    HeapGood clock result.next result.states (preparationBooks before after start ports owners states books) := by
  have prepared := preparationBooks_good before after clock start ports owners states books good
  have cutGood := heap_grower_congr prepared
    (fun owner side => (allocateCuts_grower profile.entries
      (start + Fintype.card (Place n)*(ports.length+2)) _ owner side).symm)
  exact heap_advance cutGood clock _ (le_refl _) (allocateCuts_next profile.entries _ _)

end Greedy.GrowthJournal
