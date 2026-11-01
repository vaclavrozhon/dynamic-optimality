import Greedy.GrowthCoverage

/-! A common historical invariant for growing and frozen block records. -/

namespace Greedy.GrowthJournal

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.HeapAllocation
open GreedyMerge.GrowthBook GreedyMerge.GrowthWindows GreedyMerge.ActualLinks

def Creators {n : ℕ} (states : HeapSides n) : Prop :=
  ∀ owner side grower, (states owner side).grower = some grower → grower.creator = owner.val

structure Invariant {n : ℕ} (clock next : ℕ) (states : HeapSides n) (books : HeapBooks n) : Prop where
  good : HeapGood clock next states books
  creators : Creators states
  covered : HeapCovered books states

theorem convert_creator (owner family id base : ℕ) (state : SideState)
    (creator : ∀ grower, state.grower = some grower → grower.creator = owner) :
    ∀ grower, (convert owner family id base state).grower = some grower → grower.creator = owner := by
  intro grower present
  cases old : state.grower with
  | none => simpa [convert, old] using present
  | some previous =>
      by_cases empty : previous.members = []
      · exact creator grower (by simpa [convert, old, empty] using present)
      · have equal : emptyGrower owner family id = grower := by
          simpa only [convert, old, empty, ↓reduceIte, Option.some.injEq] using present
        rw [← equal]
        rfl

theorem convertHeap_creators {n : ℕ} (rank : ℕ → ℕ) (selected : External n → Bool → Bool)
    (start : ℕ) (states : HeapSides n) (creators : Creators states) :
    Creators (convertHeap rank selected start states).1 := by
  intro owner side
  rw [convertHeap_apply]
  split_ifs
  · exact convert_creator _ _ _ _ _ (creators owner side)
  · exact creators owner side

theorem convertHeap_covered {n clock : ℕ} (rank : ℕ → ℕ) (selected : External n → Bool → Bool)
    (start : ℕ) (states : HeapSides n) (books : HeapBooks n) (inv : Invariant clock start states books) :
    HeapCovered (convertHeapBooks selected start states books) (convertHeap rank selected start states).1 := by
  intro owner side block member
  rw [convertHeap_apply] at member
  split_ifs at member
  · exact convert_covered books _ owner side (states owner side) _ _ _
      (inv.covered owner side) (inv.good owner side).matched (inv.creators owner side)
      (convertHeapBooks_extends selected start states books) block member
  · exact (inv.covered owner side block member).mono (convertHeapBooks_extends selected start states books)

theorem convertHeap_invariant {n clock : ℕ} (rank : ℕ → ℕ) (selected : External n → Bool → Bool)
    (start : ℕ) (states : HeapSides n) (books : HeapBooks n) (inv : Invariant clock start states books) :
    Invariant clock (start + 2*(2*n+1)) (convertHeap rank selected start states).1
      (convertHeapBooks selected start states books) :=
  ⟨convertHeap_good rank selected clock start states books inv.good,
    convertHeap_creators rank selected start states inv.creators,
    convertHeap_covered rank selected start states books inv⟩

theorem erase_covered {n : ℕ} (books : HeapBooks n) (key : ℕ) (state : SideState)
    (covered : ∀ block ∈ state.shrinking, Covered books block) :
    ∀ block ∈ (eraseFrozenKey key state).shrinking, Covered books block := by
  intro block member
  obtain ⟨before, beforeMem, rfl⟩ := List.mem_map.mp member
  exact (covered before beforeMem).descends (erase_descends before key)

theorem detachAll_invariant {n clock : ℕ} (before : BST 0 n) (key start : ℕ)
    (states : HeapSides n) (books : HeapBooks n) (inv : Invariant clock start states books) :
    Invariant clock (start + Fintype.card (Place n))
      (detachAll before key (conversionNames start) (conversionNames start) states)
      (convertHeapBooks (fun owner side => growerHasKey key (states owner side)) start states books) := by
  let selected := fun (owner : External n) (side : Bool) => growerHasKey key (states owner side)
  let converted := (convertHeap before.externalDepth selected start states).1
  let convertedBooks := convertHeapBooks selected start states books
  have convertedInv := convertHeap_invariant before.externalDepth selected start states books inv
  refine ⟨detachAll_good before key clock start states books inv.good, ?_, ?_⟩
  · intro owner side grower present
    rw [detachAll_grower] at present
    exact convertedInv.creators owner side grower present
  · intro owner side block member
    have equal : detachAll before key (conversionNames start) (conversionNames start) states owner side =
        eraseFrozenKey key (converted owner side) := by
      dsimp only [converted]
      rw [convertHeap_apply]
      rfl
    rw [equal] at member
    exact erase_covered convertedBooks key (converted owner side) (convertedInv.covered owner side) block member

theorem detachBooks_invariant {n : ℕ} (before : BST 0 n) (clock start : ℕ)
    (ports : List ℕ) (stage : ℕ) (states : HeapSides n) (books : HeapBooks n)
    (inv : Invariant clock (start + Fintype.card (Place n)*stage) states books) :
    Invariant clock (start + Fintype.card (Place n)*(stage+ports.length))
      (detachPorts before (sequenceNames start) (sequenceNames start) ports stage states).1
      (detachBooks before start ports stage states books) := by
  induction ports generalizing stage states books with
  | nil => simpa only [List.length_nil, Nat.add_zero, detachPorts, detachBooks] using inv
  | cons key rest ih =>
      have head := detachAll_invariant before key (start + Fintype.card (Place n)*stage) states books inv
      have step : Invariant clock (start + Fintype.card (Place n)*(stage+1))
          (detachAll before key (sequenceNames start stage) (sequenceNames start stage) states)
          (convertHeapBooks (fun owner side => growerHasKey key (states owner side))
            (start + Fintype.card (Place n)*stage) states books) := by
        simpa only [sequenceNames, Nat.mul_add, Nat.mul_one, Nat.add_assoc] using head
      have tail := ih (stage+1) _ _ step
      simpa only [detachPorts, detachBooks, List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using tail

theorem initial_invariant {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n) (K : ℤ) :
    Invariant (GreedyMerge.InitialBlocks.epoch n) (2*(2*n+1)) (GreedyMerge.InitialBlocks.state snapshot tree K)
      (GreedyMerge.GrowthBook.initial snapshot tree K) := by
  refine ⟨initial_heap_good snapshot tree K, ?_, initial_covered snapshot tree K⟩
  intro owner side grower present
  exact (GreedyMerge.InitialBlocks.state_valid snapshot tree K owner side).2.2 grower present

end Greedy.GrowthJournal
