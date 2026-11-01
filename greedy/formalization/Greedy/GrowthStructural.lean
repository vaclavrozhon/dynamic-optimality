import Greedy.GrowthInvariant

/-! Cuts, transfers, and rebasing preserve the same historical coverage. -/

namespace Greedy.GrowthJournal

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.HeapAllocation
open GreedyMerge.GrowthBook GreedyMerge.GrowthWindows

theorem Invariant.advance {n clock next : ℕ} {states : HeapSides n} {books : HeapBooks n}
    (inv : Invariant clock next states books) (newClock newNext : ℕ)
    (later : clock ≤ newClock) (more : next ≤ newNext) : Invariant newClock newNext states books :=
  ⟨heap_advance inv.good newClock newNext later more, inv.creators, inv.covered⟩

theorem Invariant.descendants {n clock next : ℕ} {before after : HeapSides n} {books : HeapBooks n}
    (inv : Invariant clock next before books)
    (growers : ∀ owner side, (after owner side).grower = (before owner side).grower)
    (descendants : ∀ owner side block, block ∈ (after owner side).shrinking →
      ∃ oldOwner oldSide old, old ∈ (before oldOwner oldSide).shrinking ∧ Descends block old) :
    Invariant clock next after books := by
  refine ⟨heap_grower_congr inv.good (fun owner side => (growers owner side).symm), ?_, ?_⟩
  · intro owner side grower present
    rw [growers] at present
    exact inv.creators owner side grower present
  · intro owner side block member
    obtain ⟨oldOwner, oldSide, old, oldMem, descendant⟩ := descendants owner side block member
    exact (inv.covered oldOwner oldSide old oldMem).descends descendant

theorem allocateCuts_invariant {n clock : ℕ} (cuts : List (ℕ × ℕ)) (start : ℕ)
    (states : HeapSides n) (books : HeapBooks n) (inv : Invariant clock start states books) :
    Invariant clock (allocateCuts cuts start states).next (allocateCuts cuts start states).states books := by
  have changed := inv.descendants (allocateCuts_grower cuts start states) (after := (allocateCuts cuts start states).states) ?_
  · exact changed.advance clock _ (le_refl _) (allocateCuts_next cuts start states)
  intro owner side block member
  have exactState := congrArg Prod.fst (allocateCuts_eq cuts start states)
  dsimp only at exactState
  rw [← exactState] at member
  obtain ⟨old, oldMem, descendant⟩ := prepareCuts_descends (allocateCuts cuts start states).names cuts 0 states owner side block member
  exact ⟨owner, side, old, oldMem, descendant⟩

theorem rebase_invariant {n clock next : ℕ} (before after : BST 0 n)
    (states : HeapSides n) (books : HeapBooks n) (inv : Invariant clock next states books) :
    Invariant clock next (rebaseAll before after states) books := by
  apply inv.descendants (after := rebaseAll before after states) (fun _ _ => rfl)
  intro owner side block member
  obtain ⟨old, oldMem, rfl⟩ := List.mem_map.mp member
  exact ⟨owner, side, old, oldMem, rfl, rfl, List.Sublist.refl _⟩

theorem junction_invariant {n clock : ℕ} (oldOwner newOwner : External n) (lo hi start : ℕ)
    (states : HeapSides n) (books : HeapBooks n) (inv : Invariant clock start states books) :
    let result := allocateJunction oldOwner newOwner lo hi start states
    Invariant clock result.next result.states books := by
  have changed := inv.descendants (junction_grower oldOwner newOwner lo hi start states)
    (after := (allocateJunction oldOwner newOwner lo hi start states).states) ?_
  · exact changed.advance clock _ (le_refl _) (allocateJunction_monotone oldOwner newOwner lo hi start states)
  intro owner side block member
  rw [allocateJunction_eq] at member
  unfold moveJunction at member
  split_ifs at member with old new
  · obtain ⟨original, originalMem, descendant⟩ := separateOuter_descends side (junctionCut side lo hi) _
      (states oldOwner side) block (List.mem_append_left _ member)
    exact ⟨oldOwner, side, original, originalMem, descendant⟩
  · change block ∈ (states newOwner side).shrinking ++ _ at member
    rcases List.mem_append.mp member with previous | moved
    · exact ⟨newOwner, side, block, previous, descends_refl _⟩
    · obtain ⟨original, originalMem, descendant⟩ := separateOuter_descends side (junctionCut side lo hi) _
        (states oldOwner side) block (List.mem_append_right _ moved)
      exact ⟨oldOwner, side, original, originalMem, descendant⟩
  · exact ⟨owner, side, block, member, descends_refl _⟩

end Greedy.GrowthJournal
