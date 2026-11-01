import Greedy.IncomingAccess

/-! Weighted subsets of actual indexed losing events. -/

namespace Greedy.AtomicDepartures

open Splay.Tree Splay.Tree.BST Splay.Rank GreedyMerge.OrderedBlocks GreedyMerge.Primitives
open GreedyMerge.Fringe GreedyMerge.Fringe.Schedule GreedyForest.Phase
open scoped BigOperators

theorem small_count {lo hi : ℕ} (rank record owner : ℕ → ℕ) (tree : BST lo hi)
    (projection : Projection (rank ∘ record) owner tree) (localOwners : LocalOwners (rank ∘ record) owner lo hi)
    (injective : Set.InjOn record {key | key ∈ atoms tree}) (block : Frozen) (small : ClosedInstances.Small block)
    (events : Finset (Fin (schedule owner tree).length))
    (losers : ∀ i ∈ events, record ((schedule owner tree).get i).2 ∈ ClosedInstances.keys block) : events.card ≤ 1 := by
  have run := schedule_run (rank ∘ record) owner tree projection localOwners
  have injection : Function.Injective (fun i : Fin (schedule owner tree).length => record ((schedule owner tree).get i).2) := by
    intro first second equal
    exact actual_loser_injective run (atoms_nodup tree)
      (injective (run.event_members _ (List.get_mem _ first)).2 (run.event_members _ (List.get_mem _ second)).2 equal)
  have subset : events.image (fun i => record ((schedule owner tree).get i).2) ⊆ ClosedInstances.keys block := by
    intro key member
    obtain ⟨i, iMem, rfl⟩ := Finset.mem_image.mp member
    exact losers i iMem
  have size := Finset.card_le_card subset
  rw [Finset.card_image_of_injective _ injection] at size
  exact size.trans small

theorem sum_le_capacity {Event : Type*} (events : Finset Event) (weight : Event → ℤ)
    (range : ℤ) (capacity : ℕ) (rangeNonneg : 0 ≤ range)
    (size : events.card ≤ capacity) (bounded : ∀ event ∈ events, weight event ≤ range) :
    (∑ event ∈ events, weight event) ≤ (capacity : ℤ)*range := by
  calc
    _ ≤ ∑ _event ∈ events, range := Finset.sum_le_sum bounded
    _ = (events.card : ℤ)*range := by simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast size) rangeNonneg

end Greedy.AtomicDepartures
