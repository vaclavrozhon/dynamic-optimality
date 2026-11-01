import Greedy.OutgoingCharges

/-! Local allowances for the two positive-excess charge destinations. -/

namespace Greedy.OutgoingExcess

open Splay.Tree Splay.Analysis GreedyMerge.OrderedBlocks GreedyMerge.Primitives
open GreedyMerge.ActualBlockPartition GreedyMerge.Fringe GreedyMerge.Fringe.Schedule
open GreedyMerge.AccessSourceAccounting GreedyForest.Phase
open scoped BigOperators

theorem nonroot_le_full {lo hi : ℕ} (rank : ℕ → ℕ) (initial : ℕ → ℤ)
    (record owner : ℕ → ℕ) (tree : BST lo hi) (block : Frozen) :
    amount .nonrootWinner rank initial record owner tree block ≤ fullAmount rank initial record owner tree block := by
  apply Finset.sum_le_sum
  intro edge _
  have nonneg := extra_nonneg rank initial record edge
  by_cases selected : Selected .nonrootWinner (treeOwner owner tree) record block edge
  · have outgoing : record edge.1 ∈ blockKeys block ∧ record edge.2 ∉ blockKeys block := ⟨selected.1, selected.2.1⟩
    simp only [weight, if_pos selected, fullWeight, if_pos outgoing]
    exact le_refl _
  · simp only [weight, if_neg selected]
    unfold fullWeight
    split_ifs <;> omega

theorem spec {lo hi : ℕ} (metric : Metric) {rank : ℕ → ℕ} {initial : ℕ → ℤ} {record : ℕ → ℕ}
    {tree : BST lo hi} {state : SideState} (view : SideView rank initial record tree state)
    (owner : ℕ → ℕ) (projection : Projection (rank ∘ record) owner tree)
    (localOwners : LocalOwners (rank ∘ record) owner lo hi)
    (injective : Set.InjOn record {key | key ∈ atoms tree})
    (block : Frozen) (member : block ∈ state.shrinking) (H : ℕ)
    (ranks : ∀ key, 2*lo ≤ key → key ≤ 2*hi → rank (record key) ≤ H) :
    0 ≤ amount metric rank initial record owner tree block ∧
      amount metric rank initial record owner tree block ≤ 4*((contractedGap H : ℤ)-1) ∧
      (ClosedInstances.Small block → amount metric rank initial record owner tree block ≤ range metric H) ∧
      (amount metric rank initial record owner tree block ≠ 0 →
        ∃ edge ∈ schedule owner tree, record edge.2 ∈ ClosedInstances.keys block) := by
  classical
  have run := schedule_run (rank ∘ record) owner tree projection localOwners
  have bounded : ∀ edge ∈ schedule owner tree, extra rank initial record edge ≤ (contractedGap H : ℤ)-1 := by
    intro edge edgeMem
    have endpoints := run.event_members edge edgeMem
    have loser := (atoms_mem_iff tree _).mp endpoints.2
    exact extra_bound rank initial record edge H (ranks _ loser.1 loser.2)
      (IncomingExcess.view_label_bounds view H ranks _ endpoints.1).1
  refine ⟨Finset.sum_nonneg (fun edge _ => weight_nonneg metric _ rank initial record block edge), ?_, ?_,
    amount_departure metric rank initial record owner tree projection localOwners block⟩
  · cases metric with
    | nonrootWinner =>
        exact (nonroot_le_full rank initial record owner tree block).trans (first_bound view owner projection localOwners block member H ranks)
    | rootLoser =>
        apply amount_le_capacity .rootLoser rank initial record owner tree block H 4 bounded
        apply winner_capacity (rank ∘ record) owner tree projection localOwners _ (Finset.filter_subset _ _) (treeOwner owner tree)
        intro edge edgeMem
        exact (weight_selected .rootLoser _ rank initial record block edge (Finset.mem_filter.mp edgeMem).2).2.2
  · intro small
    cases metric with
    | nonrootWinner =>
        apply amount_le_capacity .nonrootWinner rank initial record owner tree block H 4 bounded
        apply small_winner_capacity rank record owner tree projection localOwners injective block small _ (Finset.filter_subset _ _)
        intro edge edgeMem
        exact List.mem_toFinset.mpr (weight_selected .nonrootWinner _ rank initial record block edge (Finset.mem_filter.mp edgeMem).2).1
    | rootLoser =>
        have bound := amount_le_capacity .rootLoser rank initial record owner tree block H 1 bounded ?_
        · simpa only [Nat.cast_one, one_mul, range] using bound
        · apply small_loser_capacity rank record owner tree projection localOwners injective block small _ (Finset.filter_subset _ _)
          intro edge edgeMem
          exact List.mem_toFinset.mpr (weight_selected .rootLoser _ rank initial record block edge (Finset.mem_filter.mp edgeMem).2).1

end Greedy.OutgoingExcess
