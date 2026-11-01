import Greedy.SourceWeights
import Greedy.InstanceDeletion
import Greedy.WinnerPhase

/-! Negative boundary excess, charged to its literal losing instance. -/

namespace Greedy.IncomingExcess

open Splay.Tree Splay.Analysis GreedyMerge.OrderedBlocks GreedyMerge.Primitives
open GreedyMerge.Fringe GreedyMerge.Fringe.Schedule GreedyMerge.AccessSourceAccounting
open GreedyMerge.ActualBlockPartition
open GreedyForest.Phase GreedyForest.ActiveTree
open scoped BigOperators

noncomputable def weight (rank : ℕ → ℕ) (initial : ℕ → ℤ) (record : ℕ → ℕ)
    (parents : ℕ → ℤ) (block : Frozen) (edge : ℕ × ℕ) : ℤ :=
  if record edge.1 ∉ blockKeys block ∧ record edge.2 ∈ blockKeys block then
    max 0 (max 0 (initial (record edge.1) - initial (record edge.2)) -
      NegativeBoundary.winnerDrop (rank ∘ record) (initial ∘ record) parents edge.1)
  else 0

noncomputable def amount {lo hi : ℕ} (rank : ℕ → ℕ) (initial : ℕ → ℤ) (record owner : ℕ → ℕ)
    (tree : BST lo hi) (block : Frozen) : ℤ :=
  ∑ edge ∈ (schedule owner tree).toFinset,
    weight rank initial record (NegativeBoundary.parentRanks (rank ∘ record) (-1) (active owner tree).tree) block edge

theorem weight_nonneg (rank : ℕ → ℕ) (initial : ℕ → ℤ) (record : ℕ → ℕ)
    (parents : ℕ → ℤ) (block : Frozen) (edge : ℕ × ℕ) : 0 ≤ weight rank initial record parents block edge := by
  unfold weight
  split_ifs
  · exact le_max_left _ _
  · exact le_rfl

theorem weight_loser (rank : ℕ → ℕ) (initial : ℕ → ℤ) (record : ℕ → ℕ)
    (parents : ℕ → ℤ) (block : Frozen) (edge : ℕ × ℕ)
    (nonzero : weight rank initial record parents block edge ≠ 0) : record edge.2 ∈ ClosedInstances.keys block := by
  unfold weight at nonzero
  split_ifs at nonzero with incoming
  · exact List.mem_toFinset.mpr incoming.2
  · exact False.elim (nonzero rfl)

theorem weight_le_range (rank : ℕ → ℕ) (initial : ℕ → ℤ) (record : ℕ → ℕ)
    (parents : ℕ → ℤ) (block : Frozen) (edge : ℕ × ℕ) (K : ℤ)
    (range : 1 ≤ K) (winner : initial (record edge.1) ≤ K) (loser : 1 ≤ initial (record edge.2)) :
    weight rank initial record parents block edge ≤ K-1 := by
  have nonneg := NegativeBoundary.winnerDrop_nonneg (rank ∘ record) (initial ∘ record) parents edge.1
  unfold weight
  split_ifs <;> omega

theorem amount_nonneg {lo hi : ℕ} (rank : ℕ → ℕ) (initial : ℕ → ℤ) (record owner : ℕ → ℕ)
    (tree : BST lo hi) (block : Frozen) : 0 ≤ amount rank initial record owner tree block :=
  Finset.sum_nonneg fun edge _ => weight_nonneg rank initial record _ block edge

theorem amount_loser {lo hi : ℕ} (rank : ℕ → ℕ) (initial : ℕ → ℤ) (record owner : ℕ → ℕ)
    (tree : BST lo hi) (block : Frozen) (nonzero : amount rank initial record owner tree block ≠ 0) :
    ∃ edge ∈ schedule owner tree, record edge.2 ∈ ClosedInstances.keys block := by
  obtain ⟨edge, member, contributes⟩ := Finset.exists_ne_zero_of_sum_ne_zero nonzero
  exact ⟨edge, List.mem_toFinset.mp member, weight_loser rank initial record _ block edge contributes⟩

theorem weight_matches {lo hi : ℕ} {rank : ℕ → ℕ} {initial : ℕ → ℤ} {record : ℕ → ℕ}
    {tree : BST lo hi} {state : SideState} (view : SideView rank initial record tree state)
    (block : Frozen) (member : block ∈ state.shrinking) (parents : ℕ → ℤ) (edge : ℕ × ℕ)
    (first : edge.1 ∈ atoms tree) (second : edge.2 ∈ atoms tree) :
    weight rank initial record parents block edge = NegativeBoundary.excess (rank ∘ record) (initial ∘ record) parents
      (view.partition.first block.id) (view.partition.finish block.id) edge := by
  have matching (key : ℕ) (keyMem : key ∈ atoms tree) :
      record key ∈ blockKeys block ↔ Greedy.NegativeBoundaryGeometry.Inside (view.partition.first block.id) (view.partition.finish block.id) key := by
    have bounds := (atoms_mem_iff tree key).mp keyMem
    exact (view.matching key bounds.1 bounds.2 block member).symm.trans (view.partition.intervalExact key bounds.1 bounds.2 block.id)
  simp only [weight, NegativeBoundary.excess, NegativeBoundary.Incoming, matching _ first, matching _ second, Function.comp_apply]

theorem first_bound {lo hi : ℕ} {rank : ℕ → ℕ} {initial : ℕ → ℤ} {record : ℕ → ℕ}
    {tree : BST lo hi} {state : SideState} (view : SideView rank initial record tree state)
    (owner : ℕ → ℕ) (projection : Projection (rank ∘ record) owner tree)
    (localOwners : LocalOwners (rank ∘ record) owner lo hi) (block : Frozen) (member : block ∈ state.shrinking)
    (H : ℕ) (ranks : ∀ key, 2*lo ≤ key → key ≤ 2*hi → rank (record key) ≤ H) :
    amount rank initial record owner tree block ≤ 3*((contractedGap H : ℤ)-1) := by
  have same : amount rank initial record owner tree block =
      ∑ edge ∈ (edges owner tree).toFinset,
        NegativeBoundary.excess (rank ∘ record) (initial ∘ record)
          (NegativeBoundary.parentRanks (rank ∘ record) (-1) (active owner tree).tree)
          (view.partition.first block.id) (view.partition.finish block.id) edge := by
    unfold amount
    have same : (schedule owner tree).toFinset = (edges owner tree).toFinset := by
      ext edge
      simp only [List.mem_toFinset]
      exact (schedule_perm_edges (rank ∘ record) owner tree projection localOwners).mem_iff
    rw [same]
    apply Finset.sum_congr rfl
    intro edge edgeMem
    have bounds := edge_strict_rank_and_bounds (rank ∘ record) owner tree edge.1 edge.2 projection (List.mem_toFinset.mp edgeMem)
    exact weight_matches view block member _ edge
      ((atoms_mem_iff tree edge.1).mpr ⟨bounds.1, bounds.2.1⟩)
      ((atoms_mem_iff tree edge.2).mpr ⟨bounds.2.2.1, bounds.2.2.2.1⟩)
  rw [same]
  exact SourceWeights.partition_negative_bound (rank ∘ record) owner (initial ∘ record) tree projection localOwners view.partition block.id H ranks

theorem small_bound {lo hi : ℕ} (rank : ℕ → ℕ) (initial : ℕ → ℤ) (record owner : ℕ → ℕ)
    (tree : BST lo hi) (projection : Projection (rank ∘ record) owner tree)
    (localOwners : LocalOwners (rank ∘ record) owner lo hi)
    (injective : Set.InjOn record {key | key ∈ atoms tree})
    (block : Frozen) (small : ClosedInstances.Small block) (K : ℤ) (range : 1 ≤ K)
    (bounds : ∀ key ∈ atoms tree, 1 ≤ initial (record key) ∧ initial (record key) ≤ K) :
    amount rank initial record owner tree block ≤ K-1 := by
  classical
  let events := (schedule owner tree).toFinset
  let charge := weight rank initial record (NegativeBoundary.parentRanks (rank ∘ record) (-1) (active owner tree).tree) block
  let support := events.filter (fun edge => charge edge ≠ 0)
  have run := schedule_run (rank ∘ record) owner tree projection localOwners
  have unique := run_losers_nodup run (atoms_nodup tree)
  have injection : Set.InjOn (fun edge : ℕ × ℕ => record edge.2) {edge | edge ∈ support} := by
    intro first firstMem second secondMem equal
    have firstEvent := List.mem_toFinset.mp (Finset.mem_filter.mp firstMem).1
    have secondEvent := List.mem_toFinset.mp (Finset.mem_filter.mp secondMem).1
    exact List.inj_on_of_nodup_map unique firstEvent secondEvent
      (injective (run.event_members first firstEvent).2 (run.event_members second secondEvent).2 equal)
  have capacity : support.card ≤ 1 := by
    have subset : support.image (fun edge => record edge.2) ⊆ ClosedInstances.keys block := by
      intro key member
      obtain ⟨edge, edgeMem, rfl⟩ := Finset.mem_image.mp member
      exact weight_loser rank initial record _ block edge (Finset.mem_filter.mp edgeMem).2
    have size := Finset.card_le_card subset
    rw [Finset.card_image_of_injOn injection] at size
    exact size.trans small
  have restricted : amount rank initial record owner tree block = ∑ edge ∈ support, charge edge := by
    change (∑ edge ∈ events, charge edge) = _
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro edge _
    by_cases zero : charge edge = 0 <;> simp [zero]
  rw [restricted]
  calc
    _ ≤ ∑ _edge ∈ support, (K-1) := by
      apply Finset.sum_le_sum
      intro edge member
      have endpoint := run.event_members edge (List.mem_toFinset.mp (Finset.mem_filter.mp member).1)
      exact weight_le_range rank initial record _ block edge K range (bounds edge.1 endpoint.1).2 (bounds edge.2 endpoint.2).1
    _ = (support.card : ℤ) * (K-1) := by simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ K-1 := by
      have size : (support.card : ℤ) ≤ 1 := by exact_mod_cast capacity
      nlinarith

end Greedy.IncomingExcess
