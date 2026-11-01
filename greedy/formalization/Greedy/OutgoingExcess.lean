import Greedy.DepartureAccess

/-! Positive boundary excess across the endpoints of a winning source instance. -/

namespace Greedy.OutgoingExcess

open Splay.Tree Splay.Analysis GreedyMerge.OrderedBlocks GreedyMerge.Primitives
open GreedyMerge.ActualBlockPartition GreedyMerge.Fringe GreedyMerge.Fringe.Schedule
open GreedyMerge.AccessSourceAccounting GreedyForest.Phase
open scoped BigOperators

def extra (rank : ℕ → ℕ) (initial : ℕ → ℤ) (record : ℕ → ℕ) (edge : ℕ × ℕ) : ℤ :=
  max 0 (DepartureCells.newLabel rank record edge - initial (record edge.1))

noncomputable def fullWeight (rank : ℕ → ℕ) (initial : ℕ → ℤ) (record : ℕ → ℕ)
    (block : Frozen) (edge : ℕ × ℕ) : ℤ :=
  if record edge.1 ∈ blockKeys block ∧ record edge.2 ∉ blockKeys block then extra rank initial record edge else 0

noncomputable def fullAmount {lo hi : ℕ} (rank : ℕ → ℕ) (initial : ℕ → ℤ) (record owner : ℕ → ℕ)
    (tree : BST lo hi) (block : Frozen) : ℤ :=
  ∑ edge ∈ (schedule owner tree).toFinset, fullWeight rank initial record block edge

theorem extra_nonneg (rank : ℕ → ℕ) (initial : ℕ → ℤ) (record : ℕ → ℕ) (edge : ℕ × ℕ) :
    0 ≤ extra rank initial record edge := le_max_left _ _

theorem extra_bound (rank : ℕ → ℕ) (initial : ℕ → ℤ) (record : ℕ → ℕ) (edge : ℕ × ℕ)
    (H : ℕ) (height : rank (record edge.2) ≤ H) (lower : 1 ≤ initial (record edge.1)) :
    extra rank initial record edge ≤ (contractedGap H : ℤ)-1 := by
  have upper : DepartureCells.newLabel rank record edge ≤ (contractedGap H : ℤ) := by
    change (contractedGap (rank (record edge.2) - rank (record edge.1)) : ℤ) ≤ _
    exact_mod_cast contractedGap_mono ((Nat.sub_le (rank (record edge.2)) (rank (record edge.1))).trans height)
  have positive : 1 ≤ (contractedGap H : ℤ) := by unfold contractedGap; omega
  unfold extra
  omega

theorem fullWeight_matches {lo hi : ℕ} {rank : ℕ → ℕ} {initial : ℕ → ℤ} {record : ℕ → ℕ}
    {tree : BST lo hi} {state : SideState} (view : SideView rank initial record tree state)
    (block : Frozen) (member : block ∈ state.shrinking) (edge : ℕ × ℕ)
    (first : edge.1 ∈ atoms tree) (second : edge.2 ∈ atoms tree) :
    fullWeight rank initial record block edge =
      if PositiveBoundary.Outgoing (view.partition.first block.id) (view.partition.finish block.id) edge then
        PositiveBoundary.extra (rank ∘ record) (view.partition.base block.id) edge else 0 := by
  have matching (key : ℕ) (keyMem : key ∈ atoms tree) :
      record key ∈ blockKeys block ↔ view.partition.first block.id ≤ key ∧ key < view.partition.finish block.id := by
    have bounds := (atoms_mem_iff tree key).mp keyMem
    exact (view.matching key bounds.1 bounds.2 block member).symm.trans (view.partition.intervalExact key bounds.1 bounds.2 block.id)
  by_cases outgoing : record edge.1 ∈ blockKeys block ∧ record edge.2 ∉ blockKeys block
  · have condition : PositiveBoundary.Outgoing (view.partition.first block.id) (view.partition.finish block.id) edge :=
      ⟨((matching _ first).mp outgoing.1).1, ((matching _ first).mp outgoing.1).2, mt (matching _ second).mpr outgoing.2⟩
    have label := view.partition.interval_bucket block.id edge.1 condition.1 condition.2.1
    simp only [fullWeight, if_pos outgoing, if_pos condition, extra, PositiveBoundary.extra, DepartureCells.newLabel]
    rw [show initial (record edge.1) = _ from label]
    rfl
  · have condition : ¬PositiveBoundary.Outgoing (view.partition.first block.id) (view.partition.finish block.id) edge := by
      intro inside
      exact outgoing ⟨(matching _ first).mpr ⟨inside.1, inside.2.1⟩, mt (matching _ second).mp inside.2.2⟩
    simp only [fullWeight, if_neg outgoing, if_neg condition]

theorem first_bound {lo hi : ℕ} {rank : ℕ → ℕ} {initial : ℕ → ℤ} {record : ℕ → ℕ}
    {tree : BST lo hi} {state : SideState} (view : SideView rank initial record tree state)
    (owner : ℕ → ℕ) (projection : Projection (rank ∘ record) owner tree)
    (localOwners : LocalOwners (rank ∘ record) owner lo hi) (block : Frozen) (member : block ∈ state.shrinking)
    (H : ℕ) (ranks : ∀ key, 2*lo ≤ key → key ≤ 2*hi → rank (record key) ≤ H) :
    fullAmount rank initial record owner tree block ≤ 4*((contractedGap H : ℤ)-1) := by
  have edgeSet : (schedule owner tree).toFinset = (edges owner tree).toFinset := by
    ext edge
    simp only [List.mem_toFinset]
    exact (schedule_perm_edges (rank ∘ record) owner tree projection localOwners).mem_iff
  have same : fullAmount rank initial record owner tree block =
      ∑ edge ∈ (edges owner tree).toFinset.filter (PositiveBoundary.Outgoing (view.partition.first block.id) (view.partition.finish block.id)),
        PositiveBoundary.extra (rank ∘ record) (view.partition.base block.id) edge := by
    unfold fullAmount
    rw [edgeSet, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro edge edgeMem
    have bounds := edge_strict_rank_and_bounds (rank ∘ record) owner tree edge.1 edge.2 projection (List.mem_toFinset.mp edgeMem)
    exact fullWeight_matches view block member edge
      ((atoms_mem_iff tree edge.1).mpr ⟨bounds.1, bounds.2.1⟩)
      ((atoms_mem_iff tree edge.2).mpr ⟨bounds.2.2.1, bounds.2.2.2.1⟩)
  rw [same]
  exact SourceWeights.partition_positive_bound (rank ∘ record) owner (initial ∘ record) tree projection localOwners view.partition block.id H ranks

end Greedy.OutgoingExcess
