import Greedy.SourceClasses
import Greedy.AtomicSums
import Greedy.PhaseDrops

/-! Negative boundary differences on one side use actual future loser drops. -/

namespace Greedy.SourceCensus

open Splay.Tree Splay.Tree.BST Splay.Rank
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.ActualBlockPartition
open GreedyMerge.HeapAllocation GreedyMerge.ActualLinks
open GreedyMerge.Fringe GreedyMerge.Fringe.Schedule GreedyMerge.AccessSourceAccounting
open GreedyForest.Phase GreedyForest.ActiveTree
open scoped BigOperators

noncomputable local instance : DecidableEq Frozen := Classical.decEq _
attribute [local instance] Classical.propDecidable

noncomputable def negativeWeight {n : ℕ} (states : HeapSides n) (source : External n)
    (initial : ℕ → ℤ) (record : ℕ → ℕ) (edge : ℕ × ℕ) : ℤ :=
  if SameBlockKeys states source (record edge.1, record edge.2) then 0
  else max 0 (initial (record edge.1) - initial (record edge.2))

theorem incoming_source_sum {n lo hi : ℕ} {rank : ℕ → ℕ} {initial : ℕ → ℤ} {record : ℕ → ℕ}
    {tree : BST lo hi} (states : HeapSides n) (source : External n) (side : Bool)
    (valid : ∀ direction, Valid source.val direction (states source direction))
    (view : SideView rank initial record tree (states source side))
    (ids : ((states source side).shrinking.map Frozen.id).Nodup)
    (owner : ℕ → ℕ) (projection : Projection (rank ∘ record) owner tree)
    (localOwners : LocalOwners (rank ∘ record) owner lo hi) :
    (∑ block ∈ (states source side).shrinking.toFinset, IncomingExcess.amount rank initial record owner tree block) =
      ∑ edge ∈ (schedule owner tree).toFinset,
        if SameBlockKeys states source (record edge.1, record edge.2) then 0 else
          max 0 (max 0 (initial (record edge.1) - initial (record edge.2)) -
            NegativeBoundary.winnerDrop (rank ∘ record) (initial ∘ record)
              (NegativeBoundary.parentRanks (rank ∘ record) (-1) (active owner tree).tree) edge.1) := by
  classical
  simp only [IncomingExcess.amount]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro edge edgeMem
  have member := (schedule_run (rank ∘ record) owner tree projection localOwners).event_members edge (List.mem_toFinset.mp edgeMem)
  simpa only [IncomingExcess.weight, and_comm] using sum_boundary_value states source side valid view ids _ member.2
    (record edge.1) (max 0 (max 0 (initial (record edge.1) - initial (record edge.2)) -
      NegativeBoundary.winnerDrop (rank ∘ record) (initial ∘ record)
        (NegativeBoundary.parentRanks (rank ∘ record) (-1) (active owner tree).tree) edge.1))

theorem negative_side_bound {n lo hi : ℕ} {rank : ℕ → ℕ} {initial : ℕ → ℤ} {record : ℕ → ℕ}
    {tree : BST lo hi} (states : HeapSides n) (source : External n) (side : Bool)
    (valid : ∀ direction, Valid source.val direction (states source direction))
    (view : SideView rank initial record tree (states source side))
    (ids : ((states source side).shrinking.map Frozen.id).Nodup)
    (owner : ℕ → ℕ) (projection : Projection (rank ∘ record) owner tree)
    (localOwners : LocalOwners (rank ∘ record) owner lo hi) :
    (∑ i : Fin (schedule owner tree).length, negativeWeight states source initial record ((schedule owner tree).get i)) ≤
      4*(∑ i : Fin (schedule owner tree).length, PhaseDrops.edgeDrop (rank ∘ record) (initial ∘ record) ((schedule owner tree).get i)) +
      ∑ block ∈ (states source side).shrinking.toFinset, IncomingExcess.amount rank initial record owner tree block := by
  classical
  have unique := run_events_nodup (schedule_run (rank ∘ record) owner tree projection localOwners) (atoms_nodup tree)
  rw [AtomicAccess.indexed_toFinset _ unique, AtomicAccess.indexed_toFinset _ unique]
  let parents := NegativeBoundary.parentRanks (rank ∘ record) (-1) (active owner tree).tree
  have dropBound := PhaseDrops.winner_charges_le_four_drops (rank ∘ record) owner (initial ∘ record) tree projection localOwners
  have edgeSet : (schedule owner tree).toFinset = (edges owner tree).toFinset := by
    ext edge
    simp only [List.mem_toFinset]
    exact (schedule_perm_edges (rank ∘ record) owner tree projection localOwners).mem_iff
  rw [← edgeSet] at dropBound
  have each : ∀ edge ∈ (schedule owner tree).toFinset,
      negativeWeight states source initial record edge ≤
        NegativeBoundary.winnerDrop (rank ∘ record) (initial ∘ record) parents edge.1 +
        (if SameBlockKeys states source (record edge.1, record edge.2) then 0 else
          max 0 (max 0 (initial (record edge.1) - initial (record edge.2)) -
            NegativeBoundary.winnerDrop (rank ∘ record) (initial ∘ record) parents edge.1)) := by
    intro edge _
    have nonneg := NegativeBoundary.winnerDrop_nonneg (rank ∘ record) (initial ∘ record) parents edge.1
    unfold negativeWeight
    split_ifs <;> omega
  have total := Finset.sum_le_sum each
  rw [Finset.sum_add_distrib] at total
  have excess := incoming_source_sum states source side valid view ids owner projection localOwners
  change _ = ∑ edge ∈ (schedule owner tree).toFinset,
    if SameBlockKeys states source (record edge.1, record edge.2) then 0 else
      max 0 (max 0 (initial (record edge.1) - initial (record edge.2)) -
        NegativeBoundary.winnerDrop (rank ∘ record) (initial ∘ record) parents edge.1) at excess
  rw [← excess] at total
  change (∑ edge ∈ (schedule owner tree).toFinset, NegativeBoundary.winnerDrop (rank ∘ record) (initial ∘ record) parents edge.1) ≤ _ at dropBound
  linarith

end Greedy.SourceCensus
