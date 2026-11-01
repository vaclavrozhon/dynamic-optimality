import Greedy.OutgoingAccess
import Greedy.NegativeSide

/-! The two positive-excess destinations partition every actual boundary edge. -/

namespace Greedy.SourceCensus

open Splay.Tree Splay.Tree.BST Splay.Rank
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.ActualBlockPartition
open GreedyMerge.HeapAllocation GreedyMerge.ActualLinks
open GreedyMerge.Fringe GreedyMerge.Fringe.Schedule GreedyMerge.AccessSourceAccounting
open GreedyForest.Phase
open scoped BigOperators

noncomputable local instance : DecidableEq Frozen := Classical.decEq _
attribute [local instance] Classical.propDecidable

theorem sameBlockKeys_symm {n : ℕ} (states : HeapSides n) (source : External n) (first second : ℕ) :
    SameBlockKeys states source (first, second) ↔ SameBlockKeys states source (second, first) := by
  constructor <;> rintro ⟨side, block, member, firstMem, secondMem⟩ <;> exact ⟨side, block, member, secondMem, firstMem⟩

noncomputable def positiveWeight {n : ℕ} (states : HeapSides n) (source : External n)
    (initial : ℕ → ℤ) (record : ℕ → ℕ) (edge : ℕ × ℕ) : ℤ :=
  if SameBlockKeys states source (record edge.1, record edge.2) then 0
  else max 0 (initial (record edge.2) - initial (record edge.1))

theorem outgoing_source_sum {n lo hi : ℕ} {rank : ℕ → ℕ} {initial : ℕ → ℤ} {record : ℕ → ℕ}
    {tree : BST lo hi} (states : HeapSides n) (source : External n) (side : Bool)
    (valid : ∀ direction, Valid source.val direction (states source direction))
    (view : SideView rank initial record tree (states source side))
    (ids : ((states source side).shrinking.map Frozen.id).Nodup)
    (owner : ℕ → ℕ) (projection : Projection (rank ∘ record) owner tree)
    (localOwners : LocalOwners (rank ∘ record) owner lo hi) :
    (∑ block ∈ (states source side).shrinking.toFinset, OutgoingExcess.amount .nonrootWinner rank initial record owner tree block) +
      (∑ block ∈ (states source side).shrinking.toFinset, OutgoingExcess.amount .rootLoser rank initial record owner tree block) =
      ∑ edge ∈ (schedule owner tree).toFinset,
        if SameBlockKeys states source (record edge.1, record edge.2) then 0 else OutgoingExcess.extra rank initial record edge := by
  classical
  unfold OutgoingExcess.amount
  rw [Finset.sum_comm, Finset.sum_comm (s := (states source side).shrinking.toFinset), ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro edge edgeMem
  have endpoints := (schedule_run (rank ∘ record) owner tree projection localOwners).event_members edge (List.mem_toFinset.mp edgeMem)
  by_cases root : edge.1 = treeOwner owner tree
  · simp only [OutgoingExcess.weight, OutgoingExcess.Selected, root, ne_eq, not_true_eq_false,
      and_false, and_true, if_false, Finset.sum_const_zero, zero_add]
    simpa only [root] using sum_boundary_value states source side valid view ids edge.2 endpoints.2
      (record edge.1) (OutgoingExcess.extra rank initial record edge)
  · simp only [OutgoingExcess.weight, OutgoingExcess.Selected, ne_eq, root, not_false_eq_true,
      and_true, and_false, if_false, Finset.sum_const_zero, add_zero]
    have bound := sum_boundary_value states source side valid view ids edge.1 endpoints.1
      (record edge.2) (OutgoingExcess.extra rank initial record edge)
    rw [sameBlockKeys_symm states source (record edge.2) (record edge.1)] at bound
    exact bound

theorem positive_side_bound {n lo hi : ℕ} {rank : ℕ → ℕ} {initial : ℕ → ℤ} {record : ℕ → ℕ}
    {tree : BST lo hi} (states : HeapSides n) (source : External n) (side : Bool)
    (valid : ∀ direction, Valid source.val direction (states source direction))
    (view : SideView rank initial record tree (states source side))
    (ids : ((states source side).shrinking.map Frozen.id).Nodup)
    (owner : ℕ → ℕ) (projection : Projection (rank ∘ record) owner tree)
    (localOwners : LocalOwners (rank ∘ record) owner lo hi) :
    (∑ i : Fin (schedule owner tree).length, positiveWeight states source initial record ((schedule owner tree).get i)) ≤
      (∑ i : Fin (schedule owner tree).length, PhaseDrops.edgeDrop (rank ∘ record) (initial ∘ record) ((schedule owner tree).get i)) +
      (∑ block ∈ (states source side).shrinking.toFinset, OutgoingExcess.amount .nonrootWinner rank initial record owner tree block) +
      (∑ block ∈ (states source side).shrinking.toFinset, OutgoingExcess.amount .rootLoser rank initial record owner tree block) := by
  classical
  have unique := run_events_nodup (schedule_run (rank ∘ record) owner tree projection localOwners) (atoms_nodup tree)
  rw [AtomicAccess.indexed_toFinset _ unique, AtomicAccess.indexed_toFinset _ unique, add_assoc,
    outgoing_source_sum states source side valid view ids owner projection localOwners, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro edge _
  have split := PositiveBoundary.entry_split (initial (record edge.2)) (initial (record edge.1)) (DepartureCells.newLabel rank record edge)
  unfold positiveWeight
  by_cases internal : SameBlockKeys states source (record edge.1, record edge.2)
  · simp only [if_pos internal, add_zero, PhaseDrops.edgeDrop]
    exact le_max_left _ _
  · simp only [if_neg internal]
    exact split

end Greedy.SourceCensus
