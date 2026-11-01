import Greedy.SignedPhase
import Greedy.NegativeBoundary
import StoredSourceHistory

/-!
# Weighted estimates for the actual source partition

The source partition is the one extracted from the concrete block state
by `AccessSourceAccounting`. Its interval, base, and label equations
discharge the inputs of the weighted geometric lemmas. The signed
creator estimate also reads join times from the literal stored entries.
-/

namespace Greedy.SourceWeights

open Splay.Tree GreedyMerge.Fringe GreedyMerge.Fringe.Schedule
open GreedyForest.Phase GreedyForest.ActiveTree Splay.Analysis
open GreedyMerge.AccessSourceAccounting GreedyMerge.Primitives GreedyMerge.OrderedBlocks
open Greedy.SignedPhase Greedy.SignedLifetime
open scoped BigOperators

def closedFirst (first finish : ℕ) : ℕ := if finish = 0 then 1 else first

theorem interval_closed (first finish key : ℕ) :
    first ≤ key ∧ key < finish ↔ closedFirst first finish ≤ key ∧ key ≤ finish - 1 := by
  unfold closedFirst
  split_ifs <;> omega

theorem partition_signed_geometry {lo hi : ℕ} (rank owner : ℕ → ℕ) (initial : ℕ → ℤ)
    (tree : BST lo hi) (projection : Projection rank owner tree)
    (localOwners : LocalOwners rank owner lo hi) (partition : SourcePartition rank initial lo hi)
    (join : ℕ → ℕ) (block time : ℕ)
    (ordered :
      (∀ a ∈ blockMembers tree partition.block block, ∀ b ∈ blockMembers tree partition.block block,
        a ≤ b → join a ≤ join b) ∨
      (∀ a ∈ blockMembers tree partition.block block, ∀ b ∈ blockMembers tree partition.block block,
        a ≤ b → join b ≤ join a)) :
    Nonempty (PhaseGeometry (∑ edge ∈ (schedule owner tree).toFinset,
      historyWeight (blockMembers tree partition.block block) join time edge)) := by
  apply schedule_geometry rank owner tree projection localOwners _ join time
    (closedFirst (partition.first block) (partition.finish block)) (partition.finish block - 1)
    ?_ ordered
  intro edge member
  have bounds := edge_strict_rank_and_bounds rank owner tree edge.1 edge.2 projection
    (List.mem_toFinset.mp member)
  have inBlock : ∀ key, 2*lo ≤ key → key ≤ 2*hi →
      (key ∈ blockMembers tree partition.block block ↔
        closedFirst (partition.first block) (partition.finish block) ≤ key ∧
        key ≤ partition.finish block - 1) := by
    intro key lower upper
    have atom := (atoms_mem_iff tree key).mpr ⟨lower, upper⟩
    simp only [blockMembers, Finset.mem_filter, List.mem_toFinset, atom, true_and]
    exact (partition.intervalExact key lower upper block).trans (interval_closed _ _ _)
  exact ⟨inBlock edge.1 bounds.1 bounds.2.1, inBlock edge.2 bounds.2.2.1 bounds.2.2.2.1⟩

theorem stored_signed_geometry {lo hi : ℕ} {rank : ℕ → ℕ} {initial : ℕ → ℤ} {record : ℕ → ℕ}
    {tree : BST lo hi} {state : SideState} (view : SideView rank initial record tree state)
    (source : ℕ) (side : Bool) (valid : Valid source side state)
    (recordMono : ∀ first ∈ atoms tree, ∀ second ∈ atoms tree,
      first ≤ second → record first ≤ record second)
    (owner : ℕ → ℕ) (projection : Projection (rank ∘ record) owner tree)
    (localOwners : LocalOwners (rank ∘ record) owner lo hi)
    (block : Frozen) (blockMem : block ∈ state.shrinking)
    (history : ∃ orientation, HistMonotone orientation block.members) (time : ℕ) :
    Nonempty (PhaseGeometry (∑ edge ∈ (schedule owner tree).toFinset,
      historyWeight (blockMembers tree view.partition.block block.id)
        (storedJoin state ∘ record) time edge)) :=
  partition_signed_geometry _ owner _ tree projection localOwners view.partition
    (storedJoin state ∘ record) block.id time
    (view.storedJoin_order source side valid recordMono block blockMem history)

theorem partition_positive_bound {lo hi : ℕ} (rank owner : ℕ → ℕ) (initial : ℕ → ℤ)
    (tree : BST lo hi) (projection : Projection rank owner tree)
    (localOwners : LocalOwners rank owner lo hi) (partition : SourcePartition rank initial lo hi)
    (block H : ℕ) (ranks : ∀ key, 2*lo ≤ key → key ≤ 2*hi → rank key ≤ H) :
    (∑ edge ∈ (edges owner tree).toFinset.filter
      (Greedy.PositiveBoundary.Outgoing (partition.first block) (partition.finish block)),
      Greedy.PositiveBoundary.extra rank (partition.base block) edge) ≤
      4 * ((contractedGap H : ℤ) - 1) :=
  Greedy.PositiveBoundary.fringe_first_phase rank owner tree _ _ _ H projection localOwners
    (partition.interval_floor block) ranks

theorem partition_negative_bound {lo hi : ℕ} (rank owner : ℕ → ℕ) (initial : ℕ → ℤ)
    (tree : BST lo hi) (projection : Projection rank owner tree)
    (localOwners : LocalOwners rank owner lo hi) (partition : SourcePartition rank initial lo hi)
    (block H : ℕ) (ranks : ∀ key, 2*lo ≤ key → key ≤ 2*hi → rank key ≤ H) :
    (∑ edge ∈ (edges owner tree).toFinset,
      Greedy.NegativeBoundary.excess rank initial
        (Greedy.NegativeBoundary.parentRanks rank (-1) (active owner tree).tree)
        (partition.first block) (partition.finish block) edge) ≤
      3 * ((contractedGap H : ℤ) - 1) := by
  apply Greedy.NegativeBoundary.fringe_excess_bound rank owner initial tree
    _ _ (partition.base block) (contractedGap H) projection localOwners
  · simp only [contractedGap]; omega
  · intro key lower upper
    rw [partition.initialBucket key lower upper]
    exact baseLabel_bounds rank _ H key (ranks key lower upper)
  · intro key _ _ inside
    exact partition.interval_floor block key inside.1 inside.2
  · intro key _ _ inside
    exact partition.interval_bucket block key inside.1 inside.2

end Greedy.SourceWeights
