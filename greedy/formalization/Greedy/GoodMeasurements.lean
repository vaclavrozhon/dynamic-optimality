import Greedy.AccessMeasurements

/-! Every equal-label internal link pays one unit from its actual loser drop. -/

namespace Greedy.AccessJournal

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Analysis
open GreedyMerge.ActualLinks GreedyMerge.PathPlateau GreedyMerge.OrderedBlocks GreedyMerge.Primitives
open GreedyMerge.Fringe.Schedule
open EntryJournal GreedyForest.Phase
open scoped BigOperators

theorem equal_internal_drop {n access : ℕ} {comparator oldTree newTree : BST 0 n}
    {p : Decomposition oldTree access} (data : AccessScheduleData comparator oldTree newTree p)
    (source : External n) (geometry : AccessTrace.Geometry data source) (states : States n)
    (ready : Ready comparator oldTree states) (K : ℤ) (event : External n × External n)
    (member : event ∈ data.events) (same : AccessTrace.SameBlock states source event)
    (equal : GreedyMerge.StateLabels.label comparator.externalDepth K states event.1.val =
      GreedyMerge.StateLabels.label comparator.externalDepth K states event.2.val) :
    (contractedGap (comparator.externalDepth event.2.val - comparator.externalDepth event.1.val) : ℤ) + 1 ≤
      GreedyMerge.StateLabels.label comparator.externalDepth K states event.2.val := by
  obtain ⟨side, block, blockMem, winner, winnerMem, loser, loserMem, winnerKey, loserKey⟩ := same
  have first := GreedyMerge.StateLabels.label_of_frozen (Snapshot.ofTree comparator) oldTree comparator.externalDepth K states
    ready.valid ready.sound source side block blockMem winner winnerMem
  have second := GreedyMerge.StateLabels.label_of_frozen (Snapshot.ofTree comparator) oldTree comparator.externalDepth K states
    ready.valid ready.sound source side block blockMem loser loserMem
  rw [winnerKey] at first
  rw [loserKey] at second
  have floor := (ready.bases source side block blockMem).2 winner winnerMem
  rw [winnerKey] at floor
  have strict := GreedyMerge.MappedConsolidation.run_event_rank_lt geometry.run (eventKeys event) (List.mem_map.mpr ⟨event, member, rfl⟩)
  have gap := internalPairingGap_of_ranks (ownerRank := block.base) (intervalGap := 0) floor strict
  have buckets : contractedGap (comparator.externalDepth event.1.val - block.base) =
      contractedGap (comparator.externalDepth event.2.val - block.base) := by
    have sameLabel := first.symm.trans (equal.trans second)
    exact_mod_cast sameLabel
  have drop := gap.2 buckets
  rw [second]
  exact_mod_cast drop

end Greedy.AccessJournal

namespace Greedy.RunJournal

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Analysis
open GreedyMerge.ActualLinks GreedyMerge.PathPlateau EntryJournal RestorationJournal
open scoped BigOperators

theorem access_good_bound {n : ℕ} (before : Execution.State n) (request : Fin n) (K : ℤ)
    (root : before.comparator.HasRoot request.val)
    (decomposition : Decomposition before.refined.tree request.val)
    (data : AccessScheduleData before.comparator before.refined.tree (Execution.afterRefinement before request).tree decomposition)
    (valid : before.Valid) (state : WeightedMemory.State (External n))
    (agree : state.label = labels before.comparator K before.blocks) :
    total good state (access before request decomposition data) ≤ total negativeChange state (access before request decomposition data) := by
  classical
  let initial := GreedyMerge.StateLabels.label before.comparator.externalDepth K (prepared before request)
  have agrees : ∀ record, state.label record = initial record.val := by
    intro record
    rw [agree, ← prepared_labels before request K]
    rfl
  have geometry := AccessTrace.geometry data (Execution.source request) rfl (Execution.root_minimum _ request root)
  change total good state (AccessJournal.program _ _ _) ≤ total negativeChange state (AccessJournal.program _ _ _)
  rw [AccessJournal.program_indexed_total,
    AccessJournal.program_negative_sum data (Execution.source request) geometry _ initial state agrees]
  apply Finset.sum_le_sum
  intro i _
  have snapshots := AccessJournal.source_snapshots data (Execution.source request) geometry
    (AccessTrace.kind (prepared before request) (Execution.source request)) initial state agrees i
  by_cases same : AccessTrace.SameBlock (prepared before request) (Execution.source request) (data.events.get i)
  · simp only [AccessJournal.pairWeight, AccessTrace.kind, if_pos same, good, add_zero]
    rw [snapshots.1, snapshots.2]
    by_cases equal : initial (data.events.get i).2.val = initial (data.events.get i).1.val
    · rw [if_pos equal]
      have drop := AccessJournal.equal_internal_drop data (Execution.source request) geometry (prepared before request)
        (CreatorPhase.prepared_ready before request valid) K (data.events.get i) (List.get_mem _ i) same equal.symm
      change _ + 1 ≤ initial _ at drop
      omega
    · rw [if_neg equal]
      exact le_max_left _ _
  · simp only [AccessJournal.pairWeight, AccessTrace.kind, if_neg same, good, zero_add]
    exact le_max_left _ _

end Greedy.RunJournal
