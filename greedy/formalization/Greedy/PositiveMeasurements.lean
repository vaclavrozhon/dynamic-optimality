import Greedy.PositiveSide
import Greedy.BoundaryMeasurements

/-! Positive boundary differences use one actual loser drop and thirteen ranges per instance. -/

namespace Greedy.RunJournal

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical Splay.Analysis
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.HeapAllocation
open GreedyMerge.ActualLinks GreedyMerge.PathPlateau GreedyMerge.PlateauBridge
open GreedyMerge.AccessSourceAccounting GreedyMerge.Fringe GreedyMerge.Fringe.Schedule
open EntryJournal RestorationJournal
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem positive_phase_bound {n : ℕ} (before : Execution.State n) (request : Fin n) (K : ℤ)
    (root : before.comparator.HasRoot request.val)
    (decomposition : Decomposition before.refined.tree request.val)
    (data : AccessScheduleData before.comparator before.refined.tree (Execution.afterRefinement before request).tree decomposition)
    (valid : before.Valid) :
    let initial := GreedyMerge.StateLabels.label before.comparator.externalDepth K (prepared before request)
    (∑ i : Fin data.events.length,
      SourceCensus.positiveWeight (prepared before request) (Execution.source request) initial id (eventKeys (data.events.get i))) ≤
      (∑ i : Fin data.events.length, PhaseDrops.edgeDrop before.comparator.externalDepth initial (eventKeys (data.events.get i))) +
      (∑ piece ∈ CreatorPhase.pieces (prepared before request) (Execution.source request),
        OutgoingExcess.charge .nonrootWinner K data (prepared before request) (Execution.source request) piece.1 piece.2) +
      (∑ piece ∈ CreatorPhase.pieces (prepared before request) (Execution.source request),
        OutgoingExcess.charge .rootLoser K data (prepared before request) (Execution.source request) piece.1 piece.2) := by
  have views := actual_allocated_sources before.comparator before.refined.tree _ decomposition data
    (Execution.source request) rfl (Execution.root_minimum _ request root) before.blocks valid.1 K before.next valid.2.2.1
  have converted := convertRoot_eq_convertHeap before.comparator.externalDepth (Execution.source request) before.next before.blocks
  change convertRoot before.comparator.externalDepth (Execution.source request) _ _ before.blocks = prepared before request at converted
  dsimp only at views
  rw [converted] at views
  obtain ⟨leftView⟩ := views.1
  obtain ⟨rightView⟩ := views.2
  have inventory := convertHeap_inventory before.comparator.externalDepth
    (fun owner _ => decide (owner = Execution.source request)) before.next before.blocks valid.2.2.1
  have ids (side : Bool) := inventory_shrinking_nodup (prepared before request) _ inventory (Execution.source request) side
  have ready := CreatorPhase.prepared_ready before request valid
  have upper := data.right.lower_le_upper
  have leftBound := SourceCensus.positive_side_bound (prepared before request) (Execution.source request) true (ready.valid _)
    leftView (ids true) data.owner data.projection.2.1 (fun q lower bound => data.localOwners q lower (by omega))
  have rightBound := SourceCensus.positive_side_bound (prepared before request) (Execution.source request) false (ready.valid _)
    rightView (ids false) data.owner data.projection.2.2 (fun q lower bound => data.localOwners q (by omega) bound)
  have geometry := AccessTrace.geometry data (Execution.source request) rfl (Execution.root_minimum _ request root)
  dsimp only
  rw [AtomicAccess.sum_two_sides data (Execution.source request) geometry
      (SourceCensus.positiveWeight (prepared before request) (Execution.source request)
        (GreedyMerge.StateLabels.label before.comparator.externalDepth K (prepared before request)) id),
    AtomicAccess.sum_two_sides data (Execution.source request) geometry
      (PhaseDrops.edgeDrop before.comparator.externalDepth (GreedyMerge.StateLabels.label before.comparator.externalDepth K (prepared before request))),
    SourceCensus.sum_pieces, SourceCensus.sum_pieces]
  simp only [OutgoingExcess.charge, if_true, Bool.false_eq_true, if_false]
  dsimp only [SourceCensus.positiveWeight, PhaseDrops.edgeDrop, Function.comp_apply, id_eq] at leftBound rightBound ⊢
  convert add_le_add leftBound rightBound using 1
  all_goals first | rfl | ring

theorem access_positive_entry_bound {n : ℕ} (before : Execution.State n) (request : Fin n) (K : ℤ)
    (root : before.comparator.HasRoot request.val)
    (decomposition : Decomposition before.refined.tree request.val)
    (data : AccessScheduleData before.comparator before.refined.tree (Execution.afterRefinement before request).tree decomposition)
    (valid : before.Valid) (state : WeightedMemory.State (External n))
    (agree : state.label = labels before.comparator K before.blocks) :
    total positiveEntry state (access before request decomposition data) ≤
      total negativeChange state (access before request decomposition data) +
      (∑ piece ∈ CreatorPhase.pieces (prepared before request) (Execution.source request),
        OutgoingExcess.charge .nonrootWinner K data (prepared before request) (Execution.source request) piece.1 piece.2) +
      (∑ piece ∈ CreatorPhase.pieces (prepared before request) (Execution.source request),
        OutgoingExcess.charge .rootLoser K data (prepared before request) (Execution.source request) piece.1 piece.2) := by
  classical
  let initial := GreedyMerge.StateLabels.label before.comparator.externalDepth K (prepared before request)
  have agrees : ∀ record, state.label record = initial record.val := by
    intro record
    rw [agree, ← prepared_labels before request K]
    rfl
  have geometry := AccessTrace.geometry data (Execution.source request) rfl (Execution.root_minimum _ request root)
  have identity : total positiveEntry state (access before request decomposition data) =
      ∑ i : Fin data.events.length,
        SourceCensus.positiveWeight (prepared before request) (Execution.source request) initial id (eventKeys (data.events.get i)) := by
    unfold access
    rw [AccessJournal.program_indexed_total]
    apply Finset.sum_congr rfl
    intro i _
    have snapshots := AccessJournal.source_snapshots data (Execution.source request) geometry
      (AccessTrace.kind (prepared before request) (Execution.source request)) initial state agrees i
    have matching := SourceCensus.sameBlock_keys (prepared before request) (Execution.source request) (data.events.get i)
    dsimp only [eventKeys] at matching
    by_cases same : AccessTrace.SameBlock (prepared before request) (Execution.source request) (data.events.get i)
    · simp only [AccessJournal.pairWeight, AccessTrace.kind, if_pos same, positiveEntry, zero_add,
        SourceCensus.positiveWeight, eventKeys, id_eq, if_pos (matching.mp same)]
    · simp only [AccessJournal.pairWeight, AccessTrace.kind, if_neg same, positiveEntry, add_zero,
        SourceCensus.positiveWeight, eventKeys, id_eq, if_neg (mt matching.mpr same)]
      rw [snapshots.1, snapshots.2]
  rw [identity]
  change _ ≤ total negativeChange state (AccessJournal.program _ _ _) + _ + _
  rw [AccessJournal.program_negative_sum data (Execution.source request) geometry _ initial state agrees]
  exact positive_phase_bound before request K root decomposition data valid

end Greedy.RunJournal

