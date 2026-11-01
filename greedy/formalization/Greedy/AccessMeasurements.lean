import Greedy.SourceCensus
import Greedy.AtomicSums
import Greedy.JournalLinkSums

/-! Source lifetime charges and the actual access journal have identical totals. -/

namespace Greedy.RunJournal

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical Splay.Analysis
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.HeapAllocation
open GreedyMerge.ActualLinks GreedyMerge.PathPlateau GreedyMerge.PlateauBridge
open GreedyMerge.AccessSourceAccounting GreedyMerge.Fringe GreedyMerge.Fringe.Schedule
open EntryJournal RestorationJournal
open scoped BigOperators

theorem prepared_labels {n : ℕ} (before : Execution.State n) (request : Fin n) (K : ℤ) :
    labels before.comparator K (prepared before request) = labels before.comparator K before.blocks := by
  funext record
  change GreedyMerge.StateLabels.label _ _ _ record.val = GreedyMerge.StateLabels.label _ _ _ record.val
  unfold prepared
  rw [← convertRoot_eq_convertHeap, convertRoot_labels]

theorem increase_phase_sum {n : ℕ} (before : Execution.State n) (request : Fin n) (K : ℤ)
    (root : before.comparator.HasRoot request.val)
    (decomposition : Decomposition before.refined.tree request.val)
    (data : AccessScheduleData before.comparator before.refined.tree (Execution.afterRefinement before request).tree decomposition)
    (valid : before.Valid) :
    (∑ piece ∈ CreatorPhase.pieces (prepared before request) (Execution.source request),
      DepartureAmounts.charge .increase K data (prepared before request) (Execution.source request) piece.1 piece.2) =
      ∑ i : Fin data.events.length,
        max 0 ((contractedGap (before.comparator.externalDepth (data.events.get i).2.val -
          before.comparator.externalDepth (data.events.get i).1.val) : ℤ) -
          GreedyMerge.StateLabels.label before.comparator.externalDepth K (prepared before request) (data.events.get i).2.val) := by
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
  have upper := data.right.lower_le_upper
  have leftSum := SourceCensus.increase_sum leftView (ids true) data.owner data.projection.2.1
    (fun q lower bound => data.localOwners q lower (by omega))
  have rightSum := SourceCensus.increase_sum rightView (ids false) data.owner data.projection.2.2
    (fun q lower bound => data.localOwners q (by omega) bound)
  rw [SourceCensus.sum_pieces]
  simp only [DepartureAmounts.charge, if_true, Bool.false_eq_true, if_false]
  rw [leftSum, rightSum]
  have geometry := AccessTrace.geometry data (Execution.source request) rfl (Execution.root_minimum _ request root)
  exact (AtomicAccess.sum_two_sides data (Execution.source request) geometry
    (fun edge => max 0 ((contractedGap (before.comparator.externalDepth edge.2 - before.comparator.externalDepth edge.1) : ℤ) -
      GreedyMerge.StateLabels.label before.comparator.externalDepth K (prepared before request) edge.2))).symm

theorem access_positive_eq {n : ℕ} (before : Execution.State n) (request : Fin n) (K : ℤ)
    (root : before.comparator.HasRoot request.val)
    (decomposition : Decomposition before.refined.tree request.val)
    (data : AccessScheduleData before.comparator before.refined.tree (Execution.afterRefinement before request).tree decomposition)
    (valid : before.Valid) (state : WeightedMemory.State (External n))
    (agree : state.label = labels before.comparator K before.blocks) :
    total positiveChange state (access before request decomposition data) =
      ∑ piece ∈ CreatorPhase.pieces (prepared before request) (Execution.source request),
        DepartureAmounts.charge .increase K data (prepared before request) (Execution.source request) piece.1 piece.2 := by
  rw [increase_phase_sum before request K root decomposition data valid]
  apply AccessJournal.program_positive_sum data (Execution.source request)
    (AccessTrace.geometry data _ rfl (Execution.root_minimum _ request root))
  intro record
  rw [agree, ← prepared_labels before request K]
  rfl

end Greedy.RunJournal
