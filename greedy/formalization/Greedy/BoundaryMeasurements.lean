import Greedy.SourceClasses
import Greedy.AccessMeasurements

/-! Boundary links are paid by actual drops or the counted nondropping cells. -/

namespace Greedy.AccessJournal

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Analysis
open GreedyMerge.ActualLinks GreedyMerge.PathPlateau EntryJournal
open scoped BigOperators

theorem program_boundary_bound {n access : ℕ} {comparator oldTree newTree : BST 0 n}
    {p : Decomposition oldTree access} (data : AccessScheduleData comparator oldTree newTree p)
    (source : External n) (geometry : AccessTrace.Geometry data source)
    (kind : External n × External n → Kind) (initial : ℕ → ℤ)
    (state : WeightedMemory.State (External n)) (agree : ∀ record, state.label record = initial record.val) :
    total boundary state (program comparator.externalDepth kind data.events) ≤
      total negativeChange state (program comparator.externalDepth kind data.events) +
      ∑ i : Fin data.events.length, if kind (data.events.get i) = .boundary ∧
        initial (data.events.get i).2.val ≤
          (contractedGap (comparator.externalDepth (data.events.get i).2.val - comparator.externalDepth (data.events.get i).1.val) : ℤ)
        then 1 else 0 := by
  rw [program_indexed_total, program_negative_sum data source geometry kind initial state agree, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  cases named : kind (data.events.get i) <;>
    simp only [pairWeight, named, boundary, reduceCtorEq, false_and, if_false, zero_add, true_and] <;>
    (try split_ifs) <;> omega

end Greedy.AccessJournal

namespace Greedy.RunJournal

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical Splay.Analysis
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.HeapAllocation
open GreedyMerge.ActualLinks GreedyMerge.PathPlateau GreedyMerge.PlateauBridge
open GreedyMerge.AccessSourceAccounting GreedyMerge.Fringe GreedyMerge.Fringe.Schedule
open EntryJournal RestorationJournal
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem boundary_phase_sum {n : ℕ} (before : Execution.State n) (request : Fin n) (K : ℤ)
    (root : before.comparator.HasRoot request.val)
    (decomposition : Decomposition before.refined.tree request.val)
    (data : AccessScheduleData before.comparator before.refined.tree (Execution.afterRefinement before request).tree decomposition)
    (valid : before.Valid) :
    (∑ piece ∈ CreatorPhase.pieces (prepared before request) (Execution.source request),
      DepartureAmounts.charge .boundary K data (prepared before request) (Execution.source request) piece.1 piece.2) =
      ∑ i : Fin data.events.length,
        if SourceCensus.SameBlockKeys (prepared before request) (Execution.source request) (eventKeys (data.events.get i)) then 0 else
          if GreedyMerge.StateLabels.label before.comparator.externalDepth K (prepared before request) (data.events.get i).2.val ≤
            (contractedGap (before.comparator.externalDepth (data.events.get i).2.val - before.comparator.externalDepth (data.events.get i).1.val) : ℤ)
          then 1 else 0 := by
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
  have leftSum := SourceCensus.boundary_sum (prepared before request) (Execution.source request) true (ready.valid _)
    leftView (ids true) data.owner data.projection.2.1 (fun q lower bound => data.localOwners q lower (by omega))
  have rightSum := SourceCensus.boundary_sum (prepared before request) (Execution.source request) false (ready.valid _)
    rightView (ids false) data.owner data.projection.2.2 (fun q lower bound => data.localOwners q (by omega) bound)
  rw [SourceCensus.sum_pieces]
  simp only [DepartureAmounts.charge, if_true, Bool.false_eq_true, if_false]
  rw [leftSum, rightSum]
  have geometry := AccessTrace.geometry data (Execution.source request) rfl (Execution.root_minimum _ request root)
  exact (AtomicAccess.sum_two_sides data (Execution.source request) geometry
    (fun edge => if SourceCensus.SameBlockKeys (prepared before request) (Execution.source request) edge then 0 else
      if GreedyMerge.StateLabels.label before.comparator.externalDepth K (prepared before request) edge.2 ≤
        (contractedGap (before.comparator.externalDepth edge.2 - before.comparator.externalDepth edge.1) : ℤ)
      then 1 else 0)).symm

theorem access_boundary_bound {n : ℕ} (before : Execution.State n) (request : Fin n) (K : ℤ)
    (root : before.comparator.HasRoot request.val)
    (decomposition : Decomposition before.refined.tree request.val)
    (data : AccessScheduleData before.comparator before.refined.tree (Execution.afterRefinement before request).tree decomposition)
    (valid : before.Valid) (state : WeightedMemory.State (External n))
    (agree : state.label = labels before.comparator K before.blocks) :
    total boundary state (access before request decomposition data) ≤
      total negativeChange state (access before request decomposition data) +
      ∑ piece ∈ CreatorPhase.pieces (prepared before request) (Execution.source request),
        DepartureAmounts.charge .boundary K data (prepared before request) (Execution.source request) piece.1 piece.2 := by
  rw [boundary_phase_sum before request K root decomposition data valid]
  have bound := AccessJournal.program_boundary_bound data (Execution.source request)
    (AccessTrace.geometry data _ rfl (Execution.root_minimum _ request root))
    (AccessTrace.kind (prepared before request) (Execution.source request))
    (GreedyMerge.StateLabels.label before.comparator.externalDepth K (prepared before request)) state
    (fun record => by rw [agree, ← prepared_labels before request K]; rfl)
  apply le_trans bound
  apply le_of_eq
  apply congrArg (fun value => total negativeChange state (access before request decomposition data) + value)
  apply Finset.sum_congr rfl
  intro i _
  have same := SourceCensus.sameBlock_keys (prepared before request) (Execution.source request) (data.events.get i)
  by_cases internal : AccessTrace.SameBlock (prepared before request) (Execution.source request) (data.events.get i)
  · simp only [AccessTrace.kind, if_pos internal, if_pos (same.mp internal), reduceCtorEq, false_and, if_false]
  · simp only [AccessTrace.kind, if_neg internal, if_neg (mt same.mpr internal), true_and]

end Greedy.RunJournal
