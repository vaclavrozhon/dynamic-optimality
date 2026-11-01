import Greedy.CreatorMemorySide
import Greedy.CreditCensus

/-! Creator-shift accounting agrees with the same live entry journal. -/

namespace Greedy.RunJournal

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical Splay.Analysis
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.HeapAllocation
open GreedyMerge.ActualLinks GreedyMerge.PathPlateau GreedyMerge.PlateauBridge
open GreedyMerge.AccessSourceAccounting GreedyMerge.Fringe GreedyMerge.Fringe.Schedule
open EntryJournal RestorationJournal
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem memory_phase_eq {n : ℕ} (before : Execution.State n) (request : Fin n) (K : ℤ)
    (root : before.comparator.HasRoot request.val)
    (decomposition : Decomposition before.refined.tree request.val)
    (data : AccessScheduleData before.comparator before.refined.tree (Execution.afterRefinement before request).tree decomposition)
    (valid : before.Valid) (memory : External n → ℤ)
    (synced : LiveMemory.Synced memory (prepared before request)) :
    (∑ i : Fin data.events.length,
      SourceCensus.memoryWeight (prepared before request) (Execution.source request) (LiveMemory.atKey memory) (eventKeys (data.events.get i))) =
      CreatorPhase.shiftPhase data (prepared before request) (Execution.source request) := by
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
  have leftEq := SourceCensus.memory_side_sum
    (canonicalParent (Snapshot.ofTree before.comparator) before.refined.tree)
    (prepared before request) (Execution.source request) true ready.sound ready.valid
    leftView (ids true) data.owner data.projection.2.1
    (fun q lower bound => data.localOwners q lower (by omega)) memory synced
  have rightEq := SourceCensus.memory_side_sum
    (canonicalParent (Snapshot.ofTree before.comparator) before.refined.tree)
    (prepared before request) (Execution.source request) false ready.sound ready.valid
    rightView (ids false) data.owner data.projection.2.2
    (fun q lower bound => data.localOwners q (by omega) bound) memory synced
  have geometry := AccessTrace.geometry data (Execution.source request) rfl (Execution.root_minimum _ request root)
  rw [AtomicAccess.sum_two_sides data (Execution.source request) geometry,
    CreatorPhase.shiftPhase, SourceCensus.sum_pieces]
  simp only [CreatorPhase.shiftPart, if_true, Bool.false_eq_true, if_false]
  exact (congrArg₂ (· + ·) leftEq rightEq).symm

theorem access_creator_eq {n : ℕ} (before : Execution.State n) (request : Fin n) (K : ℤ)
    (root : before.comparator.HasRoot request.val)
    (decomposition : Decomposition before.refined.tree request.val)
    (data : AccessScheduleData before.comparator before.refined.tree (Execution.afterRefinement before request).tree decomposition)
    (valid : before.Valid) (state : WeightedMemory.State (External n))
    (synced : LiveMemory.Synced state.memory before.blocks) :
    total creatorShift state (access before request decomposition data) =
      CreatorPhase.shiftPhase data (prepared before request) (Execution.source request) := by
  classical
  have memory : LiveMemory.Synced state.memory (prepared before request) :=
    EntryProperties.convertHeap_property before.comparator.externalDepth
      (fun owner _ => decide (owner = Execution.source request)) before.next before.blocks synced
  rw [← memory_phase_eq before request K root decomposition data valid state.memory memory]
  have geometry := AccessTrace.geometry data (Execution.source request) rfl (Execution.root_minimum _ request root)
  unfold access
  rw [AccessJournal.program_indexed_total]
  apply Finset.sum_congr rfl
  intro i _
  have memories := AccessJournal.source_memories data (Execution.source request) geometry
    (AccessTrace.kind (prepared before request) (Execution.source request)) state i
  have matching := SourceCensus.sameBlock_keys (prepared before request) (Execution.source request) (data.events.get i)
  dsimp only [eventKeys] at matching
  by_cases same : AccessTrace.SameBlock (prepared before request) (Execution.source request) (data.events.get i)
  · simp only [AccessJournal.pairWeight, AccessTrace.kind, if_pos same, creatorShift, add_zero,
      SourceCensus.memoryWeight, eventKeys, if_pos (matching.mp same), LiveMemory.atKey_record]
    rw [memories.1, memories.2]
  · simp only [AccessJournal.pairWeight, AccessTrace.kind, if_neg same, creatorShift, zero_add,
      SourceCensus.memoryWeight, eventKeys, if_neg (mt matching.mpr same)]

end Greedy.RunJournal
