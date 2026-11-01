import Greedy.SourceMemories
import Greedy.AtomicSums

/-! The signed loser shift is read from literal old memberships. -/

namespace Greedy.LoserShift

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.ActualLinks
open GreedyMerge.HeapAllocation GreedyMerge.AccessSourceAccounting GreedyMerge.PathPlateau
open EntryJournal RestorationJournal
open scoped BigOperators

noncomputable def weight {n : ℕ} (states : States n) (source : External n)
    (label : External n → ℤ) (event : External n × External n) : ℤ := by
  classical
  exact if AccessTrace.SameBlock states source event then label event.1 - LiveMemory.stored states event.2 else 0

noncomputable def phase {n : ℕ} (before : Execution.State n) (request : Fin n) (K : ℤ)
    (decomposition : Decomposition before.refined.tree request.val)
    (data : AccessScheduleData before.comparator before.refined.tree
      (Execution.afterRefinement before request).tree decomposition) : ℤ :=
  (data.events.map (weight (RunJournal.prepared before request) (Execution.source request)
    (labels before.comparator K (RunJournal.prepared before request)))).sum

noncomputable def sum {n : ℕ} {K : ℤ} {first last : Execution.State n} {requests : List (Fin n)} :
    Execution.Run K first last requests → ℤ
  | .done _ => 0
  | .rotate _ _ _ rest => sum rest
  | .access (first := first) request _ decomposition data _ rest => phase first request K decomposition data + sum rest

theorem access_eq {n : ℕ} (before : Execution.State n) (request : Fin n) (K : ℤ)
    (root : before.comparator.HasRoot request.val)
    (decomposition : Decomposition before.refined.tree request.val)
    (data : AccessScheduleData before.comparator before.refined.tree
      (Execution.afterRefinement before request).tree decomposition)
    (state : WeightedMemory.State (External n))
    (agree : state.label = labels before.comparator K before.blocks)
    (synced : LiveMemory.Synced state.memory before.blocks) :
    total shift state (RunJournal.access before request decomposition data) = phase before request K decomposition data := by
  classical
  let prepared := RunJournal.prepared before request
  let source := Execution.source request
  let initial := GreedyMerge.StateLabels.label before.comparator.externalDepth K prepared
  have labelsAgree : ∀ record, state.label record = initial record.val := by
    intro record
    rw [agree, ← RunJournal.prepared_labels before request K]
    rfl
  have memory : LiveMemory.Synced state.memory prepared :=
    EntryProperties.convertHeap_property before.comparator.externalDepth
      (fun owner _ => decide (owner = source)) before.next before.blocks synced
  have geometry := AccessTrace.geometry data source rfl (Execution.root_minimum _ request root)
  unfold RunJournal.access phase
  rw [AccessJournal.program_indexed_total, ← AtomicAccess.indexed_sum]
  apply Finset.sum_congr rfl
  intro i _
  have snapshots := AccessJournal.source_snapshots data source geometry (AccessTrace.kind prepared source) initial state labelsAgree i
  have memories := AccessJournal.source_memories data source geometry (AccessTrace.kind prepared source) state i
  change AccessJournal.pairWeight shift before.comparator.externalDepth (AccessTrace.kind prepared source)
    (run state (AccessJournal.program before.comparator.externalDepth (AccessTrace.kind prepared source) (data.events.take i.val)))
    (data.events.get i) = weight prepared source (labels before.comparator K prepared) (data.events.get i)
  by_cases same : AccessTrace.SameBlock prepared source (data.events.get i)
  · have kindEq : AccessTrace.kind prepared source (data.events.get i) = .internal := by simp only [AccessTrace.kind, if_pos same]
    have witnesses := same
    obtain ⟨side, block, blockMem, winner, winMem, loser, loseMem, winKey, loseKey⟩ := witnesses
    have represented : GreedyMerge.BlockCoverage.Represented prepared (data.events.get i).2.val :=
      ⟨source, side, loser, ClosedFamilies.frozen_entry_mem _ block blockMem loser loseMem, loseKey⟩
    have stored := LiveMemory.stored_eq prepared (data.events.get i).2 state.memory memory represented
    simp only [AccessJournal.pairWeight, kindEq, shift, EntryJournal.encode, WeightedMemory.shift,
      beq_self_eq_true, if_true, add_zero, weight, if_pos same]
    rw [snapshots.1, memories.2, stored]
    rfl
  · have kindEq : AccessTrace.kind prepared source (data.events.get i) = .boundary := by simp only [AccessTrace.kind, if_neg same]
    simp only [AccessJournal.pairWeight, kindEq, shift, EntryJournal.encode, WeightedMemory.shift, weight, if_neg same]
    rfl

end Greedy.LoserShift
