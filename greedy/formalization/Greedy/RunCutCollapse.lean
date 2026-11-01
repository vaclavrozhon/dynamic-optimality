import Greedy.CutCollapse
import Greedy.RunFamilyOrder

/-! The cut-collapse theorem applies to the literal execution constructor. -/

namespace Greedy.ClosedFamilies

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.HeapAllocation
open GreedyMerge.ActualLinks GreedyMerge.PathPlateau GreedyMerge.FrozenHistory

theorem afterAccess_cut_collapse {n cut : ℕ} (before : Execution.State n) (request : Fin n) (K : ℤ)
    (root : before.comparator.HasRoot request.val)
    (decomposition : Decomposition before.refined.tree request.val)
    (data : AccessScheduleData before.comparator before.refined.tree
      (Execution.afterRefinement before request).tree decomposition)
    (inv : FamilyOrder.Invariant before.clock before.next before.blocks)
    (valid : (Execution.afterAccess before request K decomposition data).Valid)
    (side : Bool) (block : Frozen)
    (member : block ∈ (RunJournal.prepared before request (Execution.source request) side).shrinking)
    (crosses : GreedyForest.Straddles (fun joined => decide (cut ≤ joined)) (joins block)) :
    HeapClosed block.family (AvoidsCut cut) (Execution.afterAccess before request K decomposition data).blocks ∧
      block.family < (Execution.afterAccess before request K decomposition data).next := by
  have prepared := FamilyOrder.convertHeap_invariant before.comparator.externalDepth
    (fun owner _ => decide (owner = Execution.source request)) before.next before.blocks inv
  change FamilyOrder.Invariant before.clock (before.next + Fintype.card (Place n))
    (RunJournal.prepared before request) at prepared
  have zero : (Snapshot.ofTree before.comparator).rank (Execution.source request) = 0 :=
    GreedyMerge.AccessFrontier.comparator_zero_of_global before.comparator (Execution.root_minimum _ request root)
  refine ⟨runLinks_cut_collapse data (Execution.source request) rfl zero _ _
    (RunJournal.prepared before request) prepared valid.1 side block member crosses, ?_⟩
  have past := prepared.names.below (encode n (Execution.source request, side)) block.family
    (FamilyNames.frozen_mem _ block (by simpa [table] using member))
  simpa only [Execution.afterAccess, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, Nat.mul_comm] using past

theorem remaining_sources_avoid {n cut : ℕ} (before : Execution.State n) (request : Fin n) (K : ℤ)
    (root : before.comparator.HasRoot request.val)
    (decomposition : Decomposition before.refined.tree request.val)
    (data : AccessScheduleData before.comparator before.refined.tree
      (Execution.afterRefinement before request).tree decomposition)
    (inv : FamilyOrder.Invariant before.clock before.next before.blocks)
    (valid : (Execution.afterAccess before request K decomposition data).Valid)
    {last : Execution.State n} {requests : List (Fin n)}
    (rest : Execution.Run K (Execution.afterAccess before request K decomposition data) last requests)
    (side : Bool) (block : Frozen)
    (member : block ∈ (RunJournal.prepared before request (Execution.source request) side).shrinking)
    (crosses : GreedyForest.Straddles (fun joined => decide (cut ≤ joined)) (joins block)) :
    AllSourcesClosed (family := block.family) (AvoidsCut cut) rest := by
  have collapsed := afterAccess_cut_collapse before request K root decomposition data inv valid side block member crosses
  exact all_sources_closed rest collapsed.1 (avoidsCut_hereditary cut) collapsed.2

end Greedy.ClosedFamilies
