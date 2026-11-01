import Greedy.FamilyAdministration
import Greedy.FamilyAccess
import Greedy.ExecutionRun

/-! Fresh and exclusive growing-family names along the entire actual run. -/

namespace Greedy.FamilyNames

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.HeapAllocation
open FreshRecanonicalization

theorem refinement_execution_inventory {n count : ℕ} (comparator : BST 0 n) (reader : Reader n)
    {first last : Frame n} {births : List ℕ}
    (execution : FreshRecanonicalization.Execution comparator reader count first last births)
    (inventory : HeapFamilyInventory first.states first.next) : HeapFamilyInventory last.states last.next := by
  induction execution with
  | nil => exact inventory
  | @cons count depth first last middle births rotation rest ih =>
      exact ih (refinement_inventory comparator middle (refinementRotationPorts (Snapshot.ofTree comparator) rotation)
        (reader first.clock) first.next first.states inventory)

theorem complete_rotation_inventory {n depth : ℕ} (before : Greedy.Execution.State n) (after : BST 0 n)
    (rotation : RotationAt depth before.comparator after) (K : ℤ)
    (data : Greedy.Execution.RotationData before after rotation K)
    (inventory : HeapFamilyInventory before.blocks before.next) : HeapFamilyInventory data.state.blocks data.state.next := by
  let input := comparatorInput rotation
  let plan := GreedyMerge.ComparatorOuter.rotationPlan input.step before.refined.tree
  have head := comparator_inventory input.profile before.refined.tree plan
    (Greedy.Execution.entryReader after K before.clock) before.next before.blocks inventory
  exact refinement_execution_inventory after (Greedy.Execution.entryReader after K) data.executed head

theorem afterAccess_inventory {n : ℕ} (before : Greedy.Execution.State n) (request : Fin n) (K : ℤ)
    (decomposition : GreedyMerge.PathPlateau.Decomposition before.refined.tree request.val)
    (data : GreedyMerge.ActualLinks.AccessScheduleData before.comparator before.refined.tree
      (Greedy.Execution.afterRefinement before request).tree decomposition)
    (inventory : HeapFamilyInventory before.blocks before.next) :
    HeapFamilyInventory (Greedy.Execution.afterAccess before request K decomposition data).blocks
      (Greedy.Execution.afterAccess before request K decomposition data).next := by
  apply runLinks_inventory
  simpa only [slot_count, Greedy.Execution.afterAccess] using convertHeap_inventory before.comparator.externalDepth
    (fun owner _ => decide (owner = Greedy.Execution.source request)) before.next before.blocks inventory

theorem run_inventory {n : ℕ} {K : ℤ} {first last : Greedy.Execution.State n} {requests : List (Fin n)}
    (execution : Greedy.Execution.Run K first last requests) (inventory : HeapFamilyInventory first.blocks first.next) :
    HeapFamilyInventory last.blocks last.next := by
  induction execution with
  | done => exact inventory
  | @rotate first last after depth requests rotation data valid rest ih =>
      exact ih (complete_rotation_inventory first after rotation K data inventory)
  | @access first last requests request root decomposition data valid rest ih =>
      exact ih (afterAccess_inventory first request K decomposition data inventory)

theorem initialized_inventory {n : ℕ} (initial comparator : BST 0 n) (K : ℤ)
    {last : Greedy.Execution.State n} {requests : List (Fin n)}
    (execution : Greedy.Execution.Run K (Greedy.Execution.initial initial comparator K) last requests) :
    HeapFamilyInventory last.blocks last.next :=
  run_inventory execution (initial_inventory (Snapshot.ofTree comparator) _ K)

end Greedy.FamilyNames
