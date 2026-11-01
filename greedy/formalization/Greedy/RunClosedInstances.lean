import Greedy.InstanceAdministration
import Greedy.InstanceAccess
import Greedy.ExecutionRun
import Greedy.RunJournal

/-!
Once a frozen instance has a hereditary property, its literal descendants
retain it through the entire remaining run. Fresh names exclude any new
grower or singleton with that old id.
-/

namespace Greedy.ClosedInstances

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.HeapAllocation
open FreshRecanonicalization

theorem refinement_execution_closed {n count id : ℕ} {property : Frozen → Prop}
    (comparator : BST 0 n) (reader : Reader n) {first last : Frame n} {births : List ℕ}
    (execution : FreshRecanonicalization.Execution comparator reader count first last births)
    (closed : HeapClosed id property first.states) (hereditary : ClosedFamilies.Hereditary property) (past : id < first.next) :
    HeapClosed id property last.states ∧ first.next ≤ last.next := by
  induction execution with
  | nil => exact ⟨closed, le_refl _⟩
  | @cons count depth first last middle births rotation rest ih =>
      let ports := refinementRotationPorts (Snapshot.ofTree comparator) rotation
      have head := refinement_closed comparator middle ports (reader first.clock) first.next first.states closed hereditary past
      have advance := FreshRecanonicalization.allocate_monotone comparator middle ports (reader first.clock) first.next first.states
      have tail := ih head (past.trans_le advance)
      exact ⟨tail.1, advance.trans tail.2⟩

theorem complete_rotation_closed {n depth id : ℕ} {property : Frozen → Prop}
    (before : Greedy.Execution.State n) (after : BST 0 n) (rotation : RotationAt depth before.comparator after)
    (K : ℤ) (data : Greedy.Execution.RotationData before after rotation K)
    (closed : HeapClosed id property before.blocks) (hereditary : ClosedFamilies.Hereditary property) (past : id < before.next) :
    HeapClosed id property data.state.blocks ∧ before.next ≤ data.state.next := by
  let input := comparatorInput rotation
  let plan := GreedyMerge.ComparatorOuter.rotationPlan input.step before.refined.tree
  have head := comparator_closed input.profile before.refined.tree plan (Greedy.Execution.entryReader after K before.clock)
    before.next before.blocks closed hereditary past
  have advance := allocateComparatorPlan_monotone input.profile before.refined.tree plan
    (Greedy.Execution.entryReader after K before.clock) before.next before.blocks
  have tail := refinement_execution_closed after (Greedy.Execution.entryReader after K) data.executed head hereditary (past.trans_le advance)
  exact ⟨tail.1, advance.trans tail.2⟩

theorem afterAccess_closed {n id : ℕ} {property : Frozen → Prop}
    (before : Greedy.Execution.State n) (request : Fin n) (K : ℤ)
    (decomposition : GreedyMerge.PathPlateau.Decomposition before.refined.tree request.val)
    (data : GreedyMerge.ActualLinks.AccessScheduleData before.comparator before.refined.tree
      (Greedy.Execution.afterRefinement before request).tree decomposition)
    (closed : HeapClosed id property before.blocks) (hereditary : ClosedFamilies.Hereditary property) (past : id < before.next) :
    HeapClosed id property (Greedy.Execution.afterAccess before request K decomposition data).blocks := by
  apply runLinks_closed
  · exact convertHeap_closed id before.next property before.comparator.externalDepth _ before.blocks closed past
  · exact hereditary

theorem run_closed {n id : ℕ} {property : Frozen → Prop} {K : ℤ}
    {first last : Greedy.Execution.State n} {requests : List (Fin n)}
    (execution : Greedy.Execution.Run K first last requests) (closed : HeapClosed id property first.blocks)
    (hereditary : ClosedFamilies.Hereditary property) (past : id < first.next) :
    HeapClosed id property last.blocks ∧ first.next ≤ last.next := by
  induction execution with
  | done => exact ⟨closed, le_refl _⟩
  | @rotate first last after depth requests rotation data valid rest ih =>
      have head := complete_rotation_closed first after rotation K data closed hereditary past
      have tail := ih head.1 (past.trans_le head.2)
      exact ⟨tail.1, head.2.trans tail.2⟩
  | @access first last requests request root decomposition data valid rest ih =>
      have head := afterAccess_closed first request K decomposition data closed hereditary past
      have advance : first.next ≤ (Greedy.Execution.afterAccess first request K decomposition data).next := Nat.le_add_right _ _
      have tail := ih head (past.trans_le advance)
      exact ⟨tail.1, advance.trans tail.2⟩

def AllSourcesClosed {n id : ℕ} (property : Frozen → Prop) {K : ℤ}
    {first last : Greedy.Execution.State n} {requests : List (Fin n)} : Greedy.Execution.Run K first last requests → Prop
  | .done state => HeapClosed id property state.blocks
  | .rotate (first := first) _ _ _ rest => HeapClosed id property first.blocks ∧ AllSourcesClosed (id := id) property rest
  | .access (first := first) request _ _ _ _ rest =>
      HeapClosed id property first.blocks ∧ HeapClosed id property (RunJournal.prepared first request) ∧ AllSourcesClosed (id := id) property rest

theorem all_sources_closed {n id : ℕ} {property : Frozen → Prop} {K : ℤ}
    {first last : Greedy.Execution.State n} {requests : List (Fin n)}
    (execution : Greedy.Execution.Run K first last requests) (closed : HeapClosed id property first.blocks)
    (hereditary : ClosedFamilies.Hereditary property) (past : id < first.next) : AllSourcesClosed (id := id) property execution := by
  induction execution with
  | done => exact closed
  | @rotate first last after depth requests rotation data valid rest ih =>
      have head := complete_rotation_closed first after rotation K data closed hereditary past
      exact ⟨closed, ih head.1 (past.trans_le head.2)⟩
  | @access first last requests request root decomposition data valid rest ih =>
      have advance : first.next ≤ (Greedy.Execution.afterAccess first request K decomposition data).next := Nat.le_add_right _ _
      exact ⟨closed, convertHeap_closed id first.next property first.comparator.externalDepth _ first.blocks closed past,
        ih (afterAccess_closed first request K decomposition data closed hereditary past) (past.trans_le advance)⟩

end Greedy.ClosedInstances

