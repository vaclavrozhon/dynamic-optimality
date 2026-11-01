import Greedy.FamilyOrderAdministration
import Greedy.FamilyOrderAccess
import Greedy.RunFamilyNames
import Greedy.RunJournal

/-! Global historical family order is constructed for every actual access source. -/

namespace Greedy.FamilyOrder

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.HeapAllocation
open FreshRecanonicalization

theorem refinement_execution_invariant {n count : ℕ} (comparator : BST 0 n) (reader : Reader n)
    (time : ∀ clock stage states record owner, (reader clock stage states record owner).joined = clock+1+stage)
    {first last : Frame n} {births : List ℕ}
    (execution : FreshRecanonicalization.Execution comparator reader count first last births)
    (inv : Invariant first.clock first.next first.states) : Invariant last.clock last.next last.states := by
  induction execution with
  | nil => exact inv
  | @cons count depth first last middle births rotation rest ih =>
      let ports := refinementRotationPorts (Snapshot.ofTree comparator) rotation
      have head := refinement_invariant comparator middle ports (reader first.clock) (first.clock+1)
        (time first.clock) first.next first.states (inv.advance (first.clock+1) (by omega))
      have bound : first.clock+1+ports.length ≤ first.clock+5 := by
        have few := (refinementRotationPorts_spec (Snapshot.ofTree comparator) rotation).2.1
        dsimp only [ports]
        omega
      exact ih (head.advance (first.clock+5) bound)

theorem complete_rotation_invariant {n depth : ℕ} (before : Greedy.Execution.State n) (after : BST 0 n)
    (rotation : RotationAt depth before.comparator after) (K : ℤ) (data : Greedy.Execution.RotationData before after rotation K)
    (inv : Invariant before.clock before.next before.blocks) : Invariant data.state.clock data.state.next data.state.blocks := by
  let input := comparatorInput rotation
  let plan := GreedyMerge.ComparatorOuter.rotationPlan input.step before.refined.tree
  have head := comparator_invariant input.profile before.refined.tree plan (Greedy.Execution.entryReader after K before.clock)
    (before.clock+1) (fun _ _ _ _ => rfl) before.next before.blocks (inv.advance (before.clock+1) (by omega))
  apply refinement_execution_invariant after (Greedy.Execution.entryReader after K) (fun _ _ _ _ _ => rfl) data.executed
  simpa only [Greedy.Execution.rotationPrefix, Greedy.FreshComparator.allocate, Nat.add_assoc] using head

theorem afterAccess_ordered {n : ℕ} (before : Greedy.Execution.State n) (request : Fin n) (K : ℤ)
    (decomposition : GreedyMerge.PathPlateau.Decomposition before.refined.tree request.val)
    (data : GreedyMerge.ActualLinks.AccessScheduleData before.comparator before.refined.tree
      (Greedy.Execution.afterRefinement before request).tree decomposition)
    (inv : Invariant before.clock before.next before.blocks) :
    HeapOrdered (Greedy.Execution.afterAccess before request K decomposition data).blocks := by
  apply runLinks_ordered
  exact convertHeap_ordered before.comparator.externalDepth _ before.next before.blocks inv.ordered inv.names
    ((GreedyMerge.ActualLinks.chronology_iff ..).mp inv.chronology).1

theorem afterAccess_invariant {n : ℕ} (before : Greedy.Execution.State n) (request : Fin n) (K : ℤ)
    (decomposition : GreedyMerge.PathPlateau.Decomposition before.refined.tree request.val)
    (data : GreedyMerge.ActualLinks.AccessScheduleData before.comparator before.refined.tree
      (Greedy.Execution.afterRefinement before request).tree decomposition)
    (inv : Invariant before.clock before.next before.blocks)
    (valid : (Greedy.Execution.afterAccess before request K decomposition data).Valid) :
    Invariant (Greedy.Execution.afterAccess before request K decomposition data).clock
      (Greedy.Execution.afterAccess before request K decomposition data).next
      (Greedy.Execution.afterAccess before request K decomposition data).blocks :=
  ⟨FamilyNames.afterAccess_inventory before request K decomposition data inv.names,
    afterAccess_ordered before request K decomposition data inv, valid.2.1, valid.2.2.1⟩

theorem run_invariant {n : ℕ} {K : ℤ} {first last : Greedy.Execution.State n} {requests : List (Fin n)}
    (execution : Greedy.Execution.Run K first last requests) (inv : Invariant first.clock first.next first.blocks) :
    Invariant last.clock last.next last.blocks := by
  induction execution with
  | done => exact inv
  | @rotate first last after depth requests rotation data valid rest ih =>
      exact ih (complete_rotation_invariant first after rotation K data inv)
  | @access first last requests request root decomposition data valid rest ih =>
      exact ih (afterAccess_invariant first request K decomposition data inv valid)

def AllSourcesInvariant {n : ℕ} {K : ℤ} {first last : Greedy.Execution.State n} {requests : List (Fin n)} :
    Greedy.Execution.Run K first last requests → Prop
  | .done state => Invariant state.clock state.next state.blocks
  | .rotate (first := first) _ _ _ rest => Invariant first.clock first.next first.blocks ∧ AllSourcesInvariant rest
  | .access (first := first) request _ _ _ _ rest =>
      Invariant first.clock first.next first.blocks ∧
      Invariant first.clock (first.next + Fintype.card (Place n)) (RunJournal.prepared first request) ∧ AllSourcesInvariant rest

theorem all_sources_invariant {n : ℕ} {K : ℤ} {first last : Greedy.Execution.State n} {requests : List (Fin n)}
    (execution : Greedy.Execution.Run K first last requests) (inv : Invariant first.clock first.next first.blocks) :
    AllSourcesInvariant execution := by
  induction execution with
  | done => exact inv
  | @rotate first last after depth requests rotation data valid rest ih =>
      exact ⟨inv, ih (complete_rotation_invariant first after rotation K data inv)⟩
  | @access first last requests request root decomposition data valid rest ih =>
      exact ⟨inv, convertHeap_invariant first.comparator.externalDepth _ first.next first.blocks inv,
        ih (afterAccess_invariant first request K decomposition data inv valid)⟩

theorem initialized_all_sources {n : ℕ} (initial comparator : BST 0 n) (K : ℤ)
    {last : Greedy.Execution.State n} {requests : List (Fin n)}
    (execution : Greedy.Execution.Run K (Greedy.Execution.initial initial comparator K) last requests) : AllSourcesInvariant execution :=
  all_sources_invariant execution (initial_invariant (Snapshot.ofTree comparator) _ K)

end Greedy.FamilyOrder
