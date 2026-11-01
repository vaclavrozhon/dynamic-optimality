import Greedy.OutgoingBounds

/-! Whole-run positive excess: eight ranges at winners and five at losers. -/

namespace Greedy.OutgoingExcess

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical Splay.Analysis
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.HeapAllocation
open GreedyMerge.ActualLinks GreedyMerge.PathPlateau GreedyMerge.PlateauBridge
open GreedyMerge.AccessSourceAccounting GreedyMerge.Fringe GreedyMerge.Fringe.Schedule

noncomputable def charge {n : ℕ} (metric : Metric) (K : ℤ) : InstanceCharge.Charge n :=
  fun {_} {comparator _ _} {p} data states _ side block =>
    if side then amount metric comparator.externalDepth (GreedyMerge.StateLabels.label comparator.externalDepth K states)
      (AtomOwner p.separator data.gapOwner) data.owner data.left block
    else amount metric comparator.externalDepth (GreedyMerge.StateLabels.label comparator.externalDepth K states)
      (AtomOwner p.separator data.gapOwner) data.owner data.right block

theorem local_bound_for_amount {n access lo hi : ℕ} (metric : Metric) {comparator oldTree newTree : BST 0 n}
    {p : Decomposition oldTree access} (data : AccessScheduleData comparator oldTree newTree p)
    (source : External n) (geometry : AccessTrace.Geometry data source)
    (initial : ℕ → ℤ) (tree : BST lo hi) (state : SideState)
    (view : SideView comparator.externalDepth initial (AtomOwner p.separator data.gapOwner) tree state)
    (projection : Projection (comparator.externalDepth ∘ AtomOwner p.separator data.gapOwner) data.owner tree)
    (localOwners : LocalOwners (comparator.externalDepth ∘ AtomOwner p.separator data.gapOwner) data.owner lo hi)
    (injective : Set.InjOn (AtomOwner p.separator data.gapOwner) {key | key ∈ atoms tree})
    (scheduleSubset : ∀ edge ∈ schedule data.owner tree, edge ∈ schedule data.owner data.left ++ schedule data.owner data.right)
    (block : Frozen) (member : block ∈ state.shrinking) (H : ℕ) (height : comparator.height ≤ H) :
    let value := amount metric comparator.externalDepth initial (AtomOwner p.separator data.gapOwner) data.owner tree block
    0 ≤ value ∧ value ≤ (4*((contractedGap H : ℤ)-1)) ∧
      (ClosedInstances.Small block → value ≤ range metric H) ∧
      (value ≠ 0 → ∃ event ∈ data.events, event.2.val ∈ ClosedInstances.keys block) := by
  have bound := spec metric view data.owner projection localOwners injective block member H
    (fun key _ _ => (externalDepth_le_height comparator _).trans height)
  refine ⟨bound.1, bound.2.1, bound.2.2.1, ?_⟩
  intro nonzero
  obtain ⟨edge, edgeMem, loser⟩ := bound.2.2.2 nonzero
  obtain ⟨event, eventMem, _, loserKey⟩ := AtomicAccess.event_of_atom data source geometry edge (scheduleSubset edge edgeMem)
  exact ⟨event, eventMem, loserKey.symm ▸ loser⟩

theorem actual_local_bound {n : ℕ} (metric : Metric) (before : Execution.State n) (request : Fin n) (H : ℕ)
    (root : before.comparator.HasRoot request.val)
    (decomposition : Decomposition before.refined.tree request.val)
    (data : AccessScheduleData before.comparator before.refined.tree (Execution.afterRefinement before request).tree decomposition)
    (valid : before.Valid) (height : before.comparator.height ≤ H)
    (side : Bool) (block : Frozen)
    (member : block ∈ (RunJournal.prepared before request (Execution.source request) side).shrinking) :
    InstanceCharge.LocalBound (charge metric (contractedGap H)) data (RunJournal.prepared before request)
      (Execution.source request) side block (range metric H) ((4*((contractedGap H : ℤ)-1))) := by
  have views := actual_allocated_sources before.comparator before.refined.tree _ decomposition data
    (Execution.source request) rfl (Execution.root_minimum _ request root) before.blocks valid.1 (contractedGap H) before.next valid.2.2.1
  have converted := convertRoot_eq_convertHeap before.comparator.externalDepth (Execution.source request) before.next before.blocks
  change convertRoot before.comparator.externalDepth (Execution.source request) _ _ before.blocks =
    RunJournal.prepared before request at converted
  dsimp only at views
  rw [converted] at views
  have geometry := AccessTrace.geometry data (Execution.source request) rfl (Execution.root_minimum _ request root)
  have upper := data.right.lower_le_upper
  cases side with
  | false =>
      obtain ⟨view⟩ := views.2
      exact local_bound_for_amount metric data (Execution.source request) geometry _ data.right _ view data.projection.2.2
        (fun q lower bound => data.localOwners q (by omega) bound)
        (WinnerTickets.record_injective data data.right (le_refl _))
        (fun _ edgeMem => List.mem_append_right _ edgeMem) block member H height
  | true =>
      obtain ⟨view⟩ := views.1
      exact local_bound_for_amount metric data (Execution.source request) geometry _ data.left _ view data.projection.2.1
        (fun q lower bound => data.localOwners q lower (by omega))
        (WinnerTickets.record_injective data data.left (by omega))
        (fun _ edgeMem => List.mem_append_left _ edgeMem) block member H height

theorem run_bounded {n : ℕ} (metric : Metric) (H : ℕ) {first last : Execution.State n} {requests : List (Fin n)}
    (execution : Execution.Run (contractedGap H) first last requests) (valid : first.Valid) (height : execution.Bounded H) :
    InstanceCharge.Bounded (charge metric (contractedGap H)) (range metric H) ((4*((contractedGap H : ℤ)-1))) execution := by
  induction execution with
  | done => trivial
  | rotate _ _ afterValid rest ih => exact ih afterValid height.2
  | @access first last requests request root decomposition data afterValid rest ih =>
      exact ⟨fun side block member => actual_local_bound metric first request H root decomposition data valid height.1 side block member,
        ih afterValid height.2⟩

theorem initialized_mass_bound {n : ℕ} (metric : Metric) (initial comparator : BST 0 n) (H : ℕ)
    {last : Execution.State n} {requests : List (Fin n)}
    (execution : Execution.Run (contractedGap H) (Execution.initial initial comparator (contractedGap H)) last requests)
    (height : execution.Bounded H) :
    InstanceCharge.mass (charge metric (contractedGap H)) execution ≤
      ((4*((contractedGap H : ℤ)-1)) + range metric H) * (2*(2*n+1) + execution.births : ℕ) :=
  InstanceCharge.initialized_mass_bound (charge metric (contractedGap H)) _ _ (range_nonneg metric H) (by have h := DepartureAmounts.range_nonneg .increase H; change 0 ≤ (contractedGap H : ℤ)-1 at h; omega)
    initial comparator (contractedGap H) execution (run_bounded metric H execution (Execution.initial_valid initial comparator _) height)

theorem initialized_combined_bound {n : ℕ} (initial comparator : BST 0 n) (H : ℕ)
    {last : Execution.State n} {requests : List (Fin n)}
    (execution : Execution.Run (contractedGap H) (Execution.initial initial comparator (contractedGap H)) last requests)
    (height : execution.Bounded H) :
    InstanceCharge.mass (charge .nonrootWinner (contractedGap H)) execution +
      InstanceCharge.mass (charge .rootLoser (contractedGap H)) execution ≤
      13*((contractedGap H : ℤ)-1) * (2*(2*n+1) + execution.births : ℕ) := by
  have winner := initialized_mass_bound .nonrootWinner initial comparator H execution height
  have loser := initialized_mass_bound .rootLoser initial comparator H execution height
  simp only [range] at winner loser
  linarith

end Greedy.OutgoingExcess

