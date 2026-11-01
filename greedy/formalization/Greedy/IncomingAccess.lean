import Greedy.IncomingExcess
import Greedy.AtomicAccess
import Greedy.InstanceBudget

/-! Instantiate incoming excess with the actual two-sided access schedule. -/

namespace Greedy.IncomingExcess

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical Splay.Analysis
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.HeapAllocation
open GreedyMerge.ActualLinks GreedyMerge.PathPlateau GreedyMerge.PlateauBridge
open GreedyMerge.AccessSourceAccounting GreedyMerge.Fringe GreedyMerge.Fringe.Schedule
open GreedyForest.Phase

noncomputable def charge {n : ℕ} (K : ℤ) : InstanceCharge.Charge n :=
  fun {access} {comparator oldTree newTree} {p} data states source side block =>
    if side then amount comparator.externalDepth (GreedyMerge.StateLabels.label comparator.externalDepth K states)
      (AtomOwner p.separator data.gapOwner) data.owner data.left block
    else amount comparator.externalDepth (GreedyMerge.StateLabels.label comparator.externalDepth K states)
      (AtomOwner p.separator data.gapOwner) data.owner data.right block

theorem view_label_bounds {lo hi : ℕ} {rank : ℕ → ℕ} {initial : ℕ → ℤ} {record : ℕ → ℕ}
    {tree : BST lo hi} {state : SideState} (view : SideView rank initial record tree state)
    (H : ℕ) (ranks : ∀ key, 2*lo ≤ key → key ≤ 2*hi → rank (record key) ≤ H) :
    ∀ key ∈ atoms tree, 1 ≤ initial (record key) ∧ initial (record key) ≤ contractedGap H := by
  intro key member
  have bounds := (atoms_mem_iff tree key).mp member
  have same := view.partition.initialBucket key bounds.1 bounds.2
  change initial (record key) = _ at same
  rw [same]
  exact baseLabel_bounds (rank ∘ record) _ H key (ranks key bounds.1 bounds.2)

theorem local_bound_for_amount {n access lo hi : ℕ} {comparator oldTree newTree : BST 0 n}
    {p : Decomposition oldTree access} (data : AccessScheduleData comparator oldTree newTree p)
    (source : External n) (geometry : AccessTrace.Geometry data source)
    (initial : ℕ → ℤ) (tree : BST lo hi) (state : SideState)
    (view : SideView comparator.externalDepth initial (AtomOwner p.separator data.gapOwner) tree state)
    (projection : Projection (comparator.externalDepth ∘ AtomOwner p.separator data.gapOwner) data.owner tree)
    (localOwners : LocalOwners (comparator.externalDepth ∘ AtomOwner p.separator data.gapOwner) data.owner lo hi)
    (injective : Set.InjOn (AtomOwner p.separator data.gapOwner) {key | key ∈ atoms tree})
    (scheduleSubset : ∀ edge ∈ schedule data.owner tree, edge ∈ schedule data.owner data.left ++ schedule data.owner data.right)
    (block : Frozen) (member : block ∈ state.shrinking) (H : ℕ) (height : comparator.height ≤ H) :
    let value := amount comparator.externalDepth initial (AtomOwner p.separator data.gapOwner) data.owner tree block
    0 ≤ value ∧ value ≤ 3*((contractedGap H : ℤ)-1) ∧
      (ClosedInstances.Small block → value ≤ (contractedGap H : ℤ)-1) ∧
      (value ≠ 0 → ∃ event ∈ data.events, event.2.val ∈ ClosedInstances.keys block) := by
  have ranks : ∀ key, 2*lo ≤ key → key ≤ 2*hi → comparator.externalDepth (AtomOwner p.separator data.gapOwner key) ≤ H :=
    fun key _ _ => (externalDepth_le_height comparator _).trans height
  refine ⟨amount_nonneg _ _ _ _ _ _, first_bound view data.owner projection localOwners block member H ranks, ?_, ?_⟩
  · intro small
    exact small_bound _ _ _ _ tree projection localOwners injective block small (contractedGap H)
      (by unfold contractedGap; omega) (view_label_bounds view H ranks)
  · intro nonzero
    obtain ⟨edge, edgeMem, loser⟩ := amount_loser _ _ _ _ tree block nonzero
    obtain ⟨event, eventMem, _, loserKey⟩ := AtomicAccess.event_of_atom data source geometry edge (scheduleSubset edge edgeMem)
    exact ⟨event, eventMem, loserKey.symm ▸ loser⟩

theorem actual_local_bound {n : ℕ} (before : Execution.State n) (request : Fin n) (H : ℕ)
    (root : before.comparator.HasRoot request.val)
    (decomposition : Decomposition before.refined.tree request.val)
    (data : AccessScheduleData before.comparator before.refined.tree (Execution.afterRefinement before request).tree decomposition)
    (valid : before.Valid) (height : before.comparator.height ≤ H)
    (side : Bool) (block : Frozen)
    (member : block ∈ (RunJournal.prepared before request (Execution.source request) side).shrinking) :
    InstanceCharge.LocalBound (charge (contractedGap H)) data (RunJournal.prepared before request)
      (Execution.source request) side block ((contractedGap H : ℤ)-1) (3*((contractedGap H : ℤ)-1)) := by
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
      exact local_bound_for_amount data (Execution.source request) geometry _ data.right _ view data.projection.2.2
        (fun q lower bound => data.localOwners q (by omega) bound)
        (WinnerTickets.record_injective data data.right (le_refl _))
        (fun _ edgeMem => List.mem_append_right _ edgeMem) block member H height
  | true =>
      obtain ⟨view⟩ := views.1
      exact local_bound_for_amount data (Execution.source request) geometry _ data.left _ view data.projection.2.1
        (fun q lower bound => data.localOwners q lower (by omega))
        (WinnerTickets.record_injective data data.left (by omega))
        (fun _ edgeMem => List.mem_append_left _ edgeMem) block member H height

theorem run_bounded {n : ℕ} (H : ℕ) {first last : Execution.State n} {requests : List (Fin n)}
    (execution : Execution.Run (contractedGap H) first last requests) (valid : first.Valid) (height : execution.Bounded H) :
    InstanceCharge.Bounded (charge (contractedGap H)) ((contractedGap H : ℤ)-1) (3*((contractedGap H : ℤ)-1)) execution := by
  induction execution with
  | done => trivial
  | rotate _ _ afterValid rest ih => exact ih afterValid height.2
  | @access first last requests request root decomposition data afterValid rest ih =>
      exact ⟨fun side block member => actual_local_bound first request H root decomposition data valid height.1 side block member,
        ih afterValid height.2⟩

theorem initialized_mass_bound {n : ℕ} (initial comparator : BST 0 n) (H : ℕ)
    {last : Execution.State n} {requests : List (Fin n)}
    (execution : Execution.Run (contractedGap H) (Execution.initial initial comparator (contractedGap H)) last requests)
    (height : execution.Bounded H) :
    InstanceCharge.mass (charge (contractedGap H)) execution ≤
      4*((contractedGap H : ℤ)-1) * (2*(2*n+1) + execution.births : ℕ) := by
  have range : 0 ≤ (contractedGap H : ℤ)-1 := by unfold contractedGap; omega
  have bound := InstanceCharge.initialized_mass_bound (charge (contractedGap H)) _ _ range (by omega)
    initial comparator (contractedGap H) execution (run_bounded H execution (Execution.initial_valid initial comparator _) height)
  convert bound using 1 <;> ring

end Greedy.IncomingExcess
