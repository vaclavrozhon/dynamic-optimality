import Greedy.LiteralPhaseSum
import Greedy.RunFamilyOrder

/-! Each actual source fragment has the signed fringe bound of three. -/

namespace Greedy.CreatorPhase

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.HeapAllocation
open GreedyMerge.ActualLinks GreedyMerge.PathPlateau GreedyMerge.PlateauBridge
open GreedyMerge.AccessSourceAccounting GreedyMerge.Fringe GreedyMerge.Fringe.Schedule

noncomputable def part {n access : ℕ} {comparator oldTree newTree : BST 0 n}
    {p : Decomposition oldTree access} (data : AccessScheduleData comparator oldTree newTree p)
    (states : HeapSides n) (source : External n) (side : Bool) (block : Frozen) (time : ℕ) : ℤ :=
  if side then coefficient (states source side) block (AtomOwner p.separator data.gapOwner) data.owner data.left time
  else coefficient (states source side) block (AtomOwner p.separator data.gapOwner) data.owner data.right time

theorem part_nonzero_crosses {n access : ℕ} {comparator oldTree newTree : BST 0 n}
    {p : Decomposition oldTree access} (data : AccessScheduleData comparator oldTree newTree p)
    (states : HeapSides n) (source : External n) (side : Bool) (block : Frozen) (time : ℕ)
    (valid : Valid source.val side (states source side)) (member : block ∈ (states source side).shrinking)
    (nonzero : part data states source side block time ≠ 0) :
    GreedyForest.Straddles (fun joined => decide (time+1 ≤ joined)) (GreedyMerge.FrozenHistory.joins block) := by
  cases side <;> exact coefficient_nonzero_crosses _ _ _ _ _ _ _ valid member time nonzero

theorem record_monotone {n access lo hi : ℕ} {comparator oldTree newTree : BST 0 n}
    {p : Decomposition oldTree access} (data : AccessScheduleData comparator oldTree newTree p)
    (tree : BST lo hi) (upper : hi ≤ p.count) :
    ∀ first ∈ atoms tree, ∀ second ∈ atoms tree, first ≤ second →
      AtomOwner p.separator data.gapOwner first ≤ AtomOwner p.separator data.gapOwner second := by
  intro first firstMem second secondMem less
  have firstBound := (atoms_mem_iff tree first).mp firstMem
  have secondBound := (atoms_mem_iff tree second).mp secondMem
  rcases eq_or_lt_of_le less with rfl | strict
  · rfl
  · exact (GreedyMerge.MappedConsolidation.atom_owner_lt_iff comparator p data.gapOwner data.minima
      (by omega) (by omega)).mpr strict |>.le

theorem prepared_ready {n : ℕ} (before : Execution.State n) (request : Fin n)
    (valid : before.Valid) : Ready before.comparator before.refined.tree (RunJournal.prepared before request) := by
  unfold RunJournal.prepared
  rw [← convertRoot_eq_convertHeap]
  exact convertRoot_ready before.comparator before.refined.tree (Execution.source request) _ _ before.blocks valid.1

theorem prepared_part_bound {n : ℕ} (before : Execution.State n) (request : Fin n) (K : ℤ)
    (decomposition : Decomposition before.refined.tree request.val)
    (data : AccessScheduleData before.comparator before.refined.tree
      (Execution.afterRefinement before request).tree decomposition)
    (valid : before.Valid) (root : before.comparator.HasRoot request.val)
    (inv : FamilyOrder.Invariant before.clock before.next before.blocks)
    (side : Bool) (block : Frozen)
    (member : block ∈ (RunJournal.prepared before request (Execution.source request) side).shrinking) (time : ℕ) :
    |part data (RunJournal.prepared before request) (Execution.source request) side block time| ≤ 3 := by
  have views := actual_allocated_sources before.comparator before.refined.tree _ decomposition data
    (Execution.source request) rfl (Execution.root_minimum _ request root) before.blocks valid.1 K before.next inv.ids
  have converted := convertRoot_eq_convertHeap before.comparator.externalDepth (Execution.source request) before.next before.blocks
  change convertRoot before.comparator.externalDepth (Execution.source request) _ _ before.blocks =
    RunJournal.prepared before request at converted
  dsimp only at views
  rw [converted] at views
  have ready := prepared_ready before request valid
  have prepared := FamilyOrder.convertHeap_invariant before.comparator.externalDepth
    (fun owner _ => decide (owner = Execution.source request)) before.next before.blocks inv
  have history := (prepared.ordered.localOrder (encode n (Execution.source request, side))).2 block
    (by simpa [table, RunJournal.prepared] using member)
  have upper := data.right.lower_le_upper
  cases side with
  | false =>
      obtain ⟨view⟩ := views.2
      apply coefficient_bound view (Execution.source request).val false (ready.valid _ false)
        (record_monotone data data.right (le_refl _)) data.owner data.projection.2.2 _ block member history time
      intro q lower bound
      exact data.localOwners q (by omega) bound
  | true =>
      obtain ⟨view⟩ := views.1
      apply coefficient_bound view (Execution.source request).val true (ready.valid _ true)
        (record_monotone data data.left (by omega)) data.owner data.projection.2.1 _ block member history time
      intro q lower bound
      exact data.localOwners q lower (by omega)

end Greedy.CreatorPhase
