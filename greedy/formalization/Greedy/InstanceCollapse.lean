import Greedy.RunClosedInstances
import Greedy.SourceCollapse

/-! A processed frozen instance has at most one remaining physical record. -/

namespace Greedy.ClosedInstances

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.HeapAllocation
open GreedyMerge.ActualLinks GreedyMerge.PathPlateau GreedyMerge.FrozenHistory

def keys (block : Frozen) : Finset ℕ := (block.members.map Entry.key).toFinset

def Small (block : Frozen) : Prop := (keys block).card ≤ 1

theorem keys_subset {before after : Frozen} (descendant : Descends after before) : keys after ⊆ keys before := by
  intro key member
  obtain ⟨entry, entryMem, same⟩ := List.mem_map.mp (List.mem_toFinset.mp member)
  exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨entry, descendant.2.2.subset entryMem, same⟩)

theorem small_hereditary : ClosedFamilies.Hereditary Small := by
  intro before after descendant small
  exact (Finset.card_le_card (keys_subset descendant)).trans small

theorem completed_source_small {n access : ℕ} {comparator oldTree newTree : BST 0 n}
    {p : Decomposition oldTree access} (data : AccessScheduleData comparator oldTree newTree p)
    (source : External n) (real : source.val = 2*access+1) (zero : (Snapshot.ofTree comparator).rank source = 0)
    (states : HeapSides n) (ready : Ready comparator newTree states) (side : Bool)
    (block : Frozen) (member : block ∈ (states source side).shrinking) : Small block := by
  apply Finset.card_le_one.mpr
  intro first firstMem second secondMem
  obtain ⟨a, aMem, aKey⟩ := List.mem_map.mp (List.mem_toFinset.mp firstMem)
  obtain ⟨b, bMem, bKey⟩ := List.mem_map.mp (List.mem_toFinset.mp secondMem)
  have firstEqual := ClosedFamilies.completed_source_key data source real zero states ready side a
    (ClosedFamilies.frozen_entry_mem (states source side) block member a aMem)
  have secondEqual := ClosedFamilies.completed_source_key data source real zero states ready side b
    (ClosedFamilies.frozen_entry_mem (states source side) block member b bMem)
  exact aKey.symm.trans (firstEqual.trans (secondEqual.symm.trans bKey))

theorem runLinks_small {n access clock next : ℕ} {comparator oldTree newTree : BST 0 n}
    {p : Decomposition oldTree access} (data : AccessScheduleData comparator oldTree newTree p)
    (source : External n) (real : source.val = 2*access+1) (zero : (Snapshot.ofTree comparator).rank source = 0)
    (sourceSide : External n × External n → Bool) (reader : ℕ → States n → ℕ → ℤ)
    (states : HeapSides n) (inventory : HeapInventory states next)
    (ready : Ready comparator newTree (runLinks source sourceSide reader clock states data.events))
    (side : Bool) (block : Frozen) (member : block ∈ (states source side).shrinking) :
    HeapClosed block.id Small (runLinks source sourceSide reader clock states data.events) := by
  have closed : HeapClosed block.id (fun _ => True) states :=
    instance_closed (table states) inventory (encode n (source, side)) block
      (by simpa [table] using member) (fun _ => True) (by intros; trivial)
  have after := runLinks_closed source sourceSide reader clock states data.events closed (by intro _ _ _ _; trivial)
  apply after.with_property Small
  intro slot fragment fragmentMem same
  let owner := ((encode n).symm slot).1
  let direction := ((encode n).symm slot).2
  change fragment ∈ (runLinks source sourceSide reader clock states data.events owner direction).shrinking at fragmentMem
  have actualId : block.id ∈ liveIds (states owner direction) := by
    rw [← runLinks_liveIds source sourceSide reader clock states data.events owner direction]
    exact List.mem_append_left _ (List.mem_map.mpr ⟨fragment, fragmentMem, same⟩)
  have location := inventory.locations slot (encode n (source, side)) block.id actualId
    (by simp only [table, Equiv.symm_apply_apply]; exact List.mem_append_left _ (List.mem_map.mpr ⟨block, member, rfl⟩))
  have ownerEq : owner = source := by
    dsimp only [owner]
    rw [location]
    simp
  exact completed_source_small data source real zero _ ready direction fragment (by simpa only [ownerEq] using fragmentMem)

theorem afterAccess_small {n : ℕ} (before : Execution.State n) (request : Fin n) (K : ℤ)
    (root : before.comparator.HasRoot request.val)
    (decomposition : Decomposition before.refined.tree request.val)
    (data : AccessScheduleData before.comparator before.refined.tree (Execution.afterRefinement before request).tree decomposition)
    (valid : before.Valid) (afterValid : (Execution.afterAccess before request K decomposition data).Valid)
    (side : Bool) (block : Frozen)
    (member : block ∈ (RunJournal.prepared before request (Execution.source request) side).shrinking) :
    HeapClosed block.id Small (Execution.afterAccess before request K decomposition data).blocks ∧
      block.id < (Execution.afterAccess before request K decomposition data).next := by
  have prepared := convertHeap_inventory before.comparator.externalDepth
    (fun owner _ => decide (owner = Execution.source request)) before.next before.blocks valid.2.2.1
  have zero : (Snapshot.ofTree before.comparator).rank (Execution.source request) = 0 :=
    GreedyMerge.AccessFrontier.comparator_zero_of_global before.comparator (Execution.root_minimum _ request root)
  refine ⟨runLinks_small data (Execution.source request) rfl zero _ _
    (RunJournal.prepared before request) prepared afterValid.1 side block member, ?_⟩
  have past := prepared.below (encode n (Execution.source request, side)) block.id
    (by simp only [table, Equiv.symm_apply_apply]
        exact List.mem_append_left _ (List.mem_map.mpr ⟨block, member, rfl⟩))
  simpa only [GreedyMerge.ActualLinks.convertHeap_next, Execution.afterAccess] using past

theorem remaining_sources_small {n : ℕ} (before : Execution.State n) (request : Fin n) (K : ℤ)
    (root : before.comparator.HasRoot request.val)
    (decomposition : Decomposition before.refined.tree request.val)
    (data : AccessScheduleData before.comparator before.refined.tree (Execution.afterRefinement before request).tree decomposition)
    (valid : before.Valid) (afterValid : (Execution.afterAccess before request K decomposition data).Valid)
    {last : Execution.State n} {requests : List (Fin n)}
    (rest : Execution.Run K (Execution.afterAccess before request K decomposition data) last requests)
    (side : Bool) (block : Frozen)
    (member : block ∈ (RunJournal.prepared before request (Execution.source request) side).shrinking) :
    AllSourcesClosed (id := block.id) Small rest := by
  have small := afterAccess_small before request K root decomposition data valid afterValid side block member
  exact all_sources_closed rest small.1 small_hereditary small.2

end Greedy.ClosedInstances
