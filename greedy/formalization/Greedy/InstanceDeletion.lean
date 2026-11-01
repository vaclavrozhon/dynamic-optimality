import Greedy.InstanceCollapse
import Greedy.AccessTrace
import ActualSourceDeletion

/-! Once the last record of a frozen instance loses, that instance stays empty. -/

namespace Greedy.ClosedInstances

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.HeapAllocation
open GreedyMerge.ActualLinks GreedyMerge.PathPlateau GreedyMerge.FrozenHistory

theorem instance_unique {slots next : ℕ} (states : Fin slots → SideState)
    (inventory : GreedyMerge.FreshIds.Inventory states next)
    (firstSlot secondSlot : Fin slots) (first second : Frozen)
    (firstMem : first ∈ (states firstSlot).shrinking) (secondMem : second ∈ (states secondSlot).shrinking)
    (same : first.id = second.id) : firstSlot = secondSlot ∧ first = second := by
  have location := inventory.locations firstSlot secondSlot first.id
    (List.mem_append_left _ (List.mem_map.mpr ⟨first, firstMem, rfl⟩))
    (List.mem_append_left _ (List.mem_map.mpr ⟨second, secondMem, same.symm⟩))
  subst secondSlot
  exact ⟨rfl, List.inj_on_of_nodup_map (List.nodup_append.mp (inventory.localUnique firstSlot)).1 firstMem secondMem same⟩

def Empty (block : Frozen) : Prop := keys block = ∅

theorem empty_hereditary : ClosedFamilies.Hereditary Empty := by
  intro before after descendant empty
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro key present
  have old := keys_subset descendant present
  rw [empty] at old
  exact Finset.notMem_empty _ old

theorem keys_closed {n next : ℕ} (states : HeapSides n) (inventory : HeapInventory states next)
    (source : External n) (side : Bool) (block : Frozen)
    (member : block ∈ (states source side).shrinking) :
    HeapClosed block.id (fun fragment => keys fragment ⊆ keys block) states := by
  apply instance_closed (table states) inventory (encode n (source, side)) block (by simpa [table] using member)
  intro slot fragment present same
  have unique := instance_unique (table states) inventory slot (encode n (source, side)) fragment block present
    (by simpa [table] using member) same
  rw [unique.2]

theorem completed_loser_absent {n access : ℕ} {comparator oldTree newTree : BST 0 n}
    {p : Decomposition oldTree access} (data : AccessScheduleData comparator oldTree newTree p)
    (source : External n) (real : source.val = 2*access+1) (zero : (Snapshot.ofTree comparator).rank source = 0)
    (geometry : AccessTrace.Geometry data source) (states : HeapSides n) (ready : Ready comparator newTree states)
    (event : External n × External n) (eventMem : event ∈ data.events)
    (side : Bool) (block : Frozen) (member : block ∈ (states source side).shrinking) :
    event.2.val ∉ keys block := by
  intro present
  obtain ⟨entry, entryMem, same⟩ := List.mem_map.mp (List.mem_toFinset.mp present)
  have survivor := ClosedFamilies.completed_source_key data source real zero states ready side entry
    (ClosedFamilies.frozen_entry_mem _ block member entry entryMem)
  have survivorMem : event.2.val ∈ AccessTrace.survivors data := by
    rw [← same, survivor]
    cases side <;> simp [AccessTrace.survivors]
  have absent := (GreedyMerge.HistoryProcess.run_survivor_iff geometry.run geometry.unique event.2.val).mp survivorMem
  apply absent.2
  exact List.mem_map.mpr ⟨eventKeys event, List.mem_map.mpr ⟨event, eventMem, rfl⟩, rfl⟩

theorem runLinks_empty_of_small {n access next : ℕ} {comparator oldTree newTree : BST 0 n}
    {p : Decomposition oldTree access} (data : AccessScheduleData comparator oldTree newTree p)
    (source : External n) (real : source.val = 2*access+1) (zero : (Snapshot.ofTree comparator).rank source = 0)
    (geometry : AccessTrace.Geometry data source)
    (sourceSide : External n × External n → Bool) (reader : ℕ → States n → ℕ → ℤ)
    (clock : ℕ) (states : HeapSides n) (inventory : HeapInventory states next)
    (ready : Ready comparator newTree (runLinks source sourceSide reader clock states data.events))
    (side : Bool) (block : Frozen) (member : block ∈ (states source side).shrinking)
    (small : Small block) (event : External n × External n) (eventMem : event ∈ data.events)
    (loser : event.2.val ∈ keys block) :
    HeapClosed block.id Empty (runLinks source sourceSide reader clock states data.events) := by
  have closed := runLinks_closed source sourceSide reader clock states data.events
    (keys_closed states inventory source side block member)
    (by intro _ _ descendant subset; exact (keys_subset descendant).trans subset)
  apply closed.with_property Empty
  intro slot fragment fragmentMem same
  have subset := closed.frozen slot fragment fragmentMem same
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro key present
  have equal : key = event.2.val := Finset.card_le_one.mp small key (subset present) event.2.val loser
  let owner := ((encode n).symm slot).1
  let direction := ((encode n).symm slot).2
  change fragment ∈ (runLinks source sourceSide reader clock states data.events owner direction).shrinking at fragmentMem
  have oldId : block.id ∈ liveIds (states owner direction) := by
    rw [← runLinks_liveIds source sourceSide reader clock states data.events owner direction]
    exact List.mem_append_left _ (List.mem_map.mpr ⟨fragment, fragmentMem, same⟩)
  have location := inventory.locations slot (encode n (source, side)) block.id oldId
    (by simp only [table, Equiv.symm_apply_apply]; exact List.mem_append_left _ (List.mem_map.mpr ⟨block, member, rfl⟩))
  have ownerEq : owner = source := by dsimp only [owner]; rw [location]; simp
  exact completed_loser_absent data source real zero geometry _ ready event eventMem direction fragment
    (by simpa only [ownerEq] using fragmentMem) (equal ▸ present)

theorem afterAccess_empty_of_small {n : ℕ} (before : Execution.State n) (request : Fin n) (K : ℤ)
    (root : before.comparator.HasRoot request.val)
    (decomposition : Decomposition before.refined.tree request.val)
    (data : AccessScheduleData before.comparator before.refined.tree (Execution.afterRefinement before request).tree decomposition)
    (valid : before.Valid) (afterValid : (Execution.afterAccess before request K decomposition data).Valid)
    (side : Bool) (block : Frozen)
    (member : block ∈ (RunJournal.prepared before request (Execution.source request) side).shrinking)
    (small : Small block) (event : External n × External n) (eventMem : event ∈ data.events)
    (loser : event.2.val ∈ keys block) :
    HeapClosed block.id Empty (Execution.afterAccess before request K decomposition data).blocks ∧
      block.id < (Execution.afterAccess before request K decomposition data).next := by
  have global := Execution.root_minimum _ request root
  refine ⟨runLinks_empty_of_small data (Execution.source request) rfl
    (GreedyMerge.AccessFrontier.comparator_zero_of_global _ global) (AccessTrace.geometry data _ rfl global)
    _ _ before.clock (RunJournal.prepared before request)
    (convertHeap_inventory _ _ _ _ valid.2.2.1) afterValid.1 side block member small event eventMem loser,
    (afterAccess_small before request K root decomposition data valid afterValid side block member).2⟩

end Greedy.ClosedInstances
