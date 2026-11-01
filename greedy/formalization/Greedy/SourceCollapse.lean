import Greedy.ClosedCuts
import AccessSourceAccounting

/-! A completed access leaves at most one entry on each source side. -/

namespace Greedy.ClosedFamilies

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.HeapAllocation
open GreedyMerge.ActualLinks GreedyMerge.PathPlateau GreedyMerge.AccessSurvivors
open GreedyMerge.AccessSourceAccounting GreedyMerge.Fringe GreedyMerge.Fringe.Schedule
open GreedyMerge.PlateauBridge GreedyMerge.FrozenHistory

theorem completed_source_key {n access : ℕ} {comparator oldTree newTree : BST 0 n}
    {p : Decomposition oldTree access} (data : AccessScheduleData comparator oldTree newTree p)
    (source : External n) (real : source.val = 2*access+1)
    (zero : (Snapshot.ofTree comparator).rank source = 0)
    (states : HeapSides n) (ready : Ready comparator newTree states) (side : Bool)
    (entry : Entry) (member : entry ∈ entries (states source side)) :
    entry.key = AtomOwner p.separator data.gapOwner
      (if side then treeOwner data.owner data.left else treeOwner data.owner data.right) := by
  have child := (ready_side_keys comparator newTree states ready source side entry.key).mp
    (List.mem_map.mpr ⟨entry, member, rfl⟩)
  have pair := (hasChild_iff_hasPair ..).mp child.1
  rw [data.expansion] at pair
  have cases := (expanded_root_children comparator p data.gapOwner data.owner data.minima
    data.left data.right data.projection data.atAccess source real zero entry.key).mp pair
  have leftBounds := treeOwner_bounds _ data.owner data.left data.projection.2.1
  have rightBounds := treeOwner_bounds _ data.owner data.right data.projection.2.2
  have leftLess := atom_left_of_source data source real _
    (List.mem_map.mpr ⟨_, (atoms_mem_iff data.left _).mpr leftBounds, rfl⟩)
  have rightGreater := atom_right_of_source data source real _
    (List.mem_map.mpr ⟨_, (atoms_mem_iff data.right _).mpr rightBounds, rfl⟩)
  cases side <;> simp only [Bool.false_eq_true, if_false, if_true] at child ⊢ <;>
    rcases cases with left | right <;> omega

theorem valid_keys_unique {owner : ℕ} {side : Bool} {state : SideState}
    (valid : Valid owner side state) : ((entries state).map Entry.key).Nodup := by
  have sorted := GreedyMerge.SourceSideStates.increasingKeys_sorted valid
  have unique : (GreedyMerge.SourceSideStates.increasingKeys side state).Nodup :=
    sorted.imp (fun less => Nat.ne_of_lt less)
  cases side <;> simpa only [GreedyMerge.SourceSideStates.increasingKeys,
    Bool.false_eq_true, if_false, if_true, List.nodup_reverse] using unique

theorem frozen_entry_mem (state : SideState) (block : Frozen) (member : block ∈ state.shrinking)
    (entry : Entry) (entryMem : entry ∈ block.members) : entry ∈ entries state :=
  List.mem_append_left _ (List.mem_flatMap.mpr ⟨block, member, entryMem⟩)

theorem completed_source_avoids {n access : ℕ} {comparator oldTree newTree : BST 0 n}
    {p : Decomposition oldTree access} (data : AccessScheduleData comparator oldTree newTree p)
    (source : External n) (real : source.val = 2*access+1)
    (zero : (Snapshot.ofTree comparator).rank source = 0)
    (states : HeapSides n) (ready : Ready comparator newTree states) (side : Bool)
    (block : Frozen) (member : block ∈ (states source side).shrinking) (cut : ℕ) : AvoidsCut cut block := by
  intro crosses
  obtain ⟨early, earlyMem, late, lateMem, below, above⟩ :=
    (GreedyForest.straddles_nat_cut_iff cut (joins block)).mp crosses
  obtain ⟨first, firstMem, firstTime⟩ := List.mem_map.mp (List.mem_toFinset.mp earlyMem)
  obtain ⟨second, secondMem, secondTime⟩ := List.mem_map.mp (List.mem_toFinset.mp lateMem)
  have firstEntry := frozen_entry_mem (states source side) block member first firstMem
  have secondEntry := frozen_entry_mem (states source side) block member second secondMem
  have sameKey := (completed_source_key data source real zero states ready side first firstEntry).trans
    (completed_source_key data source real zero states ready side second secondEntry).symm
  have same := List.inj_on_of_nodup_map (valid_keys_unique (ready.valid source side)) firstEntry secondEntry sameKey
  have sameTime := congrArg Entry.joined same
  omega

end Greedy.ClosedFamilies
