import Greedy.SourceClasses
import Greedy.SourceMemories
import Greedy.PhaseShiftTelescope

/-! Signed creator differences are the differences of the live journal memories. -/

namespace Greedy.LiveMemory

open Splay.Rank GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.ActualLinks

noncomputable def atKey {n : ℕ} (memory : External n → ℤ) (key : ℕ) : ℤ :=
  if bound : key < 2*n+1 then memory ⟨key, bound⟩ else 0

@[simp] theorem atKey_record {n : ℕ} (memory : External n → ℤ) (record : External n) :
    atKey memory record.val = memory record := by simp [atKey, record.isLt]

theorem frozen_creator {n : ℕ} (parent : Parents n) (states : States n)
    (sound : SoundFor parent states) (ordered : Ordered states)
    (memory : External n → ℤ) (synced : Synced memory states)
    (owner : External n) (side : Bool) (block : Frozen) (member : block ∈ (states owner side).shrinking)
    (key : ℕ) (contains : key ∈ GreedyMerge.ActualBlockPartition.blockKeys block) :
    CreatorPhase.storedCreatorLabel (states owner side) key = atKey memory key := by
  obtain ⟨entry, entryMem, keyEq⟩ := List.mem_map.mp contains
  have actual := ClosedFamilies.frozen_entry_mem _ block member entry entryMem
  obtain ⟨record, recordKey, _⟩ := sound owner side entry actual
  rw [← keyEq, CreatorPhase.storedCreatorLabel_of_frozen _ owner.val side (ordered owner side) block member entry entryMem]
  rw [← recordKey, atKey_record]
  exact (synced.entry owner side entry actual record recordKey).symm

end Greedy.LiveMemory

namespace Greedy.SourceCensus

open Splay.Tree Splay.Tree.BST Splay.Rank
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.ActualBlockPartition
open GreedyMerge.HeapAllocation GreedyMerge.ActualLinks
open GreedyMerge.Fringe GreedyMerge.Fringe.Schedule GreedyMerge.AccessSourceAccounting
open GreedyForest.Phase
open scoped BigOperators

noncomputable local instance creatorMemoryFrozenDecidableEq : DecidableEq Frozen := Classical.decEq _
attribute [local instance] Classical.propDecidable

theorem sum_internal_value {n lo hi : ℕ} {rank : ℕ → ℕ} {initial : ℕ → ℤ} {record : ℕ → ℕ}
    {tree : BST lo hi} (states : HeapSides n) (source : External n) (side : Bool)
    (valid : ∀ direction, Valid source.val direction (states source direction))
    (view : SideView rank initial record tree (states source side))
    (ids : ((states source side).shrinking.map Frozen.id).Nodup)
    (loser : ℕ) (loserMem : loser ∈ atoms tree) (winner : ℕ) (value : ℤ) :
    (∑ block ∈ (states source side).shrinking.toFinset,
      if winner ∈ blockKeys block ∧ record loser ∈ blockKeys block then value else 0) =
      if SameBlockKeys states source (winner, record loser) then value else 0 := by
  classical
  obtain ⟨block, member, contains⟩ := view.covered loser loserMem
  rw [Finset.sum_eq_single block]
  · have same := sameBlock_iff_containing states source side valid view ids loser loserMem winner block member contains
    simp only [contains, and_true, same]
  · intro other otherMem different
    apply if_neg
    intro both
    exact different (unique_block view ids loser loserMem other block (List.mem_toFinset.mp otherMem) member both.2 contains)
  · intro absent
    exact False.elim (absent (List.mem_toFinset.mpr member))

noncomputable def memoryWeight {n : ℕ} (states : HeapSides n) (source : External n)
    (memory : ℕ → ℤ) (edge : ℕ × ℕ) : ℤ :=
  if SameBlockKeys states source edge then memory edge.2 - memory edge.1 else 0

theorem memory_side_sum {n lo hi : ℕ} {rank : ℕ → ℕ} {initial : ℕ → ℤ} {record : ℕ → ℕ}
    {tree : BST lo hi} (parent : Parents n) (states : HeapSides n) (source : External n) (side : Bool)
    (sound : SoundFor parent states) (ordered : Ordered states)
    (view : SideView rank initial record tree (states source side))
    (ids : ((states source side).shrinking.map Frozen.id).Nodup)
    (owner : ℕ → ℕ) (projection : Projection (rank ∘ record) owner tree)
    (localOwners : LocalOwners (rank ∘ record) owner lo hi)
    (memory : External n → ℤ) (synced : LiveMemory.Synced memory states) :
    (∑ block ∈ (states source side).shrinking.toFinset,
      CreatorPhase.shiftCoefficient (states source side) block record owner tree) =
      ∑ i : Fin (schedule owner tree).length,
        memoryWeight states source (LiveMemory.atKey memory)
          (record ((schedule owner tree).get i).1, record ((schedule owner tree).get i).2) := by
  classical
  have actualRun := schedule_run (rank ∘ record) owner tree projection localOwners
  have unique := run_events_nodup actualRun (atoms_nodup tree)
  rw [AtomicAccess.indexed_toFinset _ unique
    (fun edge => memoryWeight states source (LiveMemory.atKey memory) (record edge.1, record edge.2))]
  unfold CreatorPhase.shiftCoefficient
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro edge edgeMem
  have each (block : Frozen) (member : block ∈ (states source side).shrinking.toFinset) :
      CreatorPhase.shiftWeight (states source side) block record edge =
        if record edge.1 ∈ blockKeys block ∧ record edge.2 ∈ blockKeys block then
          LiveMemory.atKey memory (record edge.2) - LiveMemory.atKey memory (record edge.1) else 0 := by
    unfold CreatorPhase.shiftWeight
    split_ifs with both
    · rw [LiveMemory.frozen_creator parent states sound ordered memory synced source side block (List.mem_toFinset.mp member) _ both.2,
        LiveMemory.frozen_creator parent states sound ordered memory synced source side block (List.mem_toFinset.mp member) _ both.1]
    · rfl
  rw [Finset.sum_congr rfl each]
  exact sum_internal_value states source side (ordered source) view ids edge.2
    (actualRun.event_members edge (List.mem_toFinset.mp edgeMem)).2 (record edge.1) _

end Greedy.SourceCensus
