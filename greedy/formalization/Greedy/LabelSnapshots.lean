import Greedy.LabelHistory
import Greedy.GrowthInvariant
import Greedy.RestorationJournal

/-!
# Immutable entry snapshots in the sparse label history

Entries retain their original creator through freezing, splitting, and
movement. `tagged` pairs each stored entry with that original creator.
A snapshot assertion compares both immutable labels with the same sparse
history at the entry's literal joined timestamp.
-/

namespace Greedy.LabelSnapshots

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.ActualLinks
open GreedyMerge.HeapAllocation

noncomputable def atKey {n : ℕ} (history : LabelHistory.History (External n)) (time key : ℕ) : ℤ :=
  if bounded : key < 2*n+1 then LabelHistory.value history time ⟨key, bounded⟩ else 0

@[simp] theorem atKey_record {n : ℕ} (history : LabelHistory.History (External n)) (time : ℕ) (record : External n) :
    atKey history time record.val = LabelHistory.value history time record := by
  simp [atKey, record.isLt]

def Snapshot {n : ℕ} (history : LabelHistory.History (External n)) (creator : ℕ) (entry : Entry) : Prop :=
  entry.entryLabel = atKey history entry.joined entry.key ∧ entry.creatorLabel = atKey history entry.joined creator

def tagged (state : SideState) : List (Entry × ℕ) :=
  state.shrinking.flatMap (fun block => block.members.map (fun entry => (entry, block.creator))) ++
    state.grower.toList.flatMap (fun grower => grower.members.map (fun entry => (entry, grower.creator)))

def HeapSnapshots {n : ℕ} (history : LabelHistory.History (External n)) (states : States n) : Prop :=
  ∀ owner side entry creator, (entry, creator) ∈ tagged (states owner side) → Snapshot history creator entry

theorem tagged_entry (state : SideState) (entry : Entry) (creator : ℕ)
    (member : (entry, creator) ∈ tagged state) : entry ∈ entries state := by
  rcases List.mem_append.mp member with frozen | growing
  · obtain ⟨block, blockMem, mapped⟩ := List.mem_flatMap.mp frozen
    obtain ⟨item, itemMem, equal⟩ := List.mem_map.mp mapped
    have entryEq : item = entry := congrArg Prod.fst equal
    subst item
    exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨block, blockMem, itemMem⟩)
  · obtain ⟨grower, growerMem, mapped⟩ := List.mem_flatMap.mp growing
    obtain ⟨item, itemMem, equal⟩ := List.mem_map.mp mapped
    have entryEq : item = entry := congrArg Prod.fst equal
    subst item
    have present : state.grower = some grower := by simpa using growerMem
    apply List.mem_append_right
    simpa [growerEntries, present] using itemMem

theorem tagged_frozen (state : SideState) (block : Frozen) (blockMem : block ∈ state.shrinking)
    (entry : Entry) (member : entry ∈ block.members) : (entry, block.creator) ∈ tagged state :=
  List.mem_append_left _ (List.mem_flatMap.mpr ⟨block, blockMem, List.mem_map.mpr ⟨entry, member, rfl⟩⟩)

theorem tagged_growing (state : SideState) (grower : Grower) (present : state.grower = some grower)
    (entry : Entry) (member : entry ∈ grower.members) : (entry, grower.creator) ∈ tagged state :=
  List.mem_append_right _ (List.mem_flatMap.mpr
    ⟨grower, by simpa using present, List.mem_map.mpr ⟨entry, member, rfl⟩⟩)

theorem atKey_update_past {n : ℕ} (history : LabelHistory.History (External n)) (clock : ℕ)
    (target : External n → ℤ) (time key : ℕ) (past : time ≤ clock) :
    atKey (LabelHistory.update history clock target) time key = atKey history time key := by
  unfold atKey
  split_ifs
  · rw [LabelHistory.update_preserves_past history clock target time past]
  · rfl

theorem Snapshot.update_past {n : ℕ} {history : LabelHistory.History (External n)} {creator : ℕ} {entry : Entry}
    (snapshot : Snapshot history creator entry) (clock : ℕ) (target : External n → ℤ) (past : entry.joined ≤ clock) :
    Snapshot (LabelHistory.update history clock target) creator entry := by
  simpa only [Snapshot, atKey_update_past history clock target entry.joined _ past] using snapshot

theorem HeapSnapshots.update_past {n : ℕ} {history : LabelHistory.History (External n)} {states : States n}
    (snapshots : HeapSnapshots history states) (clock : ℕ) (target : External n → ℤ)
    (before : BeforeTime clock states) : HeapSnapshots (LabelHistory.update history clock target) states := by
  intro owner side entry creator member
  exact (snapshots owner side entry creator member).update_past clock target
    (Nat.le_of_lt (before owner side entry (tagged_entry _ _ _ member)))

/-- A literal factory entry reads the same current labels as the sparse
history and is therefore a correct immutable snapshot before its update. -/
theorem reader_snapshot {n : ℕ} (comparator : BST 0 n) (K : ℤ)
    (history : LabelHistory.History (External n)) (clock : ℕ) (states : States n)
    (before : LabelHistory.Before history clock)
    (current : LabelHistory.current history = RestorationJournal.labels comparator K states)
    (record owner : External n) :
    Snapshot history owner.val
      ⟨record.val, clock, GreedyMerge.StateLabels.label comparator.externalDepth K states record.val,
        GreedyMerge.StateLabels.label comparator.externalDepth K states owner.val⟩ := by
  have equal := current.symm.trans (LabelHistory.current_eq_value history clock before)
  exact ⟨by simpa [Snapshot, RestorationJournal.labels] using congrFun equal record,
    by simpa [Snapshot, RestorationJournal.labels] using congrFun equal owner⟩

end Greedy.LabelSnapshots
