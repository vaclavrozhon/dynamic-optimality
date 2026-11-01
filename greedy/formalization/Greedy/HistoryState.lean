import Greedy.SnapshotTransport

/-! The sparse history follows the current labels of the actual block heap. -/

namespace Greedy.LabelSnapshots

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.ActualLinks
open GreedyMerge.HeapAllocation

structure Sound {n : ℕ} (comparator : BST 0 n) (K : ℤ) (clock : ℕ)
    (states : States n) (history : LabelHistory.History (External n)) : Prop where
  before : LabelHistory.Before history clock
  current : LabelHistory.current history = RestorationJournal.labels comparator K states
  snapshots : HeapSnapshots history states

theorem Sound.advance {n clock : ℕ} {comparator : BST 0 n} {K : ℤ} {states : States n}
    {history : LabelHistory.History (External n)} (sound : Sound comparator K clock states history)
    (later : ℕ) (bound : clock ≤ later) : Sound comparator K later states history :=
  ⟨sound.before.mono later bound, sound.current, sound.snapshots⟩

theorem HeapSnapshots.update_through {n : ℕ} {history : LabelHistory.History (External n)} {states : States n}
    (snapshots : HeapSnapshots history states) (clock : ℕ) (target : External n → ℤ)
    (before : BeforeTime (clock+1) states) : HeapSnapshots (LabelHistory.update history clock target) states := by
  intro owner side entry creator member
  exact (snapshots owner side entry creator member).update_past clock target
    (by have bound := before owner side entry (tagged_entry _ _ _ member); omega)

theorem entry_tagged (state : SideState) (entry : Entry) (member : entry ∈ entries state) :
    ∃ creator, (entry, creator) ∈ tagged state := by
  rcases List.mem_append.mp member with frozen | growing
  · obtain ⟨block, blockMem, entryMem⟩ := List.mem_flatMap.mp frozen
    exact ⟨block.creator, tagged_frozen state block blockMem entry entryMem⟩
  · cases present : state.grower with
    | none => simp [growerEntries, present] at growing
    | some grower => exact ⟨grower.creator, tagged_growing state grower present entry (by simpa [growerEntries, present] using growing)⟩

theorem linkState_time {n clock : ℕ} (states : States n) (source winner loser : External n)
    (sourceSide targetSide : Bool) (entry : Entry) (time : entry.joined = clock)
    (creators : GrowthJournal.Creators states) (before : BeforeTime clock states) :
    BeforeTime (clock+1) (linkState states source winner loser sourceSide targetSide entry) := by
  intro owner side item member
  obtain ⟨creator, taggedMem⟩ := entry_tagged _ _ member
  unfold linkState at taggedMem
  split_ifs at taggedMem
  · rcases tagged_append owner.val entry (states owner side) (creators owner side) item creator taggedMem with old | ⟨rfl, _⟩
    · exact (before owner side item (tagged_entry _ _ _ old)).trans_le (by omega)
    · omega
  · exact (before owner side item (tagged_entry _ _ _ (tagged_erase loser.val _ _ _ taggedMem))).trans_le (by omega)
  · exact (before owner side item (tagged_entry _ _ _ taggedMem)).trans_le (by omega)

theorem Sound.update {n clock : ℕ} {oldComparator comparator : BST 0 n} {K : ℤ}
    {old states : States n} {history : LabelHistory.History (External n)}
    (sound : Sound oldComparator K clock old history) (snapshots : HeapSnapshots history states)
    (before : BeforeTime (clock+1) states) :
    Sound comparator K (clock+1) states
      (LabelHistory.update history clock (RestorationJournal.labels comparator K states)) :=
  ⟨LabelHistory.update_before history clock _ sound.before, LabelHistory.current_update history clock _,
    snapshots.update_through clock _ before⟩

theorem initial_sound {n : ℕ} (comparator tree : BST 0 n) (K : ℤ) :
    Sound comparator K (GreedyMerge.InitialBlocks.epoch n)
      (GreedyMerge.InitialBlocks.state (Splay.Rank.Snapshot.ofTree comparator) tree K)
      ⟨RestorationJournal.labels comparator K (GreedyMerge.InitialBlocks.state (Splay.Rank.Snapshot.ofTree comparator) tree K), []⟩ :=
  ⟨by intro change member; simp at member, LabelHistory.current_initial _, initial_snapshots comparator tree K⟩

end Greedy.LabelSnapshots
