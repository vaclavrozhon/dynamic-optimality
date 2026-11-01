import Greedy.LabelSnapshots
import Greedy.GrowthStructural

/-! Immutable snapshot transport through literal block operations. -/

namespace Greedy.LabelSnapshots

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.ActualLinks
open GreedyMerge.HeapAllocation

theorem tagged_cases (state : SideState) (entry : Entry) (creator : ℕ)
    (member : (entry, creator) ∈ tagged state) :
    (∃ block ∈ state.shrinking, entry ∈ block.members ∧ block.creator = creator) ∨
    (∃ grower, state.grower = some grower ∧ entry ∈ grower.members ∧ grower.creator = creator) := by
  rcases List.mem_append.mp member with frozen | growing
  · obtain ⟨block, blockMem, mapped⟩ := List.mem_flatMap.mp frozen
    obtain ⟨item, itemMem, equal⟩ := List.mem_map.mp mapped
    have first : item = entry := congrArg Prod.fst equal
    exact Or.inl ⟨block, blockMem, first ▸ itemMem, congrArg Prod.snd equal⟩
  · obtain ⟨grower, growerMem, mapped⟩ := List.mem_flatMap.mp growing
    obtain ⟨item, itemMem, equal⟩ := List.mem_map.mp mapped
    have first : item = entry := congrArg Prod.fst equal
    exact Or.inr ⟨grower, by simpa using growerMem, first ▸ itemMem, congrArg Prod.snd equal⟩

@[simp] theorem tagged_convert (owner family id base : ℕ) (state : SideState) :
    tagged (convert owner family id base state) = tagged state := by
  cases present : state.grower with
  | none => simp [convert, present]
  | some grower =>
      by_cases empty : grower.members = []
      · simp [convert, present, empty]
      · simp [convert, present, empty, tagged, freeze, emptyGrower]

theorem tagged_descends {after before : Frozen} (descendant : Descends after before)
    (entry : Entry) (member : entry ∈ after.members) :
    entry ∈ before.members ∧ after.creator = before.creator :=
  ⟨descendant.2.2.subset member, descendant.2.1⟩

theorem HeapSnapshots.descendants {n : ℕ} {history : LabelHistory.History (External n)}
    {before after : States n} (snapshots : HeapSnapshots history before)
    (growers : ∀ owner side, (after owner side).grower = (before owner side).grower)
    (descendants : ∀ owner side block, block ∈ (after owner side).shrinking →
      ∃ oldOwner oldSide old, old ∈ (before oldOwner oldSide).shrinking ∧ Descends block old) :
    HeapSnapshots history after := by
  intro owner side entry creator member
  rcases tagged_cases _ _ _ member with ⟨block, blockMem, entryMem, creatorEq⟩ |
    ⟨grower, present, entryMem, creatorEq⟩
  · obtain ⟨oldOwner, oldSide, old, oldMem, descendant⟩ := descendants owner side block blockMem
    have same : old.creator = creator := descendant.2.1.symm.trans creatorEq
    rw [← same]
    exact snapshots oldOwner oldSide entry old.creator
      (tagged_frozen _ old oldMem entry (descendant.2.2.subset entryMem))
  · rw [growers] at present
    rw [← creatorEq]
    exact snapshots owner side entry grower.creator (tagged_growing _ grower present entry entryMem)

theorem convertHeap_snapshots {n : ℕ} {history : LabelHistory.History (External n)}
    (rank : ℕ → ℕ) (selected : External n → Bool → Bool) (start : ℕ) (states : States n)
    (snapshots : HeapSnapshots history states) :
    HeapSnapshots history (convertHeap rank selected start states).1 := by
  intro owner side entry creator member
  rw [convertHeap_apply] at member
  split_ifs at member
  · exact snapshots owner side entry creator (by simpa using member)
  · exact snapshots owner side entry creator member

theorem tagged_erase (key : ℕ) (state : SideState) (entry : Entry) (creator : ℕ)
    (member : (entry, creator) ∈ tagged (eraseFrozenKey key state)) :
    (entry, creator) ∈ tagged state := by
  rcases tagged_cases _ _ _ member with ⟨block, blockMem, entryMem, creatorEq⟩ |
    ⟨grower, present, entryMem, creatorEq⟩
  · obtain ⟨old, oldMem, rfl⟩ := List.mem_map.mp blockMem
    rw [← creatorEq]
    exact tagged_frozen state old oldMem entry (List.mem_filter.mp entryMem).1
  · rw [← creatorEq]
    exact tagged_growing state grower present entry entryMem

theorem tagged_append (owner : ℕ) (entry : Entry) (state : SideState)
    (creators : ∀ grower, state.grower = some grower → grower.creator = owner)
    (item : Entry) (creator : ℕ) (member : (item, creator) ∈ tagged (appendGrower entry state)) :
    (item, creator) ∈ tagged state ∨ (item = entry ∧ creator = owner) := by
  rcases tagged_cases _ _ _ member with ⟨block, blockMem, entryMem, creatorEq⟩ |
    ⟨grower, present, entryMem, creatorEq⟩
  · left
    rw [← creatorEq]
    exact tagged_frozen state block blockMem item entryMem
  · cases old : state.grower with
    | none => simp [appendGrower, old] at present
    | some previous =>
        have same : grow entry previous = grower := by simpa [appendGrower, old] using present
        rw [← same] at entryMem creatorEq
        rcases List.mem_append.mp entryMem with previousMem | fresh
        · left
          rw [← creatorEq]
          exact tagged_growing state previous old item previousMem
        · right
          exact ⟨List.mem_singleton.mp fresh, creatorEq.symm.trans (creators previous old)⟩

theorem linkState_snapshots {n : ℕ} {history : LabelHistory.History (External n)}
    (states : States n) (source winner loser : External n) (sourceSide targetSide : Bool) (entry : Entry)
    (snapshots : HeapSnapshots history states) (creators : GrowthJournal.Creators states)
    (fresh : Snapshot history winner.val entry) :
    HeapSnapshots history (linkState states source winner loser sourceSide targetSide entry) := by
  intro owner side item creator member
  unfold linkState at member
  split_ifs at member with target selected
  · rcases tagged_append owner.val entry (states owner side) (creators owner side) item creator member with old | ⟨rfl, rfl⟩
    · exact snapshots owner side item creator old
    · simpa only [target.1] using fresh
  · exact snapshots owner side item creator (tagged_erase loser.val _ _ _ member)
  · exact snapshots owner side item creator member

theorem initial_snapshots {n : ℕ} (comparator tree : BST 0 n) (K : ℤ) :
    HeapSnapshots ⟨RestorationJournal.labels comparator K
      (GreedyMerge.InitialBlocks.state (Splay.Rank.Snapshot.ofTree comparator) tree K), []⟩
      (GreedyMerge.InitialBlocks.state (Splay.Rank.Snapshot.ofTree comparator) tree K) := by
  intro owner side entry creator member
  rcases tagged_cases _ _ _ member with ⟨block, blockMem, _⟩ | ⟨grower, present, entryMem, creatorEq⟩
  · simp [GreedyMerge.InitialBlocks.state] at blockMem
  · have same := Option.some.inj present
    rw [← same] at entryMem creatorEq
    obtain ⟨record, _, rfl⟩ := List.mem_map.mp entryMem
    have stored := GreedyMerge.InitialBlocks.entry_snapshots comparator tree K owner record side
    simpa [Snapshot, GreedyMerge.InitialBlocks.entry, ← creatorEq, atKey, LabelHistory.value,
      RestorationJournal.labels, record.isLt, owner.isLt] using stored

end Greedy.LabelSnapshots
