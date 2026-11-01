import Greedy.LiveMemory
import Greedy.AccessJournal

/-! A physical link replaces exactly the departing record's creator memory. -/

namespace Greedy.LiveMemory

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.ActualLinks
open GreedyMerge.HeapAllocation EntryJournal RestorationJournal

theorem link {n : ℕ} (parent : Parents n) (states : States n)
    (source winner loser : External n) (sourceSide targetSide : Bool) (fresh : Entry)
    (sound : SoundFor parent states) (ordered : Ordered states)
    (persistent : Persistent states) (different : source ≠ winner)
    (emptySource : growerEntries (states source sourceSide).grower = [])
    (oldEntry : Entry) (oldMember : oldEntry ∈ entries (states source sourceSide))
    (oldKey : oldEntry.key = loser.val) (freshKey : fresh.key = loser.val)
    (memory : External n → ℤ) (synced : Synced memory states) :
    Synced (Function.update memory loser fresh.creatorLabel)
      (linkState states source winner loser sourceSide targetSide fresh) := by
  intro place side entry creator tagged record key
  have member := EntryProperties.tagged_entry _ entry creator tagged
  rw [linkState_entries states source winner loser sourceSide targetSide fresh (persistent _ _) emptySource] at member
  have sameKey (oldMem : entry ∈ entries (states place side)) (equal : record = loser) :
      place = source ∧ side = sourceSide :=
    GreedyMerge.ActualLinks.key_location_unique parent states sound ordered oldMem oldMember
      (key.symm.trans ((congrArg Fin.val equal).trans oldKey.symm))
  have inherited (oldMem : entry ∈ entries (states place side)) (ne : record ≠ loser) :
      Function.update memory loser fresh.creatorLabel record = entry.creatorLabel := by
    rw [Function.update_of_ne ne]
    exact synced.entry place side entry oldMem record key
  split_ifs at member with target selected
  · rcases List.mem_append.mp member with old | arrived
    · apply inherited old
      intro equal
      exact different ((sameKey old equal).1.symm.trans target.1)
    · have sameEntry := List.mem_singleton.mp arrived
      have sameRecord : record = loser := Fin.ext (key.trans ((congrArg Entry.key sameEntry).trans freshKey))
      rw [sameRecord, Function.update_self, sameEntry]
  · have filtered := List.mem_filter.mp member
    apply inherited filtered.1
    intro equal
    have ne : entry.key ≠ loser.val := by simpa only [bne_iff_ne] using filtered.2
    exact ne (key.symm.trans (congrArg Fin.val equal))
  · apply inherited member
    intro equal
    exact selected (sameKey member equal)

end Greedy.LiveMemory
