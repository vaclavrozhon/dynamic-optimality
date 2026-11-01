import Greedy.MembershipInstall

/-! A current-record pointer identifies its literal family and original join. -/

namespace Greedy.MembershipPointer

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.ActualLinks
open GreedyMerge.HeapAllocation

abbrev Ticket := ℕ × ℕ

def Synced {n : ℕ} (pointer : External n → Ticket) (states : States n) : Prop :=
  MembershipStamps.Held (fun entry family => ∀ record : External n,
    record.val = entry.key → pointer record = (family, entry.joined)) states

theorem restore {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n) (names : PaidNames)
    (makeEntry : External n → Entry) (record owner : External n)
    (parent : canonicalParent snapshot tree record = some owner)
    (states : States n) (pointer : External n → Ticket) (synced : Synced pointer states)
    (absent : ¬ GreedyMerge.BlockCoverage.Represented states record.val)
    (keys : ∀ creator, (makeEntry creator).key = record.val) :
    Synced (Function.update pointer record (names.paidFamily, (makeEntry owner).joined))
      (restorePort snapshot tree names makeEntry record states).1 := by
  have old : Synced (Function.update pointer record (names.paidFamily, (makeEntry owner).joined)) states := by
    intro place side item family member query key
    have different : query ≠ record := by
      intro equal
      apply absent
      exact ⟨place, side, item, MembershipStamps.tagged_entry _ item family member,
        key.symm.trans (congrArg Fin.val equal)⟩
    rw [Function.update_of_ne different]
    exact synced place side item family member query key
  intro place side item family member query key
  simp only [restorePort, parent, replaceSide] at member
  split_ifs at member with selected
  · obtain ⟨placeEq, sideEq⟩ := selected
    subst place
    subst side
    rcases MembershipStamps.tagged_installPaid owner.val _ _ _ _ _ _ _ item family member with previous | ⟨rfl, rfl⟩
    · exact old owner _ item family (by simpa using previous) query key
    · have equal : query = record := Fin.ext (key.trans (keys owner))
      subst query
      exact Function.update_self ..
  · exact old place side item family member query key

theorem link {n : ℕ} (parent : Parents n) (states : States n)
    (source winner loser : External n) (sourceSide targetSide : Bool) (fresh : Entry)
    (sound : SoundFor parent states) (ordered : Ordered states)
    (different : source ≠ winner) (emptySource : growerEntries (states source sourceSide).grower = [])
    (oldEntry : Entry) (oldMember : oldEntry ∈ entries (states source sourceSide))
    (oldKey : oldEntry.key = loser.val) (freshKey : fresh.key = loser.val)
    (grower : Grower) (present : (states winner targetSide).grower = some grower)
    (pointer : External n → Ticket) (synced : Synced pointer states) :
    Synced (Function.update pointer loser (grower.family, fresh.joined))
      (linkState states source winner loser sourceSide targetSide fresh) := by
  intro place side entry family member record key
  have sameKey (oldMem : (entry, family) ∈ MembershipStamps.tagged (states place side)) (equal : record = loser) :
      place = source ∧ side = sourceSide :=
    GreedyMerge.ActualLinks.key_location_unique parent states sound ordered
      (MembershipStamps.tagged_entry _ entry family oldMem) oldMember
      (key.symm.trans ((congrArg Fin.val equal).trans oldKey.symm))
  have inherited (oldMem : (entry, family) ∈ MembershipStamps.tagged (states place side)) (ne : record ≠ loser) :
      Function.update pointer loser (grower.family, fresh.joined) record = (family, entry.joined) := by
    rw [Function.update_of_ne ne]
    exact synced place side entry family oldMem record key
  unfold linkState at member
  split_ifs at member with target selected
  · have currentGrower : (states place side).grower = some grower := by rw [target.1, target.2]; exact present
    rcases MembershipStamps.tagged_append (states place side) grower currentGrower fresh entry family member with old | ⟨equal, familyEq⟩
    · apply inherited old
      intro same
      exact different ((sameKey old same).1.symm.trans target.1)
    · have sameRecord : record = loser := Fin.ext (key.trans ((congrArg Entry.key equal).trans freshKey))
      rw [sameRecord, Function.update_self, equal, familyEq]
  · have actual := MembershipStamps.tagged_entry _ entry family member
    have emptyHere : growerEntries (states place side).grower = [] := by rw [selected.1, selected.2]; exact emptySource
    rw [eraseFrozenKey_entries loser.val _ emptyHere] at actual
    have filtered := List.mem_filter.mp actual
    apply inherited (MembershipStamps.tagged_erase loser.val _ entry family member)
    intro equal
    have ne : entry.key ≠ loser.val := by simpa only [bne_iff_ne] using filtered.2
    exact ne (key.symm.trans (congrArg Fin.val equal))
  · apply inherited member
    intro equal
    exact selected (sameKey member equal)

end Greedy.MembershipPointer
