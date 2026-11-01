import StateLabels
import ActualLinkRuns
import ActualPhaseEvents

/-!
The numerical label read from the actual intermediate forest agrees with
the literal one-record loser update used by the phase accounting. Lookup
uniqueness uses arbitrary parent-function soundness, so it applies before
a consolidation has reassembled the canonical binary tree.
-/
namespace GreedyMerge.StateLabels

open OrderedBlocks Primitives ActualLinks
open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical Splay.Analysis

theorem base_unique_for {n : ℕ} (parent : Parents n)
    (rank : ℕ → ℕ) (states : ActualLinks.States n)
    (valid : Ordered states) (sound : SoundFor parent states) (key first second : ℕ)
    (firstBase : HasBase rank states key first) (secondBase : HasBase rank states key second) :
    first=second := by
  obtain ⟨a,aSide,aEntry,aMember,aKey⟩ := firstBase
  obtain ⟨b,bSide,bEntry,bMember,bKey⟩ := secondBase
  obtain ⟨rfl,rfl⟩ := ActualLinks.key_location_unique parent states sound valid
    (tagged_member_entry _ _ _ _ aMember) (tagged_member_entry _ _ _ _ bMember)
    (aKey.trans bKey.symm)
  exact congrArg Prod.snd (List.inj_on_of_nodup_map
    (tagged_key_nodup (rank a.val) a.val aSide (states a aSide) (valid a aSide))
    aMember bMember (aKey.trans bKey.symm))

theorem label_of_base_for {n : ℕ} (parent : Parents n)
    (rank : ℕ → ℕ) (K : ℤ) (states : ActualLinks.States n)
    (valid : Ordered states) (sound : SoundFor parent states) (key base : ℕ)
    (hasBase : HasBase rank states key base) :
    label rank K states key=contractedGap (rank key-base) := by
  have present : ∃ base, HasBase rank states key base := ⟨base,hasBase⟩
  simp only [label,dif_pos present]
  rw [base_unique_for parent rank states valid sound key present.choose base present.choose_spec hasBase]

theorem label_of_frozen_for {n : ℕ} (parent : Parents n)
    (rank : ℕ → ℕ) (K : ℤ) (states : ActualLinks.States n)
    (valid : Ordered states) (sound : SoundFor parent states) (owner : External n) (side : Bool)
    (block : Frozen) (blockMember : block∈(states owner side).shrinking)
    (entry : Entry) (member : entry∈block.members) :
    label rank K states entry.key=contractedGap (rank entry.key-block.base) := by
  apply label_of_base_for parent rank K states valid sound
  exact ⟨owner,side,entry,tagged_frozen _ _ block blockMember entry member,rfl⟩

theorem label_of_growing_for {n : ℕ} (parent : Parents n)
    (rank : ℕ → ℕ) (K : ℤ) (states : ActualLinks.States n)
    (valid : Ordered states) (sound : SoundFor parent states) (owner : External n) (side : Bool)
    (entry : Entry) (member : entry∈growerEntries (states owner side).grower) :
    label rank K states entry.key=contractedGap (rank entry.key-rank owner.val) := by
  apply label_of_base_for parent rank K states valid sound
  exact ⟨owner,side,entry,tagged_growing _ _ entry member,rfl⟩

theorem tagged_appendGrower (ownerRank : ℕ) (fresh : Entry) (state : SideState)
    (present : state.grower.isSome) :
    tagged ownerRank (appendGrower fresh state)=tagged ownerRank state++[(fresh,ownerRank)] := by
  cases hg : state.grower with
  | none => simp [hg] at present
  | some grower => simp [tagged,appendGrower,hg,growerEntries,grow,List.append_assoc]

theorem tagged_eraseFrozenKey_iff (ownerRank key : ℕ) (state : SideState)
    (emptySource : growerEntries state.grower=[]) (entry : Entry) (base : ℕ) :
    (entry,base)∈tagged ownerRank (eraseFrozenKey key state) ↔
      (entry,base)∈tagged ownerRank state ∧ entry.key≠key := by
  simp only [tagged,eraseFrozenKey,emptySource,List.map_nil,List.append_nil]
  simp only [List.mem_flatMap,List.mem_map]
  constructor
  · rintro ⟨updated,⟨old,oldMem,rfl⟩,member,filtered,equal⟩
    have entryMem := (List.mem_filter.mp filtered).1
    have notKey : member.key≠key := by simpa using (List.mem_filter.mp filtered).2
    have entryEq : member=entry := congrArg Prod.fst equal
    have baseEq : old.base=base := congrArg Prod.snd equal
    subst member
    exact ⟨⟨old,oldMem,entry,entryMem,by simp [baseEq]⟩,notKey⟩
  · rintro ⟨⟨old,oldMem,member,entryMem,equal⟩,notKey⟩
    have entryEq : member=entry := congrArg Prod.fst equal
    subst member
    exact ⟨eraseMember key old,⟨old,oldMem,rfl⟩,entry,List.mem_filter.mpr ⟨entryMem,by simpa using notKey⟩,equal⟩

theorem tagged_linkState_other {n : ℕ} (rank : ℕ → ℕ) (states : ActualLinks.States n)
    (source winner loser : External n) (sourceSide targetSide : Bool) (fresh : Entry)
    (grower : (states winner targetSide).grower.isSome)
    (emptySource : growerEntries (states source sourceSide).grower=[])
    (newKey : fresh.key=loser.val) (owner : External n) (side : Bool) (entry : Entry) (base : ℕ)
    (other : entry.key≠loser.val) :
    (entry,base)∈tagged (rank owner.val)
      (linkState states source winner loser sourceSide targetSide fresh owner side) ↔
    (entry,base)∈tagged (rank owner.val) (states owner side) := by
  unfold linkState
  split_ifs with target selected
  · obtain ⟨rfl,rfl⟩ := target
    rw [tagged_appendGrower _ _ _ grower,List.mem_append,List.mem_singleton]
    have impossible : ¬(entry,base)=(fresh,rank owner.val) := by
      intro equal
      exact other ((congrArg (fun item : Entry×ℕ => item.1.key) equal).trans newKey)
    simp only [impossible,or_false]
  · obtain ⟨rfl,rfl⟩ := selected
    rw [tagged_eraseFrozenKey_iff _ _ _ emptySource]
    exact and_iff_left other
  · rfl

theorem hasBase_linkState_other {n : ℕ} (rank : ℕ → ℕ) (states : ActualLinks.States n)
    (source winner loser : External n) (sourceSide targetSide : Bool) (fresh : Entry)
    (grower : (states winner targetSide).grower.isSome)
    (emptySource : growerEntries (states source sourceSide).grower=[])
    (newKey : fresh.key=loser.val) (key base : ℕ) (other : key≠loser.val) :
    HasBase rank (linkState states source winner loser sourceSide targetSide fresh) key base ↔
      HasBase rank states key base := by
  constructor
  · rintro ⟨owner,side,entry,member,entryKey⟩
    exact ⟨owner,side,entry,(tagged_linkState_other rank states source winner loser sourceSide
      targetSide fresh grower emptySource newKey owner side entry base (by simpa [entryKey] using other)).mp member,entryKey⟩
  · rintro ⟨owner,side,entry,member,entryKey⟩
    exact ⟨owner,side,entry,(tagged_linkState_other rank states source winner loser sourceSide
      targetSide fresh grower emptySource newKey owner side entry base (by simpa [entryKey] using other)).mpr member,entryKey⟩

theorem label_linkState_other {n : ℕ} (rank : ℕ → ℕ) (K : ℤ) (states : ActualLinks.States n)
    (source winner loser : External n) (sourceSide targetSide : Bool) (fresh : Entry)
    (grower : (states winner targetSide).grower.isSome)
    (emptySource : growerEntries (states source sourceSide).grower=[])
    (newKey : fresh.key=loser.val) (key : ℕ) (other : key≠loser.val) :
    label rank K (linkState states source winner loser sourceSide targetSide fresh) key =
      label rank K states key := by
  have predicate : HasBase rank (linkState states source winner loser sourceSide targetSide fresh) key =
      HasBase rank states key := by
    funext base
    exact propext (hasBase_linkState_other rank states source winner loser sourceSide targetSide fresh
      grower emptySource newKey key base other)
  unfold label
  rw [predicate]

/-- Only the loser changes bucket, to its new grower's true parent gap.
The updated forest's soundness and ordering are ordinary structural
invariants, not a numerical label-update premise. -/
theorem linkState_label_of_next_sound {n : ℕ} (nextParent : Parents n)
    (rank : ℕ → ℕ) (K : ℤ) (states : ActualLinks.States n)
    (source winner loser : External n) (sourceSide targetSide : Bool) (fresh : Entry)
    (grower : (states winner targetSide).grower.isSome)
    (emptySource : growerEntries (states source sourceSide).grower=[])
    (newKey : fresh.key=loser.val)
    (nextOrdered : Ordered (linkState states source winner loser sourceSide targetSide fresh))
    (nextSound : SoundFor nextParent (linkState states source winner loser sourceSide targetSide fresh)) :
    label rank K (linkState states source winner loser sourceSide targetSide fresh) =
      GreedyForest.Phase.linkLabels rank (label rank K states) (winner.val,loser.val) := by
  funext key
  by_cases equal : key=loser.val
  · subst key
    have base : HasBase rank (linkState states source winner loser sourceSide targetSide fresh)
        loser.val (rank winner.val) := by
      refine ⟨winner,targetSide,fresh,?_,newKey⟩
      simp only [linkState,and_self,↓reduceIte]
      rw [tagged_appendGrower _ _ _ grower]
      exact List.mem_append_right _ (by simp)
    rw [label_of_base_for nextParent rank K _ nextOrdered nextSound _ _ base]
    simp [GreedyForest.Phase.linkLabels]
  · rw [label_linkState_other rank K states source winner loser sourceSide targetSide fresh
      grower emptySource newKey key equal]
    simp [GreedyForest.Phase.linkLabels,equal]

theorem linkState_label {n : ℕ} (parent : Parents n)
    (rank : ℕ → ℕ) (K : ℤ) (states : ActualLinks.States n)
    (source winner loser : External n) (sourceSide targetSide : Bool) (fresh : Entry)
    (sound : SoundFor parent states) (ordered : Ordered states) (persistent : Persistent states)
    (different : source≠winner) (emptySource : growerEntries (states source sourceSide).grower=[])
    (oldEntry : Entry) (oldMember : oldEntry∈entries (states source sourceSide))
    (oldKey : oldEntry.key=loser.val) (newKey : fresh.key=loser.val)
    (correctSide : onSide winner.val targetSide fresh)
    (outside : ∀ old∈entries (states winner targetSide), outward targetSide old fresh) :
    label rank K (linkState states source winner loser sourceSide targetSide fresh) =
      GreedyForest.Phase.linkLabels rank (label rank K states) (winner.val,loser.val) :=
  linkState_label_of_next_sound (linkParents parent winner loser) rank K states source winner loser
    sourceSide targetSide fresh (persistent _ _) emptySource newKey
    (linkState_ordered states source winner loser sourceSide targetSide fresh ordered persistent
      emptySource correctSide outside)
    (linkState_sound parent states source winner loser sourceSide targetSide fresh sound ordered
      persistent different emptySource oldEntry oldMember oldKey newKey)

end GreedyMerge.StateLabels

#print axioms GreedyMerge.StateLabels.base_unique_for
#print axioms GreedyMerge.StateLabels.linkState_label
