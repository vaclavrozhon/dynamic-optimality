import SourceSideStates
import OrderedPortDeletion

/-! Literal block-state updates for intermediate consolidation forests.
Both stored labels in the new immutable Entry come from the pre-update
snapshot. States have the same curried shape as administration. -/
namespace GreedyMerge.ActualLinks
open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives

abbrev States (n : ℕ) := External n → Bool → SideState
abbrev Parents (n : ℕ) := External n → Option (External n)

def SoundFor {n : ℕ} (parent : Parents n) (states : States n) : Prop :=
  ∀ owner side entry, entry ∈ entries (states owner side) →
    ∃ record : External n, record.val=entry.key ∧ parent record=some owner

def CompleteFor {n : ℕ} (parent : Parents n) (states : States n) : Prop :=
  ∀ record owner, parent record=some owner →
    ∃ side entry, entry ∈ entries (states owner side) ∧ entry.key=record.val

def Ordered {n : ℕ} (states : States n) : Prop :=
  ∀ owner side, Valid owner.val side (states owner side)

def Persistent {n : ℕ} (states : States n) : Prop :=
  ∀ owner side, (states owner side).grower.isSome

/-- Both labels are captured before the loser is relabeled. -/
def arrivalEntry {n : ℕ} (labels : ℕ → ℤ) (winner loser : External n) (time : ℕ) : Entry :=
  ⟨loser.val,time,labels loser.val,labels winner.val⟩

def appendGrower (entry : Entry) (state : SideState) : SideState :=
  { state with grower := state.grower.map (grow entry) }

def linkState {n : ℕ} (states : States n) (source winner loser : External n)
    (sourceSide targetSide : Bool) (entry : Entry) : States n :=
  fun owner side =>
    if owner=winner ∧ side=targetSide then appendGrower entry (states owner side)
    else if owner=source ∧ side=sourceSide then eraseFrozenKey loser.val (states owner side)
    else states owner side

def linkParents {n : ℕ} (parent : Parents n) (winner loser : External n) : Parents n :=
  Function.update parent loser (some winner)

@[simp] theorem linkParents_loser {n : ℕ} (parent : Parents n) (winner loser : External n) :
    linkParents parent winner loser loser=some winner := by simp [linkParents]

@[simp] theorem linkParents_other {n : ℕ} (parent : Parents n) (winner loser record : External n)
    (different : record ≠ loser) : linkParents parent winner loser record=parent record := by
  simp [linkParents,different]

theorem appendGrower_entries (entry : Entry) (state : SideState)
    (present : state.grower.isSome) :
    entries (appendGrower entry state)=entries state++[entry] := by
  cases h : state.grower with
  | none => simp [h] at present
  | some g => simpa [appendGrower,h,entries,growerEntries,grow,List.append_assoc]

theorem eraseFrozenKey_entries (key : ℕ) (state : SideState)
    (emptyGrower : growerEntries state.grower=[]) :
    entries (eraseFrozenKey key state)=(entries state).filter (fun e => e.key != key) := by
  simp [eraseFrozenKey,entries,eraseFrozenKey_flat,emptyGrower]

theorem linkState_entries {n : ℕ} (states : States n) (source winner loser : External n)
    (sourceSide targetSide : Bool) (entry : Entry)
    (grower : (states winner targetSide).grower.isSome)
    (emptySource : growerEntries (states source sourceSide).grower=[])
    (owner : External n) (side : Bool) :
    entries (linkState states source winner loser sourceSide targetSide entry owner side) =
      if owner=winner ∧ side=targetSide then entries (states owner side)++[entry]
      else if owner=source ∧ side=sourceSide then
        (entries (states owner side)).filter (fun e => e.key != loser.val)
      else entries (states owner side) := by
  unfold linkState
  split_ifs with target selected
  · obtain ⟨rfl,rfl⟩ := target
    exact appendGrower_entries entry _ grower
  · obtain ⟨rfl,rfl⟩ := selected
    exact eraseFrozenKey_entries loser.val _ emptySource
  · rfl

theorem linkState_persistent {n : ℕ} (states : States n) (source winner loser : External n)
    (sourceSide targetSide : Bool) (entry : Entry) (persistent : Persistent states) :
    Persistent (linkState states source winner loser sourceSide targetSide entry) := by
  intro owner side
  unfold linkState
  split_ifs
  · simpa [appendGrower] using persistent owner side
  · exact persistent owner side
  · exact persistent owner side

theorem appendGrower_valid {owner : ℕ} {side : Bool} {state : SideState} (entry : Entry)
    (valid : Valid owner side state) (present : state.grower.isSome)
    (onCorrectSide : onSide owner side entry)
    (outside : ∀ old ∈ entries state, outward side old entry) :
    Valid owner side (appendGrower entry state) := by
  cases h : state.grower with
  | none => simp [h] at present
  | some g =>
      have shape : state=⟨state.shrinking,some g⟩ := by cases state; simp_all
      rw [shape] at valid outside ⊢
      exact grow_valid owner side _ g entry valid onCorrectSide outside

theorem eraseFrozenKey_valid {owner key : ℕ} {side : Bool} {state : SideState}
    (valid : Valid owner side state) (emptyGrower : growerEntries state.grower=[]) :
    Valid owner side (eraseFrozenKey key state) := by
  refine ⟨?_,?_,valid.2.2⟩
  · rw [eraseFrozenKey_entries key state emptyGrower]
    exact valid.1.filter _
  · intro e he
    rw [eraseFrozenKey_entries key state emptyGrower] at he
    exact valid.2.1 e (List.mem_filter.mp he).1

theorem linkState_ordered {n : ℕ} (states : States n) (source winner loser : External n)
    (sourceSide targetSide : Bool) (entry : Entry)
    (ordered : Ordered states) (persistent : Persistent states)
    (emptySource : growerEntries (states source sourceSide).grower=[])
    (onCorrectSide : onSide winner.val targetSide entry)
    (outside : ∀ old ∈ entries (states winner targetSide), outward targetSide old entry) :
    Ordered (linkState states source winner loser sourceSide targetSide entry) := by
  intro owner side
  unfold linkState
  split_ifs with target selected
  · obtain ⟨rfl,rfl⟩ := target
    exact appendGrower_valid entry (ordered _ _) (persistent _ _) onCorrectSide outside
  · obtain ⟨rfl,rfl⟩ := selected
    exact eraseFrozenKey_valid (ordered _ _) emptySource
  · exact ordered owner side

/-- Parent correctness and side order uniquely identify a record's slot. -/
theorem key_location_unique {n : ℕ} (parent : Parents n) (states : States n)
    (sound : SoundFor parent states) (ordered : Ordered states)
    {firstOwner secondOwner : External n} {firstSide secondSide : Bool}
    {firstEntry secondEntry : Entry}
    (firstMem : firstEntry ∈ entries (states firstOwner firstSide))
    (secondMem : secondEntry ∈ entries (states secondOwner secondSide))
    (sameKey : firstEntry.key=secondEntry.key) :
    firstOwner=secondOwner ∧ firstSide=secondSide := by
  obtain ⟨firstRecord,firstKey,firstParent⟩ := sound _ _ _ firstMem
  obtain ⟨secondRecord,secondKey,secondParent⟩ := sound _ _ _ secondMem
  have recordEq : firstRecord=secondRecord := Fin.ext (by omega)
  have ownerEq : firstOwner=secondOwner := by
    rw [recordEq,secondParent] at firstParent
    exact (Option.some.inj firstParent).symm
  refine ⟨ownerEq,?_⟩
  have sideFirst := (ordered firstOwner firstSide).2.1 firstEntry firstMem
  have sideSecond := (ordered secondOwner secondSide).2.1 secondEntry secondMem
  cases firstSide <;> cases secondSide <;> simp_all [onSide] <;> omega

/-- Delete the old loser membership, append its fresh membership, and
change exactly its parent. Other membership records remain immutable. -/
theorem linkState_sound {n : ℕ} (parent : Parents n) (states : States n)
    (source winner loser : External n) (sourceSide targetSide : Bool) (fresh : Entry)
    (sound : SoundFor parent states) (ordered : Ordered states)
    (persistent : Persistent states) (different : source ≠ winner)
    (emptySource : growerEntries (states source sourceSide).grower=[])
    (oldEntry : Entry) (oldMember : oldEntry ∈ entries (states source sourceSide))
    (oldKey : oldEntry.key=loser.val) (newKey : fresh.key=loser.val) :
    SoundFor (linkParents parent winner loser)
      (linkState states source winner loser sourceSide targetSide fresh) := by
  intro owner side entry member
  rw [linkState_entries states source winner loser sourceSide targetSide fresh
    (persistent winner targetSide) emptySource] at member
  split_ifs at member with target selected
  · rcases List.mem_append.mp member with old | newEntry
    · obtain ⟨record,key,parentEq⟩ := sound owner side entry old
      refine ⟨record,key,?_⟩
      have ne : record ≠ loser := by
        intro same
        have location := key_location_unique parent states sound ordered oldMember old
          (by rw [oldKey,←key,same])
        exact different (location.1.trans target.1)
      rw [linkParents_other _ _ _ _ ne]
      exact parentEq
    · have equal := List.mem_singleton.mp newEntry
      subst entry
      exact ⟨loser,newKey.symm,by simpa only [target.1] using linkParents_loser parent winner loser⟩
  · obtain ⟨record,key,parentEq⟩ := sound owner side entry (List.mem_filter.mp member).1
    refine ⟨record,key,?_⟩
    have ne : record ≠ loser := by
      have hne : entry.key ≠ loser.val := by simpa using (List.mem_filter.mp member).2
      intro same
      exact hne (key.symm.trans (congrArg Fin.val same))
    rw [linkParents_other _ _ _ _ ne]
    exact parentEq
  · obtain ⟨record,key,parentEq⟩ := sound owner side entry member
    refine ⟨record,key,?_⟩
    have ne : record ≠ loser := by
      intro same
      have location := key_location_unique parent states sound ordered oldMember member
        (by rw [oldKey,←key,same])
      exact selected ⟨location.1.symm,location.2.symm⟩
    rw [linkParents_other _ _ _ _ ne]
    exact parentEq

theorem linkState_complete {n : ℕ} (parent : Parents n) (states : States n)
    (source winner loser : External n) (sourceSide targetSide : Bool) (fresh : Entry)
    (complete : CompleteFor parent states) (persistent : Persistent states)
    (emptySource : growerEntries (states source sourceSide).grower=[])
    (newKey : fresh.key=loser.val) :
    CompleteFor (linkParents parent winner loser)
      (linkState states source winner loser sourceSide targetSide fresh) := by
  intro record owner parentEq
  by_cases same : record=loser
  · subst record
    have sameOwner : owner=winner := (Option.some.inj ((linkParents_loser parent winner loser).symm.trans parentEq)).symm
    subst owner
    refine ⟨targetSide,fresh,?_,newKey⟩
    rw [linkState_entries states source winner loser sourceSide targetSide fresh
      (persistent winner targetSide) emptySource]
    simp
  · rw [linkParents_other _ _ _ _ same] at parentEq
    obtain ⟨side,entry,member,key⟩ := complete record owner parentEq
    refine ⟨side,entry,?_,key⟩
    rw [linkState_entries states source winner loser sourceSide targetSide fresh
      (persistent winner targetSide) emptySource]
    split_ifs
    · exact List.mem_append_left _ member
    · apply List.mem_filter.mpr
      refine ⟨member,?_⟩
      have different : entry.key ≠ loser.val := by
        intro equal
        exact same (Fin.ext (key.symm.trans equal))
      simpa using different
    · exact member

/-- Frozen instances inherit either historical orientation. Every active
persistent grower is chronological in its outward member-list direction. -/
def Histories {n : ℕ} (states : States n) : Prop :=
  ∀ owner side,
    (∀ b ∈ (states owner side).shrinking, ∃ orientation, HistMonotone orientation b.members) ∧
    (∀ g, (states owner side).grower=some g → HistMonotone true g.members)

def BeforeTime {n : ℕ} (time : ℕ) (states : States n) : Prop :=
  ∀ owner side entry, entry ∈ entries (states owner side) → entry.joined<time

theorem grow_history (entry : Entry) (grower : Grower)
    (history : HistMonotone true grower.members)
    (fresh : ∀ old ∈ grower.members, old.joined<entry.joined) :
    HistMonotone true (grow entry grower).members := by
  change (grower.members++[entry]).Pairwise (fun a b => a.joined<b.joined)
  apply List.pairwise_append.mpr
  refine ⟨history,by simp,?_⟩
  intro old member last only
  have same := List.mem_singleton.mp only
  simpa only [same] using fresh old member

theorem appendGrower_histories (entry : Entry) (state : SideState)
    (histories : (∀ b ∈ state.shrinking, ∃ orientation, HistMonotone orientation b.members) ∧
      (∀ g, state.grower=some g → HistMonotone true g.members))
    (fresh : ∀ old ∈ entries state, old.joined<entry.joined) :
    (∀ b ∈ (appendGrower entry state).shrinking,
      ∃ orientation, HistMonotone orientation b.members) ∧
    (∀ g, (appendGrower entry state).grower=some g → HistMonotone true g.members) := by
  refine ⟨histories.1,?_⟩
  intro after someAfter
  cases hg : state.grower with
  | none => simp [appendGrower,hg] at someAfter
  | some before =>
      have same : grow entry before=after := by simpa [appendGrower,hg] using someAfter
      rw [←same]
      apply grow_history entry before (histories.2 before hg)
      intro old member
      apply fresh old
      exact List.mem_append_right _ (by simpa [hg,growerEntries] using member)

theorem eraseFrozenKey_histories (key : ℕ) (state : SideState)
    (histories : (∀ b ∈ state.shrinking, ∃ orientation, HistMonotone orientation b.members) ∧
      (∀ g, state.grower=some g → HistMonotone true g.members)) :
    (∀ b ∈ (eraseFrozenKey key state).shrinking,
      ∃ orientation, HistMonotone orientation b.members) ∧
    (∀ g, (eraseFrozenKey key state).grower=some g → HistMonotone true g.members) := by
  refine ⟨?_,histories.2⟩
  intro after member
  obtain ⟨before,hbefore,rfl⟩ := List.mem_map.mp member
  obtain ⟨orientation,history⟩ := histories.1 before hbefore
  exact ⟨orientation,history.filter _⟩

theorem linkState_histories {n : ℕ} (states : States n) (source winner loser : External n)
    (sourceSide targetSide : Bool) (fresh : Entry)
    (histories : Histories states) (freshTime : BeforeTime fresh.joined states) :
    Histories (linkState states source winner loser sourceSide targetSide fresh) := by
  intro owner side
  unfold linkState
  split_ifs
  · exact appendGrower_histories fresh _ (histories owner side) (freshTime owner side)
  · exact eraseFrozenKey_histories loser.val _ (histories owner side)
  · exact histories owner side

theorem linkState_beforeTime {n : ℕ} (states : States n) (source winner loser : External n)
    (sourceSide targetSide : Bool) (fresh : Entry)
    (persistent : Persistent states)
    (emptySource : growerEntries (states source sourceSide).grower=[])
    (freshTime : BeforeTime fresh.joined states) :
    BeforeTime (fresh.joined+1) (linkState states source winner loser sourceSide targetSide fresh) := by
  intro owner side entry member
  rw [linkState_entries states source winner loser sourceSide targetSide fresh
    (persistent winner targetSide) emptySource] at member
  split_ifs at member
  · rcases List.mem_append.mp member with old | newEntry
    · have h := freshTime owner side entry old
      omega
    · have same := List.mem_singleton.mp newEntry
      subst entry
      omega
  · have h := freshTime owner side entry (List.mem_filter.mp member).1
    omega
  · have h := freshTime owner side entry member
    omega

end GreedyMerge.ActualLinks

#print axioms GreedyMerge.ActualLinks.linkState_sound
#print axioms GreedyMerge.ActualLinks.linkState_complete
#print axioms GreedyMerge.ActualLinks.linkState_ordered
#print axioms GreedyMerge.ActualLinks.linkState_persistent

#print axioms GreedyMerge.ActualLinks.linkState_histories
#print axioms GreedyMerge.ActualLinks.linkState_beforeTime
