import OrderedPaidInsertion

/-!
Concrete paid-port detachment. A growing source is selected by its actual
member key, sealed, and only then filtered. Actual parent soundness makes
that selected side unique over the entire heap, so one port causes at most
one replacement-growing-instance birth.
-/
namespace GreedyMerge.OrderedBlocks

open GreedyMerge.Primitives (Entry)
open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical

def growerHasKey (key : ℕ) (state : SideState) : Bool :=
  (growerEntries state.grower).any (fun entry => entry.key == key)

def sealPortSource (owner freshFamily freshId base key : ℕ) (state : SideState) : SideState :=
  if growerHasKey key state then convert owner freshFamily freshId base state else state

def eraseFrozenKey (key : ℕ) (state : SideState) : SideState :=
  ⟨state.shrinking.map (eraseMember key), state.grower⟩

def detachPort (owner freshFamily freshId base key : ℕ) (state : SideState) : SideState :=
  eraseFrozenKey key (sealPortSource owner freshFamily freshId base key state)

theorem sealPortSource_entries (owner freshFamily freshId base key : ℕ) (state : SideState) :
    entries (sealPortSource owner freshFamily freshId base key state) = entries state := by
  unfold sealPortSource
  split_ifs <;> simp

theorem sealPortSource_valid (owner freshFamily freshId base key : ℕ) (side : Bool)
    (state : SideState) (valid : Valid owner side state) :
    Valid owner side (sealPortSource owner freshFamily freshId base key state) := by
  unfold sealPortSource
  split_ifs
  · exact conversion_valid owner freshFamily freshId base side state valid
  · exact valid

theorem sealPortSource_grower_absent (owner freshFamily freshId base key : ℕ) (state : SideState) :
    ∀ entry ∈ growerEntries (sealPortSource owner freshFamily freshId base key state).grower,
      entry.key ≠ key := by
  unfold sealPortSource
  split_ifs with selected
  · simp only [converted_grower_empty, List.not_mem_nil, false_implies, implies_true]
  · intro entry member same
    apply selected
    apply List.any_eq_true.mpr
    exact ⟨entry, member, by simpa using same⟩

theorem eraseFrozenKey_flat (key : ℕ) (blocks : List Frozen) :
    frozenEntries (blocks.map (eraseMember key)) =
      (frozenEntries blocks).filter (fun entry => entry.key != key) := by
  induction blocks with
  | nil => rfl
  | cons block rest ih =>
      change block.members.filter (fun entry => entry.key != key) ++
        frozenEntries (rest.map (eraseMember key)) =
        (block.members ++ frozenEntries rest).filter (fun entry => entry.key != key)
      rw [List.filter_append, ih]

theorem detachPort_entries (owner freshFamily freshId base key : ℕ) (state : SideState) :
    entries (detachPort owner freshFamily freshId base key state) =
      (entries state).filter (fun entry => entry.key != key) := by
  have absent := sealPortSource_grower_absent owner freshFamily freshId base key state
  have growerUnchanged :
      (growerEntries (sealPortSource owner freshFamily freshId base key state).grower).filter
        (fun entry => entry.key != key) =
      growerEntries (sealPortSource owner freshFamily freshId base key state).grower := by
    apply List.filter_eq_self.mpr
    intro entry member
    simpa using absent entry member
  unfold detachPort eraseFrozenKey
  simp only [entries, eraseFrozenKey_flat, List.filter_append]
  rw [←growerUnchanged]
  rw [←List.filter_append]
  simpa only [entries, List.filter_append] using
    congrArg (List.filter (fun entry => entry.key != key))
      (sealPortSource_entries owner freshFamily freshId base key state)

theorem detachPort_valid (owner freshFamily freshId base key : ℕ) (side : Bool)
    (state : SideState) (valid : Valid owner side state) :
    Valid owner side (detachPort owner freshFamily freshId base key state) := by
  have sealed := sealPortSource_valid owner freshFamily freshId base key side state valid
  refine ⟨?_, ?_, sealed.2.2⟩
  · rw [detachPort_entries]
    exact valid.1.filter _
  · intro entry member
    rw [detachPort_entries] at member
    exact valid.2.1 entry (List.mem_filter.mp member).1

theorem detachPort_sound {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n)
    (owner : External n) (freshFamily freshId base key : ℕ) (state : SideState)
    (sound : ParentSound snapshot tree owner state) :
    ParentSound snapshot tree owner (detachPort owner.val freshFamily freshId base key state) := by
  intro entry member
  rw [detachPort_entries] at member
  exact sound entry (List.mem_filter.mp member).1

/-- A fixed physical key can occur in at most one owner/side location,
using real canonical parents and strict side order. -/
theorem key_location_unique {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n)
    (states : External n → Bool → SideState)
    (valid : ∀ owner side, Valid owner.val side (states owner side))
    (sound : ∀ owner side, ParentSound snapshot tree owner (states owner side))
    {firstOwner secondOwner : External n} {firstSide secondSide : Bool}
    {firstEntry secondEntry : Entry}
    (firstMem : firstEntry ∈ entries (states firstOwner firstSide))
    (secondMem : secondEntry ∈ entries (states secondOwner secondSide))
    (sameKey : firstEntry.key = secondEntry.key) :
    firstOwner = secondOwner ∧ firstSide = secondSide := by
  obtain ⟨firstRecord, firstKey, firstParent⟩ := sound firstOwner firstSide firstEntry firstMem
  obtain ⟨secondRecord, secondKey, secondParent⟩ := sound secondOwner secondSide secondEntry secondMem
  have recordEq : firstRecord = secondRecord := Fin.ext (by omega)
  have ownerEq : firstOwner = secondOwner := by
    rw [recordEq, secondParent] at firstParent
    exact (Option.some.inj firstParent).symm
  refine ⟨ownerEq, ?_⟩
  have firstSideFact := (valid firstOwner firstSide).2.1 firstEntry firstMem
  have secondSideFact := (valid secondOwner secondSide).2.1 secondEntry secondMem
  cases firstSide <;> cases secondSide <;> simp_all [onSide] <;> omega

noncomputable def portSources {n : ℕ} (key : ℕ) (states : External n → Bool → SideState) :
    Finset (External n × Bool) :=
  Finset.univ.filter (fun place => growerHasKey key (states place.1 place.2))

theorem portSources_card_le_one {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n)
    (key : ℕ) (states : External n → Bool → SideState)
    (valid : ∀ owner side, Valid owner.val side (states owner side))
    (sound : ∀ owner side, ParentSound snapshot tree owner (states owner side)) :
    (portSources key states).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro first firstMem second secondMem
  have firstHas : growerHasKey key (states first.1 first.2) = true := (Finset.mem_filter.mp firstMem).2
  have secondHas : growerHasKey key (states second.1 second.2) = true := (Finset.mem_filter.mp secondMem).2
  obtain ⟨firstEntry, firstEntryMem, firstEq⟩ := List.any_eq_true.mp firstHas
  obtain ⟨secondEntry, secondEntryMem, secondEq⟩ := List.any_eq_true.mp secondHas
  have firstEntryKey : firstEntry.key = key := by simpa using firstEq
  have secondEntryKey : secondEntry.key = key := by simpa using secondEq
  have pair := key_location_unique snapshot tree states valid sound
    (List.mem_append_right _ firstEntryMem) (List.mem_append_right _ secondEntryMem)
    (firstEntryKey.trans secondEntryKey.symm)
  exact Prod.ext pair.1 pair.2

/-- A selected source conversion creates exactly one replacement;
nonselected sources create none. Deletion itself creates no instance. -/
theorem portSource_births_exact (owner freshFamily freshId base key : ℕ) (state : SideState) :
    (sealPortSource owner freshFamily freshId base key state).shrinking.length =
      state.shrinking.length + if growerHasKey key state then 1 else 0 := by
  unfold sealPortSource
  split_ifs with selected
  · obtain ⟨entry, member, _⟩ := List.any_eq_true.mp selected
    cases same : state.grower with
    | none => simp [growerEntries, same] at member
    | some old =>
        have nonempty : old.members ≠ [] := by
          apply List.ne_nil_of_mem
          simpa [growerEntries, same] using member
        simp [convert, same, nonempty]
  · simp

#print axioms detachPort_valid
#print axioms detachPort_entries
#print axioms portSources_card_le_one

end GreedyMerge.OrderedBlocks
