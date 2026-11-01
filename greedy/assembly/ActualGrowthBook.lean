import GrowthWindows
import HeapFreshAllocation
import ActualLinkState

/-! Growth windows read from the physical persistent growers. The book
keeps completed batches after conversion; therefore its freshness and time
bounds also cover entries and families that are no longer live.
-/

namespace GreedyMerge.GrowthBook

open OrderedBlocks Primitives GrowthWindows
open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical

def batch (grower : Grower) : Batch := ⟨grower.family, grower.members.map Entry.joined⟩

def Matches (state : SideState) (book : SlotState) : Prop :=
  ∃ grower, state.grower=some grower ∧ book.current=batch grower

def Before (clock : ℕ) (book : SlotState) : Prop :=
  ∀ time∈allTimes (journal book), time<clock

def Below (next : ℕ) (book : SlotState) : Prop :=
  ∀ family∈(journal book).map Batch.family, family<next

def convertBook (state : SideState) (fresh : ℕ) (book : SlotState) : SlotState :=
  match state.grower with
  | none => book
  | some grower => if grower.members=[] then book else replace fresh book

theorem convert_matches (owner fresh id base : ℕ) (state : SideState) (book : SlotState)
    (matched : Matches state book) :
    Matches (convert owner fresh id base state) (convertBook state fresh book) := by
  obtain ⟨grower, present, same⟩ := matched
  by_cases empty : grower.members=[]
  · simpa only [convert, convertBook, present, if_pos empty] using
      (show Matches state book from ⟨grower,present,same⟩)
  · refine ⟨emptyGrower owner fresh id, ?_, ?_⟩
    · simp [convert,present,empty]
    · simp [convertBook,present,empty,replace,batch,emptyGrower]

theorem convert_run (fresh start : ℕ) (state : SideState) (book : SlotState)
    (old : Below start book) (new : start≤fresh) :
    SlotRun book (convertBook state fresh book) := by
  have unused : fresh∉(journal book).map Batch.family := by
    intro member
    have bound := old fresh member
    omega
  unfold convertBook
  cases state.grower with
  | none => exact .nil _
  | some grower =>
      dsimp only
      split_ifs
      · exact .nil _
      · exact .cons (.replace book fresh unused) (.nil _)

theorem convert_before (fresh clock : ℕ) (state : SideState) (book : SlotState)
    (before : Before clock book) : Before clock (convertBook state fresh book) := by
  unfold convertBook
  cases state.grower with
  | none => exact before
  | some grower =>
      dsimp only
      split_ifs
      · exact before
      · simpa only [Before,replace_times] using before

theorem convert_below (fresh start next : ℕ) (state : SideState) (book : SlotState)
    (old : Below start book) (advance : start≤next) (new : fresh<next) :
    Below next (convertBook state fresh book) := by
  have oldNext : Below next book := fun family member => lt_of_lt_of_le (old family member) advance
  unfold convertBook
  cases state.grower with
  | none => exact oldNext
  | some grower =>
      dsimp only
      split_ifs
      · exact oldNext
      · intro family member
        rw [replace_families] at member
        rcases List.mem_append.mp member with earlier | born
        · exact oldNext family earlier
        · simpa only [List.mem_singleton.mp born] using new

theorem append_matches (entry : Entry) (state : SideState) (book : SlotState)
    (matched : Matches state book) :
    Matches (ActualLinks.appendGrower entry state) (appendEntry entry.joined book) := by
  obtain ⟨grower,present,same⟩ := matched
  refine ⟨grow entry grower, ?_, ?_⟩
  · simp [ActualLinks.appendGrower,present]
  · simp [appendEntry,same,batch,grow]

theorem append_run (entry : Entry) (book : SlotState) (before : Before entry.joined book) :
    SlotRun book (appendEntry entry.joined book) :=
  .cons (.append book entry.joined before) (.nil _)

theorem append_before (entry : Entry) (clock : ℕ) (book : SlotState)
    (before : Before clock book) (fresh : clock≤entry.joined) :
    Before (entry.joined+1) (appendEntry entry.joined book) := by
  intro time member
  rw [appendEntry_times] at member
  rcases List.mem_append.mp member with old | born
  · have bound := before time old
    omega
  · have equal := List.mem_singleton.mp born
    omega

theorem append_below (entry : Entry) (next : ℕ) (book : SlotState) (old : Below next book) :
    Below next (appendEntry entry.joined book) := by
  simpa only [Below,appendEntry_families] using old

theorem matches_grower_congr (first second : SideState) (book : SlotState)
    (same : first.grower=second.grower) (matched : Matches first book) : Matches second book := by
  obtain ⟨grower,present,current⟩ := matched
  exact ⟨grower,same.symm.trans present,current⟩

noncomputable def initial {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n) (K : ℤ)
    (owner : External n) (side : Bool) : SlotState :=
  ⟨[],⟨InitialBlocks.slot owner side,
    ((InitialBlocks.children snapshot tree owner side).map
      (InitialBlocks.entry snapshot tree K owner side)).map Entry.joined⟩⟩

theorem initial_matches {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n) (K : ℤ)
    (owner : External n) (side : Bool) :
    Matches (InitialBlocks.state snapshot tree K owner side) (initial snapshot tree K owner side) :=
  ⟨_,rfl,rfl⟩

theorem initial_valid {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n) (K : ℤ)
    (owner : External n) (side : Bool) :
    GrowthWindows.Valid (journal (initial snapshot tree K owner side)) := by
  constructor
  · simp [journal,initial]
  · have ordered := InitialBlocks.state_history snapshot tree K owner side
    simpa [allTimes,journal,initial,List.pairwise_map,HistMonotone,
      InitialBlocks.state,growerEntries] using ordered

theorem initial_before {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n) (K : ℤ)
    (owner : External n) (side : Bool) :
    Before (InitialBlocks.epoch n) (initial snapshot tree K owner side) := by
  intro time member
  simp only [allTimes,journal,initial,List.nil_append,List.flatMap_cons,List.flatMap_nil,
    List.append_nil,List.mem_map] at member
  obtain ⟨entry,⟨record,_,rfl⟩,rfl⟩ := member
  exact InitialBlocks.ticket_before_epoch owner record side

theorem initial_below {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n) (K : ℤ)
    (owner : External n) (side : Bool) :
    Below (2*(2*n+1)) (initial snapshot tree K owner side) := by
  intro family member
  have same : family=InitialBlocks.slot owner side := by simpa [journal,initial] using member
  rw [same]
  exact List.mem_range.mp (InitialBlocks.slot_mem_birthIds owner side)

structure Good (clock next : ℕ) (state : SideState) (book : SlotState) : Prop where
  matched : Matches state book
  ordered : GrowthWindows.Valid (journal book)
  before : Before clock book
  below : Below next book

theorem Good.advance {clock next : ℕ} {state : SideState} {book : SlotState}
    (good : Good clock next state book) (newClock newNext : ℕ)
    (later : clock≤newClock) (more : next≤newNext) : Good newClock newNext state book :=
  ⟨good.matched,good.ordered,
    fun time member => lt_of_lt_of_le (good.before time member) later,
    fun family member => lt_of_lt_of_le (good.below family member) more⟩

theorem Good.grower_congr {clock next : ℕ} {first second : SideState} {book : SlotState}
    (good : Good clock next first book) (same : first.grower=second.grower) :
    Good clock next second book :=
  ⟨matches_grower_congr first second book same good.matched, good.ordered,good.before,good.below⟩

theorem convert_good (owner fresh id base clock start next : ℕ)
    (state : SideState) (book : SlotState) (good : Good clock start state book)
    (new : start≤fresh) (bound : fresh<next) :
    Good clock next (convert owner fresh id base state) (convertBook state fresh book) :=
  ⟨convert_matches owner fresh id base state book good.matched,
    (convert_run fresh start state book good.below new).valid good.ordered,
    convert_before fresh clock state book good.before,
    convert_below fresh start next state book good.below (by omega) bound⟩

theorem append_good (entry : Entry) (clock next : ℕ) (state : SideState) (book : SlotState)
    (good : Good clock next state book) (fresh : clock≤entry.joined) :
    Good (entry.joined+1) next (ActualLinks.appendGrower entry state) (appendEntry entry.joined book) :=
  ⟨append_matches entry state book good.matched,
    (append_run entry book (fun time member => lt_of_lt_of_le (good.before time member) fresh)).valid good.ordered,
    append_before entry clock book good.before fresh,append_below entry next book good.below⟩

theorem initial_good {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n) (K : ℤ)
    (owner : External n) (side : Bool) :
    Good (InitialBlocks.epoch n) (2*(2*n+1)) (InitialBlocks.state snapshot tree K owner side)
      (initial snapshot tree K owner side) :=
  ⟨initial_matches _ _ _ _ _,initial_valid _ _ _ _ _,initial_before _ _ _ _ _,initial_below _ _ _ _ _⟩

def conversionBooks {slots : ℕ} (selected : Fin slots → Bool) (start : ℕ)
    (states : Fin slots → SideState) (books : Fin slots → SlotState) : Fin slots → SlotState :=
  fun slot => if selected slot then convertBook (states slot) (start+slot.val) (books slot) else books slot

theorem freshConversions_good {slots : ℕ} (owner base : Fin slots → ℕ) (selected : Fin slots → Bool)
    (clock start : ℕ) (states : Fin slots → SideState) (books : Fin slots → SlotState)
    (good : ∀ slot, Good clock start (states slot) (books slot)) :
    ∀ slot, Good clock (FreshIds.freshConversions owner base selected start states).2
      ((FreshIds.freshConversions owner base selected start states).1 slot)
      (conversionBooks selected start states books slot) := by
  intro slot
  dsimp only [FreshIds.freshConversions,conversionBooks]
  split_ifs
  · exact convert_good _ _ _ _ clock start _ _ _ (good slot) (by omega) (by omega)
  · exact (good slot).advance _ _ (le_refl _) (by omega)

end GreedyMerge.GrowthBook

#print axioms GreedyMerge.GrowthBook.initial_valid
#print axioms GreedyMerge.GrowthBook.convert_run
#print axioms GreedyMerge.GrowthBook.append_matches
#print axioms GreedyMerge.GrowthBook.freshConversions_good
