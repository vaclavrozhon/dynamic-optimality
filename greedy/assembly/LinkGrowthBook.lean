import ActualGrowthBook
import ActualLinkRuns

/-! The same actual link fold updates a matched historical grower book.
Consequently all completed and current batches in every creator slot are
chronological, and no family name can return, throughout a whole access.
-/

namespace GreedyMerge.GrowthBook

open OrderedBlocks Primitives GrowthWindows HeapAllocation ActualLinks
open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical

abbrev HeapBooks (n : ℕ) := External n → Bool → SlotState

def HeapGood {n : ℕ} (clock next : ℕ) (states : HeapSides n) (books : HeapBooks n) : Prop :=
  ∀ owner side, Good clock next (states owner side) (books owner side)

def linkBook {n : ℕ} (winner : External n) (target : Bool) (time : ℕ)
    (books : HeapBooks n) : HeapBooks n :=
  fun owner side => if owner=winner ∧ side=target then appendEntry time (books owner side)
    else books owner side

theorem linkBook_good {n : ℕ} (clock next : ℕ) (states : HeapSides n) (books : HeapBooks n)
    (source winner loser : External n) (sourceSide targetSide : Bool) (entry : Entry)
    (time : entry.joined=clock) (good : HeapGood clock next states books) :
    HeapGood (clock+1) next
      (linkState states source winner loser sourceSide targetSide entry)
      (linkBook winner targetSide clock books) := by
  intro owner side
  unfold linkState linkBook
  split_ifs with target source
  · simpa only [time] using append_good entry clock next _ _ (good owner side) (by omega)
  · have preserved : Good clock next (eraseFrozenKey loser.val (states owner side)) (books owner side) :=
      (good owner side).grower_congr rfl
    exact preserved.advance (clock+1) next (by omega) (le_refl _)
  · exact (good owner side).advance _ _ (by omega) (le_refl _)

def runBook {n : ℕ} : ℕ → HeapBooks n → List (External n × External n) → HeapBooks n
  | _, books, [] => books
  | clock, books, event::rest =>
      runBook (clock+1) (linkBook event.1 (targetSide event) clock books) rest

theorem runBook_good {n : ℕ} (source : External n)
    (sourceSide : External n × External n → Bool) (reader : ℕ → States n → ℕ → ℤ)
    (clock next : ℕ) (states : HeapSides n) (books : HeapBooks n)
    (events : List (External n × External n)) (good : HeapGood clock next states books) :
    HeapGood (clock+events.length) next
      (runLinks source sourceSide reader clock states events) (runBook clock books events) := by
  induction events generalizing clock states books with
  | nil => simpa [runLinks,runBook] using good
  | cons event rest ih =>
      have first := linkBook_good clock next states books source event.1 event.2
        (sourceSide event) (targetSide event) (arrivalEntry (reader clock states) event.1 event.2 clock) rfl good
      have tail := ih (clock+1) _ _ first
      simpa only [runLinks,runBook,List.length_cons,Nat.add_assoc,Nat.add_comm 1] using tail

noncomputable def convertHeapBooks {n : ℕ} (selected : External n → Bool → Bool)
    (start : ℕ) (states : HeapSides n) (books : HeapBooks n) : HeapBooks n :=
  fun owner side => if selected owner side then
      convertBook (states owner side) (start+(encode n (owner,side)).val) (books owner side)
    else books owner side

theorem convertHeap_good {n : ℕ} (rank : ℕ → ℕ) (selected : External n → Bool → Bool)
    (clock start : ℕ) (states : HeapSides n) (books : HeapBooks n)
    (good : HeapGood clock start states books) :
    HeapGood clock (start+2*(2*n+1)) (convertHeap rank selected start states).1
      (convertHeapBooks selected start states books) := by
  intro owner side
  rw [convertHeap_apply]
  unfold convertHeapBooks
  split_ifs
  · have size := (encode n (owner,side)).isLt
    have size' : (encode n (owner,side)).val < 2*(2*n+1) := by
      simpa only [slot_count] using size
    exact convert_good _ _ _ _ clock start _ _ _ (good owner side) (by omega) (by omega)
  · exact (good owner side).advance _ _ (le_refl _) (by omega)

theorem initial_heap_good {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n) (K : ℤ) :
    HeapGood (InitialBlocks.epoch n) (2*(2*n+1)) (InitialBlocks.state snapshot tree K)
      (initial snapshot tree K) := initial_good snapshot tree K

/-- The overlap fact is now read from the actual matched book at the end
of the access. The hypotheses concern only the already established input
book invariant and the literal execution, not an overlap certificate. -/
theorem runBook_one_active {n : ℕ} (source : External n)
    (sourceSide : External n × External n → Bool) (reader : ℕ → States n → ℕ → ℤ)
    (clock next : ℕ) (states : HeapSides n) (books : HeapBooks n)
    (events : List (External n × External n)) (good : HeapGood clock next states books)
    (owner : External n) (side : Bool) (first second time : ℕ)
    (firstStart : growthStart first (journal (runBook clock books events owner side))≤time)
    (firstEnd : time<growthEnd first (journal (runBook clock books events owner side)))
    (secondStart : growthStart second (journal (runBook clock books events owner side))≤time)
    (secondEnd : time<growthEnd second (journal (runBook clock books events owner side))) : first=second :=
  one_active_family _
    ((runBook_good source sourceSide reader clock next states books events good) owner side).ordered
    first second time firstStart firstEnd secondStart secondEnd

end GreedyMerge.GrowthBook

#print axioms GreedyMerge.GrowthBook.runBook_good
#print axioms GreedyMerge.GrowthBook.convertHeap_good
#print axioms GreedyMerge.GrowthBook.runBook_one_active
