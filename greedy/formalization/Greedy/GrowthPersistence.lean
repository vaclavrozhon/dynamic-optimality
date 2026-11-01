import Greedy.GrowthAdministration

/-!
# Persistent membership times in historical grower books

Closing a grower retains every family/time pair; appending an entry adds
one such pair. These statements hold for the literal administrative and
access book programs, so future final books retain earlier source times.
-/

namespace Greedy.GrowthJournal

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.HeapAllocation
open GreedyMerge.GrowthBook GreedyMerge.GrowthWindows GreedyMerge.ActualLinks GreedyMerge.ComparatorOuter

def Extends (first last : SlotState) : Prop :=
  ∀ family time, time ∈ collect family (journal first) → time ∈ collect family (journal last)

def HeapExtends {n : ℕ} (first last : HeapBooks n) : Prop := ∀ owner side, Extends (first owner side) (last owner side)

theorem Extends.refl (book : SlotState) : Extends book book := fun _ _ member => member

theorem Extends.trans {first middle last : SlotState} (firstStep : Extends first middle) (lastStep : Extends middle last) :
    Extends first last := fun family time member => lastStep family time (firstStep family time member)

theorem HeapExtends.refl {n : ℕ} (books : HeapBooks n) : HeapExtends books books := fun _ _ => Extends.refl _

theorem HeapExtends.trans {n : ℕ} {first middle last : HeapBooks n}
    (firstStep : HeapExtends first middle) (lastStep : HeapExtends middle last) : HeapExtends first last :=
  fun owner side => (firstStep owner side).trans (lastStep owner side)

theorem replace_extends (family : ℕ) (book : SlotState) : Extends book (replace family book) := by
  intro name time member
  simpa [collect, journal, replace, List.flatMap_append] using member

theorem append_extends (time : ℕ) (book : SlotState) : Extends book (appendEntry time book) := by
  intro family joined member
  have expand (current : Batch) : collect family (book.closed ++ [current]) =
      collect family book.closed ++ if current.family = family then current.joined else [] := by
    simp [collect, List.flatMap_append]
  rw [journal, expand] at member
  change joined ∈ collect family (book.closed ++ [⟨book.current.family, book.current.joined ++ [time]⟩])
  rw [expand]
  split_ifs with same
  · change book.current.family = family at same
    simp only [same, ↓reduceIte, List.mem_append] at member
    exact List.mem_append.mpr (member.elim Or.inl (fun mem => Or.inr (List.mem_append_left _ mem)))
  · change book.current.family ≠ family at same
    simpa only [same, ↓reduceIte, List.append_nil] using member

theorem convertBook_extends (state : SideState) (fresh : ℕ) (book : SlotState) : Extends book (convertBook state fresh book) := by
  unfold convertBook
  split <;> rename_i h
  · exact Extends.refl _
  · split_ifs
    · exact Extends.refl _
    · exact replace_extends _ _

theorem convertHeapBooks_extends {n : ℕ} (selected : External n → Bool → Bool) (start : ℕ)
    (states : HeapSides n) (books : HeapBooks n) : HeapExtends books (convertHeapBooks selected start states books) := by
  intro owner side
  unfold convertHeapBooks
  split_ifs
  · exact convertBook_extends _ _ _
  · exact Extends.refl _

theorem detachBooks_extends {n : ℕ} (before : BST 0 n) (start : ℕ) (ports : List ℕ)
    (stage : ℕ) (states : HeapSides n) (books : HeapBooks n) :
    HeapExtends books (detachBooks before start ports stage states books) := by
  induction ports generalizing stage states books with
  | nil => exact HeapExtends.refl _
  | cons record rest ih => exact (convertHeapBooks_extends _ _ states books).trans (ih _ _ _)

theorem preparationBooks_extends {n : ℕ} (before after : BST 0 n) (start : ℕ)
    (ports : List ℕ) (owners : Finset (External n)) (states : HeapSides n) (books : HeapBooks n) :
    HeapExtends books (preparationBooks before after start ports owners states books) := by
  classical
  exact (convertHeapBooks_extends _ start states books).trans
    ((detachBooks_extends before start ports 1 _ _).trans (convertHeapBooks_extends _ _ _ _))

theorem restoreBook_extends {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n)
    (record : External n) (start : ℕ) (states : HeapSides n) (books : HeapBooks n) :
    HeapExtends books (restoreBook snapshot tree record start states books) := by
  intro owner side
  cases parent : canonicalParent snapshot tree record <;> simp only [restoreBook, parent]
  · exact Extends.refl _
  · split_ifs
    · exact convertBook_extends _ _ _
    · exact Extends.refl _

theorem restorationBooks_extends {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n)
    (reader : ℕ → HeapSides n → External n → External n → Entry)
    (ports : List (External n)) (stage start : ℕ) (states : HeapSides n) (books : HeapBooks n) :
    HeapExtends books (restorationBooks snapshot tree reader ports stage start states books) := by
  induction ports generalizing stage start states books with
  | nil => exact HeapExtends.refl _
  | cons record rest ih => exact (restoreBook_extends snapshot tree record start states books).trans (ih _ _ _ _)

theorem comparatorBooks_extends {n a b depth : ℕ} {before after : BST 0 n}
    (profile : RotationCutProfile before after depth) (tree : BST 0 n)
    (plan : RotationPlan before after tree a b)
    (reader : ℕ → HeapSides n → External n → External n → Entry)
    (start : ℕ) (states : HeapSides n) (books : HeapBooks n) :
    HeapExtends books (comparatorBooks profile tree plan reader start states books) := by
  cases plan with
  | quiet => exact preparationBooks_extends before after start [] ∅ states books
  | junction => exact (preparationBooks_extends before after start _ _ states books).trans (by apply restorationBooks_extends)

theorem refinementBooks_extends {n : ℕ} (comparator tree : BST 0 n)
    (ports : List (External n)) (reader : ℕ → HeapSides n → External n → External n → Entry)
    (start : ℕ) (states : HeapSides n) (books : HeapBooks n) :
    HeapExtends books (refinementBooks comparator tree ports reader start states books) :=
  (detachBooks_extends comparator start (ports.map Fin.val) 0 states books).trans (by apply restorationBooks_extends)

theorem linkBook_extends {n : ℕ} (winner : External n) (side : Bool) (time : ℕ) (books : HeapBooks n) :
    HeapExtends books (linkBook winner side time books) := by
  intro owner currentSide
  unfold linkBook
  split_ifs
  · exact append_extends _ _
  · exact Extends.refl _

theorem runBook_extends {n : ℕ} (clock : ℕ) (books : HeapBooks n) (events : List (External n × External n)) :
    HeapExtends books (runBook clock books events) := by
  induction events generalizing clock books with
  | nil => exact HeapExtends.refl _
  | cons event rest ih => exact (linkBook_extends event.1 (targetSide event) clock books).trans (ih _ _)

end Greedy.GrowthJournal
