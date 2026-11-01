import Greedy.GrowthPreparation
import FreshPortRestoration

/-!
# Historical grower books through literal paid restoration

A paid entry forms a frozen singleton family. It closes the receiving
current grower but is not appended to its replacement grower. Consequently
only the conversion changes the historical grower book; singleton families
have zero-length growth windows and are accounted for separately.
-/

namespace Greedy.GrowthJournal

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.HeapAllocation
open GreedyMerge.GrowthBook GreedyMerge.GrowthWindows

noncomputable def restoreBook {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n)
    (record : External n) (start : ℕ) (states : HeapSides n) (books : HeapBooks n) : HeapBooks n :=
  match canonicalParent snapshot tree record with
  | none => books
  | some owner => fun current side =>
      if current = owner ∧ side = decide (record.val < owner.val) then
        convertBook (states current side) start (books current side)
      else books current side

theorem restoreBook_good {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n)
    (record : External n) (makeEntry : External n → Entry) (clock start : ℕ)
    (states : HeapSides n) (books : HeapBooks n) (good : HeapGood clock start states books) :
    HeapGood clock (restoreNext snapshot tree record start states)
      (restorePort snapshot tree (portNames snapshot tree record start states) makeEntry record states).1
      (restoreBook snapshot tree record start states books) := by
  cases parent : canonicalParent snapshot tree record with
  | none => simpa only [restorePort, restoreNext, restoreBook, parent] using good
  | some owner =>
      let targetSide := decide (record.val < owner.val)
      let next := restoreNext snapshot tree record start states
      have new : start < next := by simp [next, restoreNext, portNames, parent, GreedyMerge.FreshIds.freshPaidNames]; omega
      intro current side
      by_cases selected : current = owner ∧ side = targetSide
      · obtain ⟨sameOwner, sameSide⟩ := selected
        subst current
        subst side
        have converted := convert_good owner.val start start (snapshot.rank owner) clock start next
          (states owner targetSide) (books owner targetSide) (good owner targetSide) (le_refl _) new
        have inserted := converted.grower_congr (second :=
          paidInsertion owner.val targetSide start start
            (GreedyMerge.FreshIds.freshPaidNames owner.val (snapshot.rank owner) start (states owner targetSide)).splitStart
            (GreedyMerge.FreshIds.freshPaidNames owner.val (snapshot.rank owner) start (states owner targetSide)).paidId
            (GreedyMerge.FreshIds.freshPaidNames owner.val (snapshot.rank owner) start (states owner targetSide)).paidFamily
            (snapshot.rank owner) (makeEntry owner) (states owner targetSide)) rfl
        simpa only [restorePort, portNames, parent, replaceSide, restoreBook, targetSide, and_self,
          ↓reduceIte, GreedyMerge.FreshIds.freshPaidNames] using inserted
      · have same : ¬ (current = owner ∧ side = decide (record.val < owner.val)) := selected
        simpa only [restorePort, parent, replaceSide, restoreBook, same, ↓reduceIte] using
          (good current side).advance clock next (le_refl _) (Nat.le_of_lt new)

noncomputable def restorationBooks {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n)
    (reader : ℕ → HeapSides n → External n → External n → Entry) :
    List (External n) → ℕ → ℕ → HeapSides n → HeapBooks n → HeapBooks n
  | [], _, _, _, books => books
  | record :: rest, stage, start, states, books =>
      let names := portNames snapshot tree record start states
      let restored := restorePort snapshot tree names (reader stage states record) record states
      restorationBooks snapshot tree reader rest (stage+1) (restoreNext snapshot tree record start states) restored.1
        (restoreBook snapshot tree record start states books)

theorem restorationBooks_good {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n)
    (reader : ℕ → HeapSides n → External n → External n → Entry)
    (ports : List (External n)) (clock stage start : ℕ) (states : HeapSides n) (books : HeapBooks n)
    (good : HeapGood clock start states books) :
    let result := freshRestorePorts snapshot tree reader ports stage start states
    HeapGood clock result.next result.states (restorationBooks snapshot tree reader ports stage start states books) := by
  induction ports generalizing stage start states books with
  | nil => exact good
  | cons record rest ih =>
      exact ih (stage+1) _ _ _ (restoreBook_good snapshot tree record (reader stage states record) clock start states books good)

end Greedy.GrowthJournal
