import Greedy.GrowthPreparationInvariant

/-! Paid singleton creation preserves coverage by complete growth histories. -/

namespace Greedy.GrowthJournal

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.HeapAllocation
open GreedyMerge.GrowthBook GreedyMerge.GrowthWindows

theorem restoreBook_invariant {n clock : ℕ} (snapshot : Snapshot n) (tree : BST 0 n)
    (record : External n) (makeEntry : External n → Entry) (start : ℕ)
    (states : HeapSides n) (books : HeapBooks n) (inv : Invariant clock start states books) :
    Invariant clock (restoreNext snapshot tree record start states)
      (restorePort snapshot tree (portNames snapshot tree record start states) makeEntry record states).1
      (restoreBook snapshot tree record start states books) := by
  refine ⟨restoreBook_good snapshot tree record makeEntry clock start states books inv.good, ?_, ?_⟩
  · intro current side grower present
    cases parent : canonicalParent snapshot tree record with
    | none => exact inv.creators current side grower (by simpa [restorePort, parent] using present)
    | some owner =>
        simp only [restorePort, parent, replaceSide] at present
        split_ifs at present with selected
        · obtain ⟨sameOwner, sameSide⟩ := selected
          subst current
          subst side
          exact convert_creator owner.val _ _ (snapshot.rank owner) _
            (inv.creators owner _) grower present
        · exact inv.creators current side grower present
  · intro current side block member
    have extension := restoreBook_extends snapshot tree record start states books
    cases parent : canonicalParent snapshot tree record with
    | none =>
        have old := inv.covered current side block (by simpa [restorePort, parent] using member)
        exact old.mono extension
    | some owner =>
        simp only [restorePort, parent, replaceSide] at member
        split_ifs at member with selected
        · obtain ⟨sameOwner, sameSide⟩ := selected
          subst current
          subst side
          apply installPaid_covered _ owner.val _ _ _ _ _ _ _ _ block member
          exact convert_covered books _ owner _ _ _ _ _
            (inv.covered owner _) (inv.good owner _).matched (inv.creators owner _) extension
        · exact (inv.covered current side block member).mono extension

theorem restorationBooks_invariant {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n)
    (reader : ℕ → HeapSides n → External n → External n → Entry)
    (ports : List (External n)) (clock stage start : ℕ) (states : HeapSides n) (books : HeapBooks n)
    (inv : Invariant clock start states books) :
    let result := freshRestorePorts snapshot tree reader ports stage start states
    Invariant clock result.next result.states (restorationBooks snapshot tree reader ports stage start states books) := by
  induction ports generalizing stage start states books with
  | nil => exact inv
  | cons record rest ih =>
      exact ih (stage+1) _ _ _ (restoreBook_invariant snapshot tree record (reader stage states record) start states books inv)

end Greedy.GrowthJournal
