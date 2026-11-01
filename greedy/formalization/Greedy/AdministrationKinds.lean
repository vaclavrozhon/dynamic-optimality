import Greedy.AdministrationJournal
import Greedy.JournalKinds

/-! Administration creates only ordinary entries in the actual journal. -/

namespace Greedy.AdministrationKinds

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.HeapAllocation
open GreedyMerge.ComparatorOuter EntryJournal RestorationJournal AdministrationJournal

theorem one_ordinary {n : ℕ} (comparator tree : BST 0 n) (K : ℤ)
    (names : PaidNames) (makeEntry : External n → Entry) (record : External n) (states : HeapSides n) :
    OrdinaryOnly (one comparator tree K names makeEntry record states) := by
  cases parent : canonicalParent (Snapshot.ofTree comparator) tree record with
  | none => simp [one, parent, OrdinaryOnly]
  | some owner =>
      intro action member
      simp only [one, parent] at member
      rcases List.mem_cons.mp member with equal | tail
      · subst action; rfl
      · exact ordinaryOnly_batch _ action tail

theorem program_ordinary {n : ℕ} (comparator tree : BST 0 n) (K : ℤ)
    (reader : ℕ → HeapSides n → External n → External n → Entry)
    (ports : List (External n)) (stage start : ℕ) (states : HeapSides n) :
    OrdinaryOnly (RestorationJournal.program comparator tree K reader ports stage start states) := by
  induction ports generalizing stage start states with
  | nil => simp [RestorationJournal.program, OrdinaryOnly]
  | cons record rest ih =>
      apply (ordinaryOnly_append ..).mpr
      exact ⟨one_ordinary comparator tree K _ _ record states, ih _ _ _⟩

theorem administration_ordinary {n : ℕ} (comparator tree : BST 0 n) (K : ℤ)
    (reader : ℕ → HeapSides n → External n → External n → Entry)
    (ports : List (External n)) (stage start : ℕ) (states : HeapSides n) :
    OrdinaryOnly (administration comparator tree K reader ports stage start states) :=
  (ordinaryOnly_append ..).mpr ⟨ordinaryOnly_batch _, program_ordinary comparator tree K reader ports stage start states⟩

theorem plan_ordinary {n a b depth : ℕ} {before after : BST 0 n}
    (profile : RotationCutProfile before after depth) (tree : BST 0 n)
    (plan : RotationPlan before after tree a b) (K : ℤ)
    (reader : ℕ → HeapSides n → External n → External n → Entry)
    (start : ℕ) (states : HeapSides n) : OrdinaryOnly (planJournal profile tree plan K reader start states) := by
  apply administration_ordinary

theorem refinement_ordinary {n : ℕ} (comparator afterTree : BST 0 n) (K : ℤ)
    (ports : List (External n)) (reader : ℕ → HeapSides n → External n → External n → Entry)
    (start : ℕ) (states : HeapSides n) :
    OrdinaryOnly (AdministrationJournal.refinement comparator afterTree K ports reader start states) := by
  apply administration_ordinary

end Greedy.AdministrationKinds
