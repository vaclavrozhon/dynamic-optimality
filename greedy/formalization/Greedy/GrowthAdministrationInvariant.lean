import Greedy.GrowthRestorationInvariant
import Greedy.GrowthAccessInvariant

/-! Every administrative macro preserves full historical family coverage. -/

namespace Greedy.GrowthJournal

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.HeapAllocation
open GreedyMerge.GrowthBook GreedyMerge.GrowthWindows GreedyMerge.ComparatorOuter

theorem comparatorBooks_invariant {n a b depth : ℕ} {before after : BST 0 n}
    (profile : RotationCutProfile before after depth) (tree : BST 0 n)
    (plan : RotationPlan before after tree a b)
    (reader : ℕ → HeapSides n → External n → External n → Entry)
    (clock start : ℕ) (states : HeapSides n) (books : HeapBooks n) (inv : Invariant clock start states books) :
    let result := allocateComparatorPlan profile tree plan reader start states
    Invariant clock result.next result.states (comparatorBooks profile tree plan reader start states books) := by
  cases plan with
  | quiet parents =>
      exact rebase_invariant before after _ _ (allocated_preparation_invariant profile clock start [] ∅ states books inv)
  | junction certificate =>
      exact restorationBooks_invariant (Snapshot.ofTree after) tree reader _ clock 0 _ _ _
        (rebase_invariant before after _ _
          (junction_invariant _ _ _ _ _ _ _
            (allocated_preparation_invariant profile clock start _ _ states books inv)))

theorem refinementBooks_invariant {n : ℕ} (comparator tree : BST 0 n)
    (ports : List (External n)) (reader : ℕ → HeapSides n → External n → External n → Entry)
    (clock start : ℕ) (states : HeapSides n) (books : HeapBooks n) (inv : Invariant clock start states books) :
    let result := FreshRecanonicalization.allocate comparator tree ports reader start states
    Invariant clock result.next result.states (refinementBooks comparator tree ports reader start states books) := by
  apply restorationBooks_invariant
  simpa only [List.length_map, Nat.zero_add, Nat.mul_zero, Nat.add_zero] using
    detachBooks_invariant comparator clock start (ports.map Fin.val) 0 states books (by simpa using inv)

end Greedy.GrowthJournal
