import Splay.Accounting.RibStackFoldedShape
import Splay.Accounting.RibStackInitialization

namespace Splay.Accounting.OfflineNormalForm.RibStack

open Splay.Tree Digits

theorem exists_initialized_foldedShape (count capacity : ℕ) (fits : count ≤ capacity) :
    ∃ (digits : List Digit) (tree : BST (capacity - count) capacity),
      FoldedStackShape 0 digits tree ∧ value digits = count := by
  obtain ⟨digits, tree, _, _, shaped, valueEq, _, _, _⟩ :=
    exists_initialized_stack_with_capacity count capacity fits
  obtain ⟨after, folded⟩ := shaped.exists_foldedShape
  exact ⟨digits, after, folded, valueEq⟩

end Splay.Accounting.OfflineNormalForm.RibStack
