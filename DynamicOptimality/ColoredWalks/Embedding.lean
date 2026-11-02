import DynamicOptimality.ColoredWalks.EmbeddingConstruction
import DynamicOptimality.ColoredWalks.EmbeddingExtrema
import DynamicOptimality.ColoredWalks.EmbeddingCursors

/-! # An actual BST for adjacent moves in colored ordered subsets

There are `k` colors. Two keys are neighbors of their color when no key
of that color lies strictly between them. The constructed tree has exactly
the supplied keys. Each such pair has distance at most
`4 * ceil(log₂(2*k+1))`, certified by literal pointer moves that keep the
whole tree fixed. The tree may depend on the colored subsets, but not on
the subsequent walk or its interleaving.
-/

namespace DynamicOptimality.ColoredWalks

open ChaCha.MTR

variable {α : Type*} [LinearOrder α]

/-- The finite color set discharges the selection hypothesis completely. -/
theorem exists_colored_embedding {k : Nat} (color : α → Fin k)
    (keys : List α) (ordered : keys.Pairwise (· < ·)) :
    ∃ tree : RawTree α, Embedding color keys (Nat.clog 2 (2*k+1)) tree := by
  apply exists_embedding_of_selection color (2*k) _ keys ordered
  intro part partOrdered nonempty
  obtain ⟨selected,included,small,present,covers⟩ :=
    exists_extreme_selection color part partOrdered
  exact ⟨selected,included,present nonempty,small,covers⟩

/-- In particular, the result is an ordered BST on precisely the original
keys, and the metric certificate acts on the supplied persistent fingers. -/
theorem exists_colored_pointer_tree {k : Nat} (color : α → Fin k)
    (keys : List α) (ordered : keys.Pairwise (· < ·)) :
    ∃ tree : RawTree α, tree.inorder = keys ∧ tree.Ordered ∧
      ∀ first last, Neighbors color keys first last →
      ∀ a b : Pointer.Cursor α, a.tree = tree → b.tree = tree →
        a.focus.rootKey = some first → b.focus.rootKey = some last →
        ∃ cost ≤ 4*Nat.clog 2 (2*k+1), Moves a b cost := by
  obtain ⟨tree,embedding⟩ := exists_colored_embedding color keys ordered
  have treeOrdered : tree.Ordered := by
    change tree.inorder.Pairwise (· < ·)
    rw [embedding.word]
    exact ordered
  refine ⟨tree,embedding.word,treeOrdered,?_⟩
  intro first last neighbors a b aTree bTree aKey bKey
  exact (embedding.neighbors first last neighbors).moves_between
    treeOrdered a b aTree bTree aKey bKey

end DynamicOptimality.ColoredWalks
