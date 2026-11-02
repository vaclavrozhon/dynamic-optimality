import DynamicOptimality.ColoredWalks.EmbeddingMetric
import DynamicOptimality.PointerRelabel
import DynamicOptimality.OnlineBSTInitialization
import Splay.Accounting.OfflineNormalForm

/-! # A balanced exposed skeleton on arbitrary keys

Reuse the indexed balanced BST and relabel its ranks by the actual ordered
key list. Relabeling changes no edge or path length.
-/

namespace DynamicOptimality.ColoredWalks

open ChaCha.MTR

variable {α β : Type*}

theorem treeHeight_relabel (label : α → β) (tree : RawTree α) :
    treeHeight (Relabel.tree label tree) = treeHeight tree := by
  induction tree <;> simp [Relabel.tree,treeHeight, *]

theorem treeHeight_indexed {lower upper : Nat} (tree : BST lower upper) :
    treeHeight tree.toRaw = tree.height := by
  induction tree <;> simp [BST.toRaw,treeHeight,Splay.Tree.BST.height, *]

theorem map_range_lookup (keys : List α) (fallback : α) :
    (List.range keys.length).map (fun index => keys[index]?.getD fallback) = keys := by
  apply List.ext_getElem (by simp)
  intro index _ present
  simp [List.getElem?_eq_getElem present]

theorem exists_balanced_skeleton (keys : List α) :
    ∃ tree : RawTree α, tree.inorder = keys ∧ treeHeight tree ≤ Nat.clog 2 (keys.length+1) := by
  cases keys with
  | nil => exact ⟨.empty,rfl,by simp [treeHeight]⟩
  | cons first rest =>
    let source := Splay.Accounting.OfflineNormalForm.balancedTree (first::rest).length
    let label : Nat → α := fun index => (first::rest)[index]?.getD first
    refine ⟨Relabel.tree label (BST.toRaw source),?_,?_⟩
    · rw [Relabel.tree_word,OnlineBST.Initialization.indexed_inorder]
      exact map_range_lookup (first::rest) first
    · rw [treeHeight_relabel,treeHeight_indexed]
      exact Splay.Accounting.OfflineNormalForm.balancedTree_height_le _

end DynamicOptimality.ColoredWalks
