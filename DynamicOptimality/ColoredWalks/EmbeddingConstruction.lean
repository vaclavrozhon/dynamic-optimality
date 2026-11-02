import DynamicOptimality.ColoredWalks.EmbeddingAssembly
import DynamicOptimality.ColoredWalks.EmbeddingBalanced

/-! # The recursive colored-order construction

Expose a small balanced skeleton containing every color's two extremes,
recursively fill its ordered gaps, and retain the actual resulting tree.
The only abstract input in the first theorem is a finite selection lemma;
the following theorem reduces that input to at most two keys per color.
-/

namespace DynamicOptimality.ColoredWalks

open ChaCha.MTR

variable {α β : Type*} [LinearOrder α]

theorem exists_embedding_of_skeletons (color : α → β) (height : Nat)
    (expose : ∀ (keys : List α), keys.Pairwise (· < ·) → keys ≠ [] →
      ∃ skeleton : RawTree α, skeleton.Ordered ∧ skeleton ≠ .empty ∧
        (∀ key ∈ skeleton.inorder, key ∈ keys) ∧ treeHeight skeleton ≤ height ∧
        (∀ key, Extreme color keys key → key ∈ skeleton.inorder))
    (keys : List α) (ordered : keys.Pairwise (· < ·)) :
    ∃ tree : RawTree α, Embedding color keys height tree := by
  classical
  by_cases empty : keys = []
  · subst keys
    refine ⟨.empty,⟨rfl,?_,?_⟩⟩
    · intro key extreme
      have impossible := extreme.1
      simp at impossible
    · intro first last neighbors
      have impossible := neighbors.first_mem
      simp at impossible
  · obtain ⟨skeleton,skeletonOrdered,nonempty,covered,small,extremes⟩ := expose keys ordered empty
    let fill : List α → RawTree α := fun part =>
      if valid : part.length < keys.length ∧ part.Pairwise (· < ·) then
        Classical.choose (exists_embedding_of_skeletons color height expose part valid.2)
      else .empty
    have fillGood : ∀ part, part.Sublist keys → part.length < keys.length →
        Embedding color part height (fill part) := by
      intro part included shorter
      have valid : part.length < keys.length ∧ part.Pairwise (· < ·) :=
        ⟨shorter,ordered.sublist included⟩
      dsimp only [fill]
      rw [dif_pos valid]
      exact Classical.choose_spec (exists_embedding_of_skeletons color height expose part valid.2)
    have gaps : AllGaps (fun part => Embedding color part height (fill part)) skeleton keys :=
      (allGaps_shorter ordered nonempty covered).mono (fun part smaller => fillGood part smaller.1 smaller.2)
    refine ⟨assemble fill skeleton keys,⟨?_,?_,?_⟩⟩
    · exact assemble_word fill ordered skeletonOrdered covered (gaps.mono (fun _ embedding => embedding.word))
    · intro key extreme
      obtain ⟨depth,path⟩ := exists_rootPath (extremes key extreme)
      exact ⟨depth,path.assemble fill keys,path.depth_lt_height.trans_le small⟩
    · intro first last neighbors
      exact assemble_neighbors fill color height gaps small neighbors
termination_by keys.length
decreasing_by all_goals exact valid.1

/-- A finite endpoint selection is enough; all tree structure and pointer
distance guarantees are constructed by the theorem above. -/
theorem exists_embedding_of_selection (color : α → β) (capacity : Nat)
    (select : ∀ keys : List α, keys.Pairwise (· < ·) → keys ≠ [] →
      ∃ selected : List α, selected.Sublist keys ∧ selected ≠ [] ∧
        selected.length ≤ capacity ∧ (∀ key, Extreme color keys key → key ∈ selected))
    (keys : List α) (ordered : keys.Pairwise (· < ·)) :
    ∃ tree : RawTree α, Embedding color keys (Nat.clog 2 (capacity+1)) tree := by
  apply exists_embedding_of_skeletons color _ _ keys ordered
  intro part partOrdered nonempty
  obtain ⟨selected,included,selectedNonempty,short,extremes⟩ := select part partOrdered nonempty
  obtain ⟨skeleton,word,small⟩ := exists_balanced_skeleton selected
  refine ⟨skeleton,?_,?_,?_,?_,?_⟩
  · change skeleton.inorder.Pairwise (· < ·)
    rw [word]
    exact partOrdered.sublist included
  · intro empty
    have : selected = [] := word.symm.trans (congrArg Tree.inorder empty)
    exact selectedNonempty this
  · intro key member
    rw [word] at member
    exact included.subset member
  · exact small.trans (Nat.clog_mono_right 2 (by omega))
  · intro key extreme
    rw [word]
    exact extremes key extreme

end DynamicOptimality.ColoredWalks
