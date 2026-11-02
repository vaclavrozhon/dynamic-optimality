import ChaCha.Paper20261030.DecompositionLeaves
import ChaCha.Paper20261030.PreparedExposure

/-!
# The exposed blocks have the exact depth-side meaning

A physical boundary exposure preserves the full increasing depth-leaf
word. Consequently its left block contains exactly the leaves below the
prepared terminal, and its right block exactly those above it. Neither
statement treats an arbitrary ordered partition as an implementation.
-/

namespace ChaCha.Paper20261030.SourcePointer

open ColoredStorage

variable {α ρ : Type*}

theorem Rearranges.leaves {a b : Source α ρ} {budget : Nat} (h : Rearranges a b budget) :
    a.shape.leaves = b.shape.leaves := by
  obtain ⟨reads,cost,trace,bound⟩ := h []
  exact trace.leaves

end ChaCha.Paper20261030.SourcePointer

namespace ChaCha.Paper20261030.SecondaryDecomposition

open RouterProjection ColoredStorage Auxiliary Auxiliary.Metadata AuxiliaryComponent BoundaryObservations PathDecomposition

theorem exposed_partition {a b : Nat} (reference : DepthTree a b) (p : DepthSplit → Bool)
    (d : Nat) (c left right : AuxiliaryComponent Nat Nat (Tagged Payload))
    (represented : Represents followsRight (source reference p) c)
    (low high : Cached) (budget : Nat)
    (exposure : SourcePointer.Rearranges (closed c)
      (.fork low left.tree (.fork high (terminalLeaf d) right.tree)) budget) :
    left.tree.shape.leaves ++ d :: right.tree.shape.leaves = List.range' a (b+1-a) ∧
      (∀ key ∈ left.tree.shape.leaves, key < d) ∧
      (∀ key ∈ right.tree.shape.leaves, d < key) := by
  have leaves := exposure.leaves
  rw [represented_leaf_word reference p c represented] at leaves
  change List.range' a (b+1-a) = left.tree.shape.leaves ++ d :: right.tree.shape.leaves at leaves
  have ordered : (left.tree.shape.leaves ++ d :: right.tree.shape.leaves).Pairwise (· < ·) := by
    rw [← leaves]
    exact List.pairwise_lt_range'
  obtain ⟨leftOrder,rightOrder,cross⟩ := List.pairwise_append.mp ordered
  refine ⟨by simpa only [List.append_assoc,List.singleton_append] using leaves.symm,?_,?_⟩
  · intro key member
    exact cross key member d (by simp)
  · exact (List.pairwise_cons.mp rightOrder).1

theorem exposed_sentinel_partition {a b : Nat} (reference : DepthTree a b) (p : DepthSplit → Bool)
    (d : Nat) (valid : a ≤ d ∧ d ≤ b)
    (c right : AuxiliaryComponent Nat Nat (Tagged Payload))
    (represented : Represents followsRight (suffixSource reference p d valid) c)
    (record : Cached) (budget : Nat)
    (exposure : SourcePointer.Rearranges (closed c) (.fork record (terminalLeaf d) right.tree) budget) :
    d :: right.tree.shape.leaves = (List.range' a (b+1-a)).filter (Secondary.suffixKeep d) ∧
      ∀ key ∈ right.tree.shape.leaves, d < key := by
  have leaves := exposure.leaves
  rw [represented_suffix_leaf_word reference p d valid c represented] at leaves
  change (List.range' a (b+1-a)).filter (Secondary.suffixKeep d) = d :: right.tree.shape.leaves at leaves
  have ordered : (d :: right.tree.shape.leaves).Pairwise (· < ·) := by
    rw [← leaves]
    exact List.Pairwise.filter (Secondary.suffixKeep d) List.pairwise_lt_range'
  exact ⟨leaves.symm,(List.pairwise_cons.mp ordered).1⟩

end ChaCha.Paper20261030.SecondaryDecomposition
