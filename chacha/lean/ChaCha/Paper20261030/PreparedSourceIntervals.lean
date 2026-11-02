import ChaCha.Paper20261030.PreparedHeadViews
import ChaCha.Paper20261030.PreparedBlockIntervals

/-! Depth inequalities for the exact closed prefix in a prepared head view. -/

namespace ChaCha.Paper20261030.SecondaryDecomposition

open RouterProjection ColoredStorage Auxiliary Auxiliary.Metadata AuxiliaryComponent BoundaryObservations PathDecomposition

theorem exposed_source_intervals {a b : Nat} (reference : DepthTree a b) (p : DepthSplit → Bool)
    (d : Nat) (component : AuxiliaryComponent Nat Nat (Tagged Payload))
    (represented : Represents followsRight (source reference p) component)
    (left right : Source Nat Cached) (low high : Cached) (budget : Nat)
    (exposure : SourcePointer.Rearranges (closed component)
      (.fork low left (.fork high (terminalLeaf d) right)) budget) :
    (∀ key ∈ left.shape.leaves, key < d) ∧ (∀ key ∈ right.shape.leaves, d < key) := by
  have leaves := exposure.leaves
  rw [represented_leaf_word reference p component represented] at leaves
  change List.range' a (b+1-a) = left.shape.leaves ++ d :: right.shape.leaves at leaves
  have ordered : (left.shape.leaves ++ d :: right.shape.leaves).Pairwise (· < ·) := by
    rw [← leaves]
    exact List.pairwise_lt_range'
  obtain ⟨_,rightOrder,cross⟩ := List.pairwise_append.mp ordered
  exact ⟨fun key member => cross key member d (by simp),(List.pairwise_cons.mp rightOrder).1⟩

end ChaCha.Paper20261030.SecondaryDecomposition
