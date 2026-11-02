import ChaCha.Paper20261030.SplayAuxiliaryPayload
import ChaCha.Paper20261030.SplayAuxiliarySpliceWords
import ChaCha.Paper20261030.PreparedBlockIntervals

/-! Exact original depth-leaf words of arbitrary-shape splay components
and the two sides of an exposed prepared terminal. -/

namespace ChaCha.Paper20261030.SplayAuxiliary

open ColoredStorage SecondaryDecomposition RawComponent Decomposition PreferredProjection RouterProjection

variable {α ρ κ : Type*}

 theorem leafPayloads_keys (source : Source α ρ) :
    (leafPayloads source).map Prod.fst = source.shape.leaves := by
  induction source <;> simp_all [leafPayloads,Source.shape,Router.leaves]

 theorem represented_source_leaves {key : ρ → κ} {right : ρ → Bool} {reference : Source α ρ}
    {c : RawComponent α κ} (represented : Represents key right reference c) :
    c.closed.shape.leaves = reference.shape.leaves := by
  have payloads := congrArg (List.map Prod.fst) (represented_leafPayloads represented)
  simpa only [leafPayloads_keys,Source.mapRecords_shape] using payloads

 theorem represented_depth_leaves {a b : Nat} (reference : DepthTree a b) (p : DepthSplit → Bool)
    {c : RawComponent Nat Nat} (represented : Represents cutKey followsRight (source reference p) c) :
    c.closed.shape.leaves = List.range' a (b+1-a) := by
  rw [represented_source_leaves represented,source_shape,LocalReferences.depthReference_leaves]

 theorem represented_suffix_leaves {a b : Nat} (reference : DepthTree a b) (p : DepthSplit → Bool)
    (d : Nat) (valid : a ≤ d ∧ d ≤ b)
    {c : RawComponent Nat Nat} (represented : Represents cutKey followsRight (suffixSource reference p d valid) c) :
    c.closed.shape.leaves = (List.range' a (b+1-a)).filter (Secondary.suffixKeep d) := by
  have restriction := PrefRouter.prune_some_leaves (Secondary.suffixKeep d)
    (suffixSource_decode reference p d valid)
  rw [decodeSource_leaves] at restriction
  have original : (Secondary.decodeDepth reference p).leaves = List.range' a (b+1-a) := by
    rw [← decodeSource_source,decodeSource_leaves,source_shape,LocalReferences.depthReference_leaves]
  rw [original] at restriction
  rw [represented_source_leaves represented,restriction]

 theorem exposed_depth_partition {a b : Nat} (reference : DepthTree a b) (p : DepthSplit → Bool)
    (d : Nat) {c : RawComponent Nat Nat}
    (represented : Represents cutKey followsRight (source reference p) c)
    {left right : Source Nat Nat} {low high budget : Nat}
    (exposure : SourcePointer.Rearranges c.closed (.fork low left (.fork high (.leaf d d) right)) budget) :
    (∀ key ∈ left.shape.leaves, key < d) ∧ (∀ key ∈ right.shape.leaves, d < key) := by
  have leaves := exposure.leaves
  rw [represented_depth_leaves reference p represented] at leaves
  change List.range' a (b+1-a) = left.shape.leaves ++ d :: right.shape.leaves at leaves
  have ordered : (left.shape.leaves ++ d :: right.shape.leaves).Pairwise (· < ·) := by
    rw [← leaves]
    exact List.pairwise_lt_range'
  obtain ⟨leftOrder,rightOrder,cross⟩ := List.pairwise_append.mp ordered
  exact ⟨fun key member => cross key member d (by simp),(List.pairwise_cons.mp rightOrder).1⟩

 theorem exposed_suffix_partition {a b : Nat} (reference : DepthTree a b) (p : DepthSplit → Bool)
    (d : Nat) (valid : a ≤ d ∧ d ≤ b) {c : RawComponent Nat Nat}
    (represented : Represents cutKey followsRight (suffixSource reference p d valid) c)
    {right : Source Nat Nat} {high budget : Nat}
    (exposure : SourcePointer.Rearranges c.closed (.fork high (.leaf d d) right) budget) :
    ∀ key ∈ right.shape.leaves, d < key := by
  have leaves := exposure.leaves
  rw [represented_suffix_leaves reference p d valid represented] at leaves
  change (List.range' a (b+1-a)).filter (Secondary.suffixKeep d) = d :: right.shape.leaves at leaves
  have ordered : (d :: right.shape.leaves).Pairwise (· < ·) := by
    rw [← leaves]
    exact List.Pairwise.filter _ List.pairwise_lt_range'
  exact (List.pairwise_cons.mp ordered).1

end ChaCha.Paper20261030.SplayAuxiliary
