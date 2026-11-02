import ChaCha.Paper20261030.SuffixDecomposition
import ChaCha.Paper20261030.ComponentPortWords

/-!
# A maintained path decomposition preserves the entire leaf word

The leaf word of a balanced component is the concatenation of its actual
port words. Equivalent cores preserve it, and the recursive maintained
representation preserves the complete ordered reference leaf word. This
identifies the whole blocks exposed by prepared boundary operations.
-/

namespace ChaCha.Paper20261030.AuxiliaryComponent

open Std Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open ColoredStorage Auxiliary Auxiliary.Metadata

variable {α κ : Type*} {β : κ → Type*}

theorem tree_leaves_portWord (c : AuxiliaryComponent α κ β) :
    c.tree.shape.leaves = c.portWord.flatMap (fun port => port.shape.leaves) := by
  simp only [tree,GapSource.encode_leaves,recordTree_size_of_balanced c.core c.balanced,
    portWord,List.flatMap_map,List.range_eq_range',Function.comp_def]

theorem Equivalent.leaves {a b : AuxiliaryComponent α κ β} (h : Equivalent a b) :
    a.tree.shape.leaves = b.tree.shape.leaves := by
  rw [tree_leaves_portWord,tree_leaves_portWord,h.portWord]

theorem append_leaves (c : AuxiliaryComponent α κ β) (key : κ) (value : β key)
    (sibling : Source α (NodeRecord κ β)) :
    (append c key value sibling).tree.shape.leaves = c.tree.shape.leaves ++ sibling.shape.leaves := by
  rw [tree_leaves_portWord,append_portWord,List.flatMap_append,← tree_leaves_portWord]
  simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil]

theorem prepend_leaves (key : κ) (value : β key) (sibling : Source α (NodeRecord κ β))
    (c : AuxiliaryComponent α κ β) :
    (prepend key value sibling c).tree.shape.leaves = sibling.shape.leaves ++ c.tree.shape.leaves := by
  rw [tree_leaves_portWord,prepend_portWord,List.flatMap_cons,← tree_leaves_portWord]

end ChaCha.Paper20261030.AuxiliaryComponent

namespace ChaCha.Paper20261030.PathDecomposition

open ColoredStorage Auxiliary Auxiliary.Metadata AuxiliaryComponent BoundaryObservations

variable {α κ : Type*} {β : κ → Type*}

theorem Represents.leaves {right : Record (β := β) → Bool}
    {reference : Source α (Record (β := β))} {c : AuxiliaryComponent α κ (Tagged β)}
    (h : Represents right reference c) : c.tree.shape.leaves = reference.shape.leaves := by
  induction h with
  | leaf marked same => exact same.leaves
  | left direction clean hl hr same ihl ihr =>
    rw [same.leaves,append_leaves]
    simpa only [closed,SourcePointer.source_setRoot_shape,Source.shape,RouterProjection.Router.leaves,ihl,ihr]
  | right direction clean hl hr same ihl ihr =>
    rw [same.leaves,prepend_leaves]
    simpa only [closed,SourcePointer.source_setRoot_shape,Source.shape,RouterProjection.Router.leaves,ihl,ihr]

end ChaCha.Paper20261030.PathDecomposition

namespace ChaCha.Paper20261030.SecondaryDecomposition

open PreferredProjection ColoredStorage Auxiliary Auxiliary.Metadata AuxiliaryComponent BoundaryObservations PathDecomposition

theorem represented_leaf_word {a b : Nat} (reference : DepthTree a b) (p : DepthSplit → Bool)
    (c : AuxiliaryComponent Nat Nat (Tagged Payload))
    (represented : Represents followsRight (source reference p) c) :
    (closed c).shape.leaves = List.range' a (b+1-a) := by
  rw [closed,SourcePointer.source_setRoot_shape,represented.leaves,source_shape,
    LocalReferences.depthReference_leaves]

theorem decodeSource_leaves (t : Source Nat Cached) : (decodeSource t).leaves = t.shape.leaves := by
  induction t <;> simp_all [decodeSource,Source.shape,PrefRouter.leaves,RouterProjection.Router.leaves]

theorem represented_suffix_leaf_word {a b : Nat} (reference : DepthTree a b) (p : DepthSplit → Bool)
    (d : Nat) (valid : a ≤ d ∧ d ≤ b)
    (c : AuxiliaryComponent Nat Nat (Tagged Payload))
    (represented : Represents followsRight (suffixSource reference p d valid) c) :
    (closed c).shape.leaves = (List.range' a (b+1-a)).filter (Secondary.suffixKeep d) := by
  have restriction := PrefRouter.prune_some_leaves (Secondary.suffixKeep d)
    (suffixSource_decode reference p d valid)
  rw [decodeSource_leaves] at restriction
  have original : (Secondary.decodeDepth reference p).leaves = List.range' a (b+1-a) := by
    rw [← decodeSource_source,decodeSource_leaves,source_shape,LocalReferences.depthReference_leaves]
  rw [original] at restriction
  rw [closed,SourcePointer.source_setRoot_shape,represented.leaves,restriction]

end ChaCha.Paper20261030.SecondaryDecomposition
