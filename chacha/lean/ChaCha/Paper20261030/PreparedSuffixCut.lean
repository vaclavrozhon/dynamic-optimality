import ChaCha.Paper20261030.SuffixPortTransfer
import ChaCha.Paper20261030.CutSuffixWords

/-!
# The actual balanced cut is the dormant secondary decomposition

Cutting a prepared active root core just below its terminal produces an
actual suffix component representing the restricted old reference. Its
word and all its ports agree with the semantic restriction. The marked
cut physically installs that component as the prefix's last port.
-/

namespace ChaCha.Paper20261030.SecondaryDecomposition

open Std Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open PreferredProjection ColoredStorage Auxiliary Auxiliary.Metadata AuxiliaryComponent BoundaryObservations PathDecomposition

theorem represented_terminal_rank {a b : Nat} (reference : DepthTree a b) (p : DepthSplit → Bool)
    (d : Nat) (prepared : (Secondary.decodeDepth reference p).terminal = d)
    (c : AuxiliaryComponent Nat Nat (Tagged Payload))
    (represented : Represents followsRight (source reference p) c) :
    terminalIndex followsRight (source reference p) = gapIndex d c.core := by
  rw [gapIndex_count d c.core c.balanced (represented_ordered reference p c represented),
    represented_word reference p c represented,List.filter_map,List.length_map]
  exact terminalIndex_rank reference p d prepared

theorem prepared_cut_rank {a b : Nat} (reference : DepthTree a b) (p : DepthSplit → Bool)
    (d : Nat) (prepared : (Secondary.decodeDepth reference p).terminal = d) (lower : a < d)
    (c : AuxiliaryComponent Nat Nat (Tagged Payload))
    (represented : Represents followsRight (source reference p) c)
    (found : searchResult (d-1) c.core = true) :
    terminalIndex followsRight (source reference p) = (cutLeft c (d-1) found).core.size + 1 := by
  rw [represented_terminal_rank reference p d prepared c represented]
  have next : d-1+1 = d := by omega
  simpa only [next] using gapIndex_successor_split c (represented_ordered reference p c represented) (d-1) found

theorem prepared_cutRight_represents {a b : Nat} (reference : DepthTree a b) (p : DepthSplit → Bool)
    (d : Nat) (valid : a ≤ d ∧ d ≤ b)
    (prepared : (Secondary.decodeDepth reference p).terminal = d) (lower : a < d)
    (c : AuxiliaryComponent Nat Nat (Tagged Payload))
    (represented : Represents followsRight (source reference p) c)
    (found : searchResult (d-1) c.core = true) :
    Represents followsRight (suffixSource reference p d valid) (cutRight c (d-1) found) := by
  obtain ⟨suffix,suffixRep,ports⟩ := suffixRepresentative_exists reference p d valid prepared c represented
  apply suffixRep.equivalent
  apply equivalent_of_words
  · rw [cutRight_word_filter c (represented_ordered reference p c represented),
      represented_suffix_word reference p d valid prepared suffix suffixRep,
      represented_word reference p c represented,List.filter_map]
    congr 1
    apply List.filter_congr
    intro e he
    change decide (d-1 < e.1) = decide (d ≤ e.1)
    simp only [show d-1 < e.1 ↔ d ≤ e.1 by omega]
  · rw [cutRight_portWord_drop,ports,prepared_cut_rank reference p d prepared lower c represented found]

theorem prepared_cutMarked_charged {a b : Nat} (reference : DepthTree a b) (p : DepthSplit → Bool)
    (d : Nat) (valid : a ≤ d ∧ d ≤ b)
    (prepared : (Secondary.decodeDepth reference p).terminal = d) (lower : a < d)
    (c : AuxiliaryComponent Nat Nat (Tagged Payload))
    (represented : Represents followsRight (source reference p) c) :
    ∃ (prefixPart suffixPart : AuxiliaryComponent Nat Nat (Tagged Payload)),
      Represents followsRight (suffixSource reference p d valid) suffixPart ∧
      prefixPart.ports prefixPart.core.size = closed suffixPart ∧
      SourcePointer.Rearranges (closed c) (closed prefixPart)
        (6225 * Nat.clog 2 ((LocalReferences.depthReference reference).height + 1) + 84) := by
  have found := prepared_lower_found reference p d prepared lower c represented
  obtain ⟨clean,marked⟩ := represented.invariant
  refine ⟨cutMarked c (d-1) found,cutRight c (d-1) found,
    prepared_cutRight_represents reference p d valid prepared lower c represented found,?_,?_⟩
  · unfold cutMarked
    rw [append_size]
    simp only [append,
      show ¬ (cutLeft c (d-1) found).core.size + 1 ≤ (cutLeft c (d-1) found).core.size by omega,if_false]
  · apply (cutMarked_charged c clean marked (d-1) found).mono
    have size := represented_size reference p c represented
    have logarithm := Nat.clog_monotone 2 (Nat.add_le_add_right size 1)
    omega

end ChaCha.Paper20261030.SecondaryDecomposition
