import TangoSquared.Paper20261030.PreparedSuffixCut
import TangoSquared.Paper20261030.SplicedDecomposition
import TangoSquared.Paper20261030.MarkedJoin

/-!
# Joining the old prefix to the incoming dormant component

The join uses the existing separator immediately below the prepared
terminal. Its word is the original full prepared path, and its port word
is exactly the semantic prefix/suffix exchange. Consequently the actual
balanced output represents the persistent-memory splice. This supplies
the depth-source reconstruction; exposing/reassembling its colored
original-key projections is a separate operation.
-/

namespace TangoSquared.Paper20261030.SecondaryDecomposition

open Std Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open PreferredProjection ColoredStorage Auxiliary Auxiliary.Metadata AuxiliaryComponent BoundaryObservations PathDecomposition

theorem splice_prepared_terminal {a b : Nat} (reference : DepthTree a b)
    (p q : DepthSplit → Bool) (d : Nat) (valid : a ≤ d ∧ d ≤ b)
    (prepared : (Secondary.decodeDepth reference p).terminal = d) :
    (Secondary.decodeDepth reference (Secondary.spliceBits d p q)).terminal = d := by
  have terminal := spliced_terminal reference p q d valid prepared
  rw [← source_splice,terminalSource_eq] at terminal
  exact (Source.leaf.inj terminal).1

theorem prepared_join_represents {a b : Nat} (reference : DepthTree a b)
    (p q : DepthSplit → Bool) (d : Nat) (valid : a ≤ d ∧ d ≤ b)
    (preparedP : (Secondary.decodeDepth reference p).terminal = d)
    (preparedQ : (Secondary.decodeDepth reference q).terminal = d) (lower : a < d)
    (active incoming : AuxiliaryComponent Nat Nat (Tagged Payload))
    (activeRep : Represents followsRight (source reference p) active)
    (incomingRep : Represents followsRight (suffixSource reference q d valid) incoming)
    (found : searchResult (d-1) active.core = true) :
    Represents followsRight (source reference (Secondary.spliceBits d p q))
      (join (d-1) (splitAt (d-1) active.core active.balanced found).value
        (cutLeft active (d-1) found) incoming) := by
  obtain ⟨semantic,semanticRep,ports⟩ := splicedRepresentative_exists reference p q d valid
    preparedP preparedQ active incoming activeRep incomingRep
  rw [← source_splice] at semanticRep
  apply semanticRep.equivalent
  apply equivalent_of_words
  · have suffixRep := prepared_cutRight_represents reference p d valid preparedP lower active activeRep found
    have rightWord : (cutRight active (d-1) found).core.toListModel = incoming.core.toListModel := by
      rw [represented_suffix_word reference p d valid preparedP _ suffixRep,
        represented_suffix_word reference q d valid preparedQ _ incomingRep,
        SeparatorPath.word_terminal_congr reference p q d preparedP preparedQ]
    rw [join_word,← rightWord]
    have whole := splitAt_toList (d-1) active.core active.balanced found
    change (cutLeft active (d-1) found).core.toListModel ++
      ⟨d-1,(splitAt (d-1) active.core active.balanced found).value⟩ ::
        (cutRight active (d-1) found).core.toListModel = active.core.toListModel at whole
    rw [whole,represented_word reference p active activeRep,
      represented_word reference (Secondary.spliceBits d p q) semantic semanticRep]
    rw [SeparatorPath.word_terminal_congr reference p (Secondary.spliceBits d p q) d preparedP
      (splice_prepared_terminal reference p q d valid preparedP)]
  · rw [join_portWord,ports,prepared_cut_rank reference p d preparedP lower active activeRep found,
      cutLeft_portWord_take]

theorem prepared_join_minimum_represents {a b : Nat} (reference : DepthTree a b)
    (p q : DepthSplit → Bool) (preparedP : (Secondary.decodeDepth reference p).terminal = a)
    (preparedQ : (Secondary.decodeDepth reference q).terminal = a)
    (incoming : AuxiliaryComponent Nat Nat (Tagged Payload))
    (incomingRep : Represents followsRight
      (suffixSource reference q a ⟨le_rfl,Secondary.reference_bounds reference⟩) incoming) :
    Represents followsRight (source reference (Secondary.spliceBits a p q)) incoming := by
  let valid : a ≤ a ∧ a ≤ b := ⟨le_rfl,Secondary.reference_bounds reference⟩
  let active := initializeMarked followsRight (source reference p)
  have activeRep := initialize_representation reference p
  have incomingFull : Represents followsRight (source reference q) incoming := by
    simpa only [suffixSource_minimum] using incomingRep
  obtain ⟨semantic,semanticRep,ports⟩ := splicedRepresentative_exists reference p q a valid
    preparedP preparedQ active incoming activeRep incomingRep
  rw [← source_splice] at semanticRep
  have index : terminalIndex followsRight (source reference p) = 0 := by
    have restricted := suffixSource_terminalIndex reference p a valid preparedP
    simpa only [suffixSource_minimum] using restricted.1
  rw [index,List.take_zero,List.nil_append] at ports
  apply semanticRep.equivalent
  apply equivalent_of_words
  · rw [represented_word reference q incoming incomingFull,
      represented_word reference (Secondary.spliceBits a p q) semantic semanticRep]
    rw [SeparatorPath.word_terminal_congr reference q (Secondary.spliceBits a p q) a preparedQ
      (splice_prepared_terminal reference p q a valid preparedP)]
  · exact ports.symm

theorem prepared_join_charged {a b : Nat} (reference : DepthTree a b)
    (p q : DepthSplit → Bool) (d : Nat) (valid : a ≤ d ∧ d ≤ b)
    (preparedP : (Secondary.decodeDepth reference p).terminal = d)
    (preparedQ : (Secondary.decodeDepth reference q).terminal = d) (lower : a < d)
    (active incoming : AuxiliaryComponent Nat Nat (Tagged Payload))
    (activeRep : Represents followsRight (source reference p) active)
    (incomingRep : Represents followsRight (suffixSource reference q d valid) incoming)
    (found : searchResult (d-1) active.core = true) (old : Nat) :
    let value := (splitAt (d-1) active.core active.balanced found).value
    let left := cutLeft active (d-1) found
    ∃ out : AuxiliaryComponent Nat Nat (Tagged Payload),
      Represents followsRight (source reference (Secondary.spliceBits d p q)) out ∧
      SourcePointer.Rearranges (.fork (old,⟨d-1,value⟩) (closed left) (closed incoming)) (closed out)
        (990 * Nat.clog 2 ((LocalReferences.depthReference reference).height + 1) + 86) := by
  dsimp only
  let left := cutLeft active (d-1) found
  let value := (splitAt (d-1) active.core active.balanced found).value
  refine ⟨join (d-1) value left incoming,
    prepared_join_represents reference p q d valid preparedP preparedQ lower active incoming activeRep incomingRep found,?_⟩
  obtain ⟨cleanA,markedA⟩ := activeRep.invariant
  obtain ⟨cleanI,markedI⟩ := incomingRep.invariant
  apply (joinMarked_charged (d-1) value left incoming (clean_split active cleanA (d-1) found).2.1
    cleanI (marked_cutLeft active markedA (d-1) found) markedI old).mono
  have splitSize := splitAt_size (d-1) active.core active.balanced found
  have activeSize := represented_size reference p active activeRep
  have incomingSize := represented_suffix_size reference q d valid incoming incomingRep
  have leftSize : left.core.size ≤ (LocalReferences.depthReference reference).height := by
    change (splitAt (d-1) active.core active.balanced found).left.size ≤ _
    omega
  have logLeft := Nat.clog_monotone 2 (Nat.add_le_add_right leftSize 1)
  have logIncoming := Nat.clog_monotone 2 (Nat.add_le_add_right incomingSize 1)
  omega

end TangoSquared.Paper20261030.SecondaryDecomposition
