import TangoSquared.Paper20261030.PreparedPrefixJoin

/-!
# Concrete balanced outputs of a prepared head exchange

The new active core joins the old prefix below the sentinel to the
incoming dormant core. The old suffix becomes dormant. At sentinel zero,
the two whole components exchange roles. These definitions use the
already verified split/join outputs and preserve the exact reference
representations. Their physical exposure and reconstruction costs are
proved separately; this is not yet the assembled original-key BST trace.
-/

namespace TangoSquared.Paper20261030.SecondaryDecomposition

open Std Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open PreferredProjection ColoredStorage Auxiliary Auxiliary.Metadata AuxiliaryComponent BoundaryObservations PathDecomposition

def exchange {b : Nat} (reference : DepthTree 0 b) (p : DepthSplit → Bool)
    (d : Nat) (prepared : (Secondary.decodeDepth reference p).terminal = d)
    (active incoming : AuxiliaryComponent Nat Nat (Tagged Payload))
    (represented : Represents followsRight (source reference p) active) :
    AuxiliaryComponent Nat Nat (Tagged Payload) × AuxiliaryComponent Nat Nat (Tagged Payload) :=
  if lower : 0 < d then
    let found := prepared_lower_found reference p d prepared lower active represented
    (join (d-1) (splitAt (d-1) active.core active.balanced found).value
      (cutLeft active (d-1) found) incoming,cutRight active (d-1) found)
  else (incoming,active)

theorem exchange_represents {b : Nat} (reference : DepthTree 0 b) (p q : DepthSplit → Bool)
    (d : Nat) (valid : 0 ≤ d ∧ d ≤ b)
    (preparedP : (Secondary.decodeDepth reference p).terminal = d)
    (preparedQ : (Secondary.decodeDepth reference q).terminal = d)
    (active incoming : AuxiliaryComponent Nat Nat (Tagged Payload))
    (activeRep : Represents followsRight (source reference p) active)
    (incomingRep : Represents followsRight (suffixSource reference q d valid) incoming) :
    let out := exchange reference p d preparedP active incoming activeRep
    Represents followsRight (source reference (Secondary.spliceBits d p q)) out.1 ∧
      Represents followsRight (suffixSource reference p d valid) out.2 := by
  unfold exchange
  split
  · rename_i lower
    exact ⟨prepared_join_represents reference p q d valid preparedP preparedQ lower active incoming activeRep incomingRep _,
      prepared_cutRight_represents reference p d valid preparedP lower active activeRep _⟩
  · rename_i notLower
    have zero : d = 0 := by omega
    have pp : (Secondary.decodeDepth reference p).terminal = 0 := preparedP.trans zero
    have pq : (Secondary.decodeDepth reference q).terminal = 0 := preparedQ.trans zero
    have incomingZero : Represents followsRight
        (suffixSource reference q 0 ⟨Nat.zero_le _,Secondary.reference_bounds reference⟩) incoming := by
      simpa only [zero] using incomingRep
    constructor
    · simpa only [zero] using prepared_join_minimum_represents reference p q pp pq incoming incomingZero
    · simpa only [zero,suffixSource_minimum] using activeRep

theorem exchange_port_words {b : Nat} (reference : DepthTree 0 b) (p : DepthSplit → Bool)
    (d : Nat) (valid : 0 ≤ d ∧ d ≤ b)
    (prepared : (Secondary.decodeDepth reference p).terminal = d)
    (active incoming : AuxiliaryComponent Nat Nat (Tagged Payload))
    (represented : Represents followsRight (source reference p) active) :
    let out := exchange reference p d prepared active incoming represented
    let index := terminalIndex followsRight (source reference p)
    out.1.portWord = active.portWord.take index ++ incoming.portWord ∧
      out.2.portWord = active.portWord.drop index := by
  unfold exchange
  split
  · rename_i lower
    dsimp only
    have rank := prepared_cut_rank reference p d prepared lower active represented
      (prepared_lower_found reference p d prepared lower active represented)
    rw [rank,join_portWord,cutLeft_portWord_take,cutRight_portWord_drop]
    exact ⟨rfl,rfl⟩
  · rename_i notLower
    have zero : d = 0 := by omega
    have index : terminalIndex followsRight (source reference p) = 0 := by
      have restricted := suffixSource_terminalIndex reference p 0
        ⟨Nat.zero_le _,Secondary.reference_bounds reference⟩ (prepared.trans zero)
      simpa only [suffixSource_minimum] using restricted.1
    simp only [index,List.take_zero,List.drop_zero,List.nil_append]
    constructor <;> trivial

theorem exchange_record_words {b : Nat} (reference : DepthTree 0 b) (p q : DepthSplit → Bool)
    (d : Nat) (valid : 0 ≤ d ∧ d ≤ b)
    (preparedP : (Secondary.decodeDepth reference p).terminal = d)
    (preparedQ : (Secondary.decodeDepth reference q).terminal = d)
    (active incoming : AuxiliaryComponent Nat Nat (Tagged Payload))
    (activeRep : Represents followsRight (source reference p) active)
    (incomingRep : Represents followsRight (suffixSource reference q d valid) incoming) :
    let out := exchange reference p d preparedP active incoming activeRep
    out.1.core.toListModel = active.core.toListModel ∧
      out.2.core.toListModel = incoming.core.toListModel := by
  let out := exchange reference p d preparedP active incoming activeRep
  obtain ⟨newRep,oldRep⟩ := exchange_represents reference p q d valid preparedP preparedQ active incoming activeRep incomingRep
  constructor
  · rw [represented_word reference (Secondary.spliceBits d p q) out.1 newRep,
      represented_word reference p active activeRep]
    rw [SeparatorPath.word_terminal_congr reference (Secondary.spliceBits d p q) p d
      (splice_prepared_terminal reference p q d valid preparedP) preparedP]
  · rw [represented_suffix_word reference p d valid preparedP out.2 oldRep,
      represented_suffix_word reference q d valid preparedQ incoming incomingRep,
      SeparatorPath.word_terminal_congr reference p q d preparedP preparedQ]

end TangoSquared.Paper20261030.SecondaryDecomposition
