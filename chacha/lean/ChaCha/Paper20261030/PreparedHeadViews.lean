import ChaCha.Paper20261030.PreparedHeadExchange
import ChaCha.Paper20261030.MarkedSplitExposure
import ChaCha.Paper20261030.SourceReversal

/-!
# Aligned exposed views for a prepared primary head exchange

The common prefix is the exact old lower split fragment. The two tails
are exposed independently at their common sentinel. Rebuilding the new
active view uses the inverse incoming-tail exposure followed by the
already verified join. Rebuilding the old dormant view uses the inverse
old-tail exposure. Thus the same three whole source fragments occur on
both sides of the physical exchange, with no assumed balancing-shape
equality between independent split calls.
-/

namespace ChaCha.Paper20261030.SecondaryDecomposition

open Std Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open ColoredStorage Auxiliary Auxiliary.Metadata AuxiliaryComponent BoundaryObservations PathDecomposition

theorem prepared_head_views {b : Nat} (reference : DepthTree 0 b) (p q : DepthSplit → Bool)
    (d : Nat) (lower : 0 < d) (upper : d < b)
    (preparedP : (Secondary.decodeDepth reference p).terminal = d)
    (preparedQ : (Secondary.decodeDepth reference q).terminal = d)
    (active incoming : AuxiliaryComponent Nat Nat (Tagged Payload))
    (activeRep : Represents followsRight (source reference p) active)
    (incomingRep : Represents followsRight
      (suffixSource reference q d ⟨Nat.zero_le _,Nat.le_of_lt upper⟩) incoming) :
    ∃ (headPart oldRest incomingRest : AuxiliaryComponent Nat Nat (Tagged Payload))
      (low oldHigh incomingHigh : Cached),
      let K := Nat.clog 2 ((LocalReferences.depthReference reference).height+1)
      let out := exchange reference p d preparedP active incoming activeRep
      SourcePointer.Rearranges (closed active)
        (.fork low (closed headPart) (.fork oldHigh (terminalLeaf d) oldRest.tree)) (11460*K+14) ∧
      SourcePointer.Rearranges (closed incoming)
        (.fork incomingHigh (terminalLeaf d) incomingRest.tree) (5730*K+2) ∧
      SourcePointer.Rearranges
        (.fork low (closed headPart) (.fork incomingHigh (terminalLeaf d) incomingRest.tree))
        (closed out.1) (6720*K+90) ∧
      SourcePointer.Rearranges (.fork oldHigh (terminalLeaf d) oldRest.tree) (closed out.2) (5730*K+2) ∧
      Represents followsRight (source reference (Secondary.spliceBits d p q)) out.1 ∧
      Represents followsRight (suffixSource reference p d ⟨Nat.zero_le _,Nat.le_of_lt upper⟩) out.2 := by
  let valid : 0 ≤ d ∧ d ≤ b := ⟨Nat.zero_le _,Nat.le_of_lt upper⟩
  let found := prepared_lower_found reference p d preparedP lower active activeRep
  let headPart := cutLeft active (d-1) found
  let oldTail := cutRight active (d-1) found
  let low : Cached := (active.core.size,⟨d-1,(splitAt (d-1) active.core active.balanced found).value⟩)
  have oldRep := prepared_cutRight_represents reference p d valid preparedP lower active activeRep found
  obtain ⟨oldRest,oldHigh,_,_,_,oldExposure⟩ :=
    expose_prepared_sentinel reference p d valid preparedP upper oldTail oldRep
  obtain ⟨incomingRest,incomingHigh,_,_,_,incomingExposure⟩ :=
    expose_prepared_sentinel reference q d valid preparedQ upper incoming incomingRep
  obtain ⟨clean,marked⟩ := activeRep.invariant
  have split := expose_closed_fragments active clean marked (d-1) found
  have oldInside := oldExposure.right (l := closed headPart) (record := low)
  have size := represented_size reference p active activeRep
  have logarithm := Nat.clog_monotone 2 (Nat.add_le_add_right size 1)
  have newInside := incomingExposure.symm.right (l := closed headPart) (record := low)
  have joined : SourcePointer.Rearranges (.fork low (closed headPart) (closed incoming))
      (closed (join (d-1) (splitAt (d-1) active.core active.balanced found).value headPart incoming))
      (990 * Nat.clog 2 ((LocalReferences.depthReference reference).height+1)+86) := by
    obtain ⟨cleanI,markedI⟩ := incomingRep.invariant
    apply (joinMarked_charged (d-1) _ headPart incoming (clean_split active clean (d-1) found).2.1
      cleanI (marked_cutLeft active marked (d-1) found) markedI active.core.size).mono
    have splitSize := splitAt_size (d-1) active.core active.balanced found
    have incomingSize := represented_suffix_size reference q d valid incoming incomingRep
    have leftSize : headPart.core.size ≤ (LocalReferences.depthReference reference).height := by
      change (splitAt (d-1) active.core active.balanced found).left.size ≤ _
      omega
    have logLeft := Nat.clog_monotone 2 (Nat.add_le_add_right leftSize 1)
    have logIncoming := Nat.clog_monotone 2 (Nat.add_le_add_right incomingSize 1)
    omega
  have represented := exchange_represents reference p q d valid preparedP preparedQ active incoming activeRep incomingRep
  refine ⟨headPart,oldRest,incomingRest,low,oldHigh,incomingHigh,?_,incomingExposure,?_,?_,represented⟩
  · exact (split.trans oldInside).mono (by omega)
  · have finish := newInside.trans joined
    simpa only [exchange,dif_pos lower] using finish.mono (show
      (5730 * Nat.clog 2 ((LocalReferences.depthReference reference).height+1)+2+2) +
        (990 * Nat.clog 2 ((LocalReferences.depthReference reference).height+1)+86) ≤
          6720 * Nat.clog 2 ((LocalReferences.depthReference reference).height+1)+90 by omega)
  · simpa only [exchange,dif_pos lower] using oldExposure.symm

theorem prepared_head_views_zero {b : Nat} (reference : DepthTree 0 b) (p q : DepthSplit → Bool)
    (upper : 0 < b)
    (preparedP : (Secondary.decodeDepth reference p).terminal = 0)
    (preparedQ : (Secondary.decodeDepth reference q).terminal = 0)
    (active incoming : AuxiliaryComponent Nat Nat (Tagged Payload))
    (activeRep : Represents followsRight (source reference p) active)
    (incomingRep : Represents followsRight
      (suffixSource reference q 0 ⟨Nat.zero_le _,Nat.le_of_lt upper⟩) incoming) :
    ∃ (oldRest incomingRest : AuxiliaryComponent Nat Nat (Tagged Payload)) (oldHigh incomingHigh : Cached),
      let K := Nat.clog 2 ((LocalReferences.depthReference reference).height+1)
      let out := exchange reference p 0 preparedP active incoming activeRep
      SourcePointer.Rearranges (closed active) (.fork oldHigh (terminalLeaf 0) oldRest.tree) (5730*K+2) ∧
      SourcePointer.Rearranges (closed incoming) (.fork incomingHigh (terminalLeaf 0) incomingRest.tree) (5730*K+2) ∧
      SourcePointer.Rearranges (.fork incomingHigh (terminalLeaf 0) incomingRest.tree) (closed out.1) (5730*K+2) ∧
      SourcePointer.Rearranges (.fork oldHigh (terminalLeaf 0) oldRest.tree) (closed out.2) (5730*K+2) ∧
      Represents followsRight (source reference (Secondary.spliceBits 0 p q)) out.1 ∧
      Represents followsRight (suffixSource reference p 0 ⟨Nat.zero_le _,Nat.le_of_lt upper⟩) out.2 := by
  let valid : 0 ≤ 0 ∧ 0 ≤ b := ⟨le_rfl,Nat.le_of_lt upper⟩
  have oldRep : Represents followsRight (suffixSource reference p 0 valid) active := by
    simpa only [suffixSource_minimum] using activeRep
  obtain ⟨oldRest,oldHigh,_,_,_,oldExposure⟩ :=
    expose_prepared_sentinel reference p 0 valid preparedP upper active oldRep
  obtain ⟨incomingRest,incomingHigh,_,_,_,incomingExposure⟩ :=
    expose_prepared_sentinel reference q 0 valid preparedQ upper incoming incomingRep
  have represented := exchange_represents reference p q 0 valid preparedP preparedQ active incoming activeRep incomingRep
  refine ⟨oldRest,incomingRest,oldHigh,incomingHigh,oldExposure,incomingExposure,?_,?_,represented⟩
  · simpa only [exchange,Nat.lt_irrefl,not_false_eq_true,dif_neg] using incomingExposure.symm
  · simpa only [exchange,Nat.lt_irrefl,not_false_eq_true,dif_neg] using oldExposure.symm

end ChaCha.Paper20261030.SecondaryDecomposition
