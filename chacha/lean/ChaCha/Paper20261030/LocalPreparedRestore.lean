import ChaCha.Paper20261030.LocalHeadRestore
import ChaCha.Paper20261030.SplitRejoinEquivalence
import ChaCha.Paper20261030.PreparedPrefixJoin

/-! Join-based reconstruction preserves the prescribed secondary state.
These controllers return balanced representatives of the same persistent
preferences as the manuscript's head exchange. Their balancing shapes
are allowed to change. No inverse trace or operation history is an input.
-/

namespace ChaCha.Paper20261030.SecondaryDecomposition.PreparedRestoreController

open Std Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open ColoredStorage Auxiliary Auxiliary.Metadata AuxiliaryComponent BoundaryObservations PathDecomposition SourceLocalProgram

theorem sentinel {a b : Nat} (reference : DepthTree a b) (preferences : DepthSplit → Bool)
    (d : Nat) (valid : a ≤ d ∧ d ≤ b)
    (terminal : (Secondary.decodeDepth reference preferences).terminal = d)
    (component : AuxiliaryComponent Nat Nat (Tagged Payload))
    (represented : Represents followsRight (suffixSource reference preferences d valid) component)
    (found : searchResult d component.core = true) (outside) :
    ∃ out : AuxiliaryComponent Nat Nat (Tagged Payload),
      Equivalent out component ∧ Represents followsRight (suffixSource reference preferences d valid) out ∧
      ∃ reads cost, Run (HeadRestoreController.program false) (HeadRestoreController.initial false)
        ⟨.fork (component.core.size,⟨d,(splitAt d component.core component.balanced found).value⟩)
          (terminalLeaf d) (cutRight component d found).tree,outside⟩ .done ⟨closed out,outside⟩ reads cost ∧
        cost ≤ 2100*Nat.clog 2 ((LocalReferences.depthReference reference).height+1)+310 := by
  have ordered := represented_suffix_ordered reference preferences d valid terminal component represented
  have minimum := represented_suffix_minimum reference preferences d valid terminal component represented
  have same := prepend_minimum_split_equivalent component ordered d found minimum
  rw [represented_sentinel_port reference preferences d valid terminal component represented] at same
  let out := prepend d (splitAt d component.core component.balanced found).value (terminalLeaf d) (cutRight component d found)
  have outRep : Represents followsRight (suffixSource reference preferences d valid) out := represented.equivalent same
  obtain ⟨clean,marked⟩ := represented.invariant
  have splitClean := clean_split component clean d found
  obtain ⟨reads,cost,run,bounded⟩ := HeadRestoreController.tail (cutRight component d found) splitClean.2.2
    (marked_cutRight component marked d found) d (splitAt d component.core component.balanced found).value splitClean.1
    (terminalLeaf d) rfl component.core.size outside
  refine ⟨out,same,outRep,reads,cost,run,?_⟩
  have size := (cutRight_size_le component d found).trans (represented_suffix_size reference preferences d valid component represented)
  have logarithm := Nat.clog_monotone 2 (Nat.add_le_add_right size 1)
  omega

theorem active {a b : Nat} (reference : DepthTree a b) (oldPreferences incomingPreferences : DepthSplit → Bool)
    (d : Nat) (valid : a ≤ d ∧ d ≤ b) (lower : a < d)
    (preparedOld : (Secondary.decodeDepth reference oldPreferences).terminal = d)
    (preparedIncoming : (Secondary.decodeDepth reference incomingPreferences).terminal = d)
    (old incoming : AuxiliaryComponent Nat Nat (Tagged Payload))
    (oldRep : Represents followsRight (source reference oldPreferences) old)
    (incomingRep : Represents followsRight (suffixSource reference incomingPreferences d valid) incoming)
    (lowFound : searchResult (d-1) old.core = true) (highFound : searchResult d incoming.core = true) (outside) :
    ∃ out : AuxiliaryComponent Nat Nat (Tagged Payload),
      Represents followsRight (source reference (Secondary.spliceBits d oldPreferences incomingPreferences)) out ∧
      ∃ reads cost, Run (HeadRestoreController.program true) (HeadRestoreController.initial true)
        ⟨.fork (old.core.size,⟨d-1,(splitAt (d-1) old.core old.balanced lowFound).value⟩)
          (cutLeft old (d-1) lowFound).tree
          (.fork (incoming.core.size,⟨d,(splitAt d incoming.core incoming.balanced highFound).value⟩)
            (terminalLeaf d) (cutRight incoming d highFound).tree),outside⟩ .done ⟨closed out,outside⟩ reads cost ∧
        cost ≤ 6300*Nat.clog 2 ((LocalReferences.depthReference reference).height+1)+620 := by
  have ordered := represented_suffix_ordered reference incomingPreferences d valid preparedIncoming incoming incomingRep
  have minimum := represented_suffix_minimum reference incomingPreferences d valid preparedIncoming incoming incomingRep
  have same := prepend_minimum_split_equivalent incoming ordered d highFound minimum
  rw [represented_sentinel_port reference incomingPreferences d valid preparedIncoming incoming incomingRep] at same
  let headPart := cutLeft old (d-1) lowFound
  let tail := cutRight incoming d highFound
  let lowValue := (splitAt (d-1) old.core old.balanced lowFound).value
  let highValue := (splitAt d incoming.core incoming.balanced highFound).value
  let restored := prepend d highValue (terminalLeaf d) tail
  let out := AuxiliaryComponent.join (d-1) lowValue headPart restored
  have restoredRep : Represents followsRight (suffixSource reference incomingPreferences d valid) restored := incomingRep.equivalent same
  have outRep : Represents followsRight (source reference (Secondary.spliceBits d oldPreferences incomingPreferences)) out :=
    prepared_join_represents reference oldPreferences incomingPreferences d valid preparedOld preparedIncoming lower old restored oldRep restoredRep lowFound
  obtain ⟨oldClean,oldMarked⟩ := oldRep.invariant
  obtain ⟨incomingClean,incomingMarked⟩ := incomingRep.invariant
  have lowClean := clean_split old oldClean (d-1) lowFound
  have highClean := clean_split incoming incomingClean d highFound
  obtain ⟨reads,cost,run,bounded⟩ := HeadRestoreController.active headPart tail lowClean.2.1 highClean.2.2
    (marked_cutLeft old oldMarked (d-1) lowFound) (marked_cutRight incoming incomingMarked d highFound)
    (d-1) d lowValue highValue lowClean.1 highClean.1 (terminalLeaf d) rfl old.core.size incoming.core.size outside
  refine ⟨out,outRep,reads,cost,run,?_⟩
  have oldSize := represented_size reference oldPreferences old oldRep
  have incomingSize := represented_suffix_size reference incomingPreferences d valid incoming incomingRep
  have lowSize := splitAt_size (d-1) old.core old.balanced lowFound
  have highSize := splitAt_size d incoming.core incoming.balanced highFound
  have prefixBound : headPart.core.size ≤ (LocalReferences.depthReference reference).height := by
    change (splitAt (d-1) old.core old.balanced lowFound).left.size ≤ _
    omega
  have tailBound : tail.core.size+1 ≤ (LocalReferences.depthReference reference).height := by
    change (splitAt d incoming.core incoming.balanced highFound).right.size+1 ≤ _
    omega
  have firstLog := Nat.clog_monotone 2 (show tail.core.size+1 ≤ (LocalReferences.depthReference reference).height+1 by omega)
  have prefixLog := Nat.clog_monotone 2 (Nat.add_le_add_right prefixBound 1)
  have secondLog := Nat.clog_monotone 2 (show tail.core.size+2 ≤ (LocalReferences.depthReference reference).height+1 by omega)
  omega

/-- At the minimum depth there is no old-prefix join. The same sentinel
restoration is already the full active representative of the memory splice. -/
theorem root_active {a b : Nat} (reference : DepthTree a b) (oldPreferences incomingPreferences : DepthSplit → Bool)
    (preparedOld : (Secondary.decodeDepth reference oldPreferences).terminal = a)
    (preparedIncoming : (Secondary.decodeDepth reference incomingPreferences).terminal = a)
    (incoming : AuxiliaryComponent Nat Nat (Tagged Payload))
    (incomingRep : Represents followsRight
      (suffixSource reference incomingPreferences a ⟨le_rfl,Secondary.reference_bounds reference⟩) incoming)
    (found : searchResult a incoming.core = true) (outside) :
    ∃ out : AuxiliaryComponent Nat Nat (Tagged Payload),
      Represents followsRight (source reference (Secondary.spliceBits a oldPreferences incomingPreferences)) out ∧
      ∃ reads cost, Run (HeadRestoreController.program false) (HeadRestoreController.initial false)
        ⟨.fork (incoming.core.size,⟨a,(splitAt a incoming.core incoming.balanced found).value⟩)
          (terminalLeaf a) (cutRight incoming a found).tree,outside⟩ .done ⟨closed out,outside⟩ reads cost ∧
        cost ≤ 2100*Nat.clog 2 ((LocalReferences.depthReference reference).height+1)+310 := by
  obtain ⟨out,_,outRep,reads,cost,actual,bound⟩ := sentinel reference incomingPreferences a
    ⟨le_rfl,Secondary.reference_bounds reference⟩ preparedIncoming incoming incomingRep found outside
  exact ⟨out,prepared_join_minimum_represents reference oldPreferences incomingPreferences preparedOld preparedIncoming out outRep,
    reads,cost,actual,bound⟩

end ChaCha.Paper20261030.SecondaryDecomposition.PreparedRestoreController
