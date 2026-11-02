import ChaCha.Paper20261030.SplayAuxiliaryPreparedRoot
import ChaCha.Paper20261030.SplayAuxiliaryPreparedSuffix
import ChaCha.Paper20261030.SplayAuxiliaryLeaves

/-!
# The three actual splays of an interior primary exchange

Expose the old predecessor, then the old and incoming upper boundary.
The selected output shapes need no reconstruction. All attached physical
subtrees retain their literal identities, and both output root potentials
are included in the amortized bound.
-/

namespace ChaCha.Paper20261030.SplayAuxiliary

open DynamicOptimality (RawTree)
open ColoredStorage SecondaryDecomposition RawComponent Decomposition PreferredProjection
open MultiSplay.Auxiliary

 theorem prepared_interior_exchange {a b : Nat} (reference : DepthTree a b) (p q : DepthSplit → Bool)
    (d : Nat) (valid : a ≤ d ∧ d ≤ b)
    (preparedP : (Secondary.decodeDepth reference p).terminal = d)
    (preparedQ : (Secondary.decodeDepth reference q).terminal = d)
    (lower : a < d) (upper : d < b) (active incoming : RawComponent Nat Nat)
    (activeRep : Represents cutKey followsRight (source reference p) active)
    (incomingRep : Represents cutKey followsRight (suffixSource reference q d valid) incoming) :
    ∃ left suffix oldTail newTail : RawTree Nat, ∃ splitWork oldWork incomingWork : Nat,
      Splay (d-1) active.core (.node left (d-1) suffix) splitWork ∧
      Splay d suffix (.node .empty d oldTail) oldWork ∧
      Splay d incoming.core (.node .empty d newTail) incomingWork ∧
      Represents cutKey followsRight (suffixSource reference p d valid)
        ⟨.node .empty d oldTail,(RawComponent.suffix left suffix active.ports).ports⟩ ∧
      Represents cutKey followsRight (source reference (Secondary.spliceBits d p q))
        (RawComponent.join (prefixPart left active.ports) (d-1) ⟨.node .empty d newTail,incoming.ports⟩) ∧
      SourcePointer.Rearranges active.closed
        (.fork (d-1) (prefixPart left active.ports).closed
          (.fork d (.leaf d d) (GapSource.encode oldTail (RawComponent.suffix left suffix active.ports).ports 1)))
        (3*(splitWork+oldWork)+4) ∧
      SourcePointer.Rearranges incoming.closed (.fork d (.leaf d d) (GapSource.encode newTail incoming.ports 1))
        (3*incomingWork+1) ∧
      splitWork+oldWork+incomingWork+
        2*(potential (.node left (d-1) (.node .empty d newTail))+potential (.node .empty d oldTail)) ≤
        2*(potential active.core+potential incoming.core)+
          20*Nat.log 2 (source reference p).shape.height+3 := by
  obtain ⟨left,suffix,splitWork,split,suffixRep,joinedRep,exchangeBound⟩ :=
    prepared_root_exchange reference p q d valid preparedP preparedQ lower active incoming activeRep incomingRep
  obtain ⟨oldTail,oldWork,oldSplay,oldRep,oldExpose,oldBound⟩ :=
    prepared_suffix_expose reference p d valid preparedP upper
      (RawComponent.suffix left suffix active.ports) suffixRep
  obtain ⟨newTail,incomingWork,incomingSplay,newRep,incomingExpose,incomingBound⟩ :=
    prepared_suffix_expose reference q d valid preparedQ upper incoming incomingRep
  have newEquivalent : Equivalent
      (RawComponent.join (prefixPart left active.ports) (d-1) ⟨.node .empty d newTail,incoming.ports⟩)
      (RawComponent.join (prefixPart left active.ports) (d-1) incoming) := by
    refine ⟨?_,fun _ _ => rfl⟩
    simp only [join_word,← incomingSplay.inorder_eq]
  have newJoinedRep := joinedRep.equivalent newEquivalent
  have unique := (represented_core_ordered activeRep (referenceCuts_source_ordered reference p)).imp
    (fun less => Nat.ne_of_lt less)
  have incomingUnique :=
    (represented_core_ordered incomingRep (referenceCuts_suffix_ordered reference q d valid)).imp
      (fun less => Nat.ne_of_lt less)
  have splitTrace := splay_source_rearranges split unique active.ports
  change SourcePointer.Rearranges active.closed
    (RawComponent.mk (.node left (d-1) suffix) active.ports).closed (3*splitWork+1) at splitTrace
  rw [prefix_suffix_closed] at splitTrace
  have oldPhysical := splitTrace.trans
    (oldExpose.right (l := (prefixPart left active.ports).closed) (record := d-1))
  have sameHeight : (source reference q).shape.height = (source reference p).shape.height := by
    rw [source_shape,source_shape]
  have incomingFits : incoming.core.size ≤ (source reference p).shape.height := by
    have bound := incomingRep.size_height.trans (suffixSource_height reference q d valid)
    simpa only [source_shape] using bound
  have outputFits : (ChaCha.MTR.Tree.node left (d-1) (.node .empty d newTail)).size ≤
      (source reference p).shape.height := by
    have bound := newJoinedRep.size_height
    simpa only [join,prefixPart,source_shape] using bound
  refine ⟨left,suffix,oldTail,newTail,splitWork,oldWork,incomingWork,split,oldSplay,incomingSplay,
    oldRep,newJoinedRep,oldPhysical.mono (by omega),incomingExpose,?_⟩
  exact exposed_exchange_amortized split oldSplay incomingSplay unique incomingUnique
    activeRep.size_height incomingFits outputFits

end ChaCha.Paper20261030.SplayAuxiliary
