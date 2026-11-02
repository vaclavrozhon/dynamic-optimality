import ChaCha.Paper20261030.SplayAuxiliaryPreparedSuffix

/-! At the minimum depth the whole root auxiliaries exchange roles.
Two actual boundary splays expose the unchanged original sentinel. -/

namespace ChaCha.Paper20261030.SplayAuxiliary

open DynamicOptimality (RawTree)
open ColoredStorage SecondaryDecomposition RawComponent Decomposition PreferredProjection
open MultiSplay.Auxiliary

 theorem prepared_minimum_splice {a b : Nat} (reference : DepthTree a b) (p q : DepthSplit → Bool)
    (preparedP : (Secondary.decodeDepth reference p).terminal = a)
    (preparedQ : (Secondary.decodeDepth reference q).terminal = a)
    (active incoming : RawComponent Nat Nat)
    (activeRep : Represents cutKey followsRight (source reference p) active)
    (incomingRep : Represents cutKey followsRight
      (suffixSource reference q a ⟨le_rfl,Secondary.reference_bounds reference⟩) incoming) :
    Represents cutKey followsRight (source reference (Secondary.spliceBits a p q)) incoming := by
  have incomingFull : Represents cutKey followsRight (source reference q) incoming := by
    simpa only [suffixSource_minimum] using incomingRep
  have index : PathDecomposition.terminalIndex followsRight (source reference p) = 0 := by
    have restricted := suffixSource_terminalIndex reference p a
      ⟨le_rfl,Secondary.reference_bounds reference⟩ preparedP
    simpa only [suffixSource_minimum] using restricted.1
  apply splice_represents_of_words reference p q a ⟨le_rfl,Secondary.reference_bounds reference⟩
    preparedP preparedQ active incoming incoming activeRep incomingRep
  · rw [represented_keys reference q incomingFull,represented_keys reference p activeRep,
      SeparatorPath.word_terminal_congr reference q p a preparedQ preparedP]
  · simp only [index,List.take_zero,List.nil_append]

 theorem prepared_minimum_exchange {a b : Nat} (reference : DepthTree a b) (p q : DepthSplit → Bool)
    (preparedP : (Secondary.decodeDepth reference p).terminal = a)
    (preparedQ : (Secondary.decodeDepth reference q).terminal = a) (upper : a < b)
    (active incoming : RawComponent Nat Nat)
    (activeRep : Represents cutKey followsRight (source reference p) active)
    (incomingRep : Represents cutKey followsRight
      (suffixSource reference q a ⟨le_rfl,Secondary.reference_bounds reference⟩) incoming) :
    ∃ oldTail newTail : RawTree Nat, ∃ oldWork incomingWork : Nat,
      Splay a active.core (.node .empty a oldTail) oldWork ∧
      Splay a incoming.core (.node .empty a newTail) incomingWork ∧
      Represents cutKey followsRight
        (suffixSource reference p a ⟨le_rfl,Secondary.reference_bounds reference⟩)
        ⟨.node .empty a oldTail,active.ports⟩ ∧
      Represents cutKey followsRight (source reference (Secondary.spliceBits a p q))
        ⟨.node .empty a newTail,incoming.ports⟩ ∧
      SourcePointer.Rearranges active.closed (.fork a (.leaf a a) (GapSource.encode oldTail active.ports 1))
        (3*oldWork+1) ∧
      SourcePointer.Rearranges incoming.closed (.fork a (.leaf a a) (GapSource.encode newTail incoming.ports 1))
        (3*incomingWork+1) ∧
      oldWork+incomingWork+2*(potential (.node .empty a newTail)+potential (.node .empty a oldTail)) ≤
        2*(potential active.core+potential incoming.core)+
          12*Nat.log 2 (LocalReferences.depthReference reference).height+2 := by
  have activeSuffix : Represents cutKey followsRight
      (suffixSource reference p a ⟨le_rfl,Secondary.reference_bounds reference⟩) active := by
    simpa only [suffixSource_minimum] using activeRep
  obtain ⟨oldTail,oldWork,oldSplay,oldRep,oldExpose,oldBound⟩ :=
    prepared_suffix_expose reference p a ⟨le_rfl,Secondary.reference_bounds reference⟩
      preparedP upper active activeSuffix
  obtain ⟨newTail,incomingWork,incomingSplay,newRep,newExpose,newBound⟩ :=
    prepared_suffix_expose reference q a ⟨le_rfl,Secondary.reference_bounds reference⟩
      preparedQ upper incoming incomingRep
  refine ⟨oldTail,newTail,oldWork,incomingWork,oldSplay,incomingSplay,oldRep,
    prepared_minimum_splice reference p q preparedP preparedQ active _ activeRep newRep,
    oldExpose,newExpose,?_⟩
  omega

end ChaCha.Paper20261030.SplayAuxiliary
