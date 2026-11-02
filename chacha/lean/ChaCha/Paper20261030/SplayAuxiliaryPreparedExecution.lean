import ChaCha.Paper20261030.SplayAuxiliaryPreparedExchange
import ChaCha.Paper20261030.SplayAuxiliaryPreparedMinimum

/-!
# Ordinary-splay provenance of a prepared primary exchange

The constructors retain every bottom-up splay and the exact unchanged
port tables. Splitting the port word is therefore independent of the
resulting root shapes; it supplies the persistent global inventory proof.
-/

namespace ChaCha.Paper20261030.SplayAuxiliary

open DynamicOptimality (RawTree)
open ColoredStorage SecondaryDecomposition RawComponent Decomposition PreferredProjection
open MultiSplay.Auxiliary

inductive PreparedExecution (active incoming : RawComponent Nat Nat) :
    Nat → RawComponent Nat Nat → RawComponent Nat Nat → Nat → Prop
  | interior {d : Nat} {left suffix oldTail newTail : RawTree Nat} {splitWork oldWork incomingWork : Nat}
      (positive : 0 < d)
      (split : Splay (d-1) active.core (.node left (d-1) suffix) splitWork)
      (oldSplay : Splay d suffix (.node .empty d oldTail) oldWork)
      (incomingSplay : Splay d incoming.core (.node .empty d newTail) incomingWork)
      (oldExpose : SourcePointer.Rearranges active.closed
        (.fork (d-1) (prefixPart left active.ports).closed
          (.fork d (.leaf d d) (GapSource.encode oldTail (RawComponent.suffix left suffix active.ports).ports 1)))
        (3*(splitWork+oldWork)+4))
      (incomingExpose : SourcePointer.Rearranges incoming.closed
        (.fork d (.leaf d d) (GapSource.encode newTail incoming.ports 1)) (3*incomingWork+1))
      (incomingPort : incoming.ports 0 = .leaf d d)
      (oldPort : (RawComponent.suffix left suffix active.ports).ports 0 = .leaf d d) :
      PreparedExecution active incoming d
        (RawComponent.join (prefixPart left active.ports) (d-1) ⟨.node .empty d newTail,incoming.ports⟩)
        ⟨.node .empty d oldTail,(RawComponent.suffix left suffix active.ports).ports⟩
        (splitWork+oldWork+incomingWork)
  | minimum {oldTail newTail : RawTree Nat} {oldWork incomingWork : Nat}
      (oldSplay : Splay 0 active.core (.node .empty 0 oldTail) oldWork)
      (incomingSplay : Splay 0 incoming.core (.node .empty 0 newTail) incomingWork)
      (oldExpose : SourcePointer.Rearranges active.closed
        (.fork 0 (.leaf 0 0) (GapSource.encode oldTail active.ports 1)) (3*oldWork+1))
      (incomingExpose : SourcePointer.Rearranges incoming.closed
        (.fork 0 (.leaf 0 0) (GapSource.encode newTail incoming.ports 1)) (3*incomingWork+1))
      (incomingPort : incoming.ports 0 = .leaf 0 0)
      (oldPort : active.ports 0 = .leaf 0 0) :
      PreparedExecution active incoming 0 ⟨.node .empty 0 newTail,incoming.ports⟩
        ⟨.node .empty 0 oldTail,active.ports⟩ (oldWork+incomingWork)

 theorem PreparedExecution.port_words {b d : Nat} (reference : DepthTree 0 b) (p : DepthSplit → Bool)
    (prepared : (Secondary.decodeDepth reference p).terminal = d)
    {active incoming out parked : RawComponent Nat Nat} {work : Nat}
    (represented : Represents cutKey followsRight (source reference p) active)
    (execution : PreparedExecution active incoming d out parked work) :
    out.portWord = active.portWord.take (PathDecomposition.terminalIndex followsRight (source reference p)) ++
      incoming.portWord ∧
    parked.portWord = active.portWord.drop (PathDecomposition.terminalIndex followsRight (source reference p)) := by
  cases execution with
  | @interior d left suffix oldTail newTail splitWork oldWork incomingWork positive split oldSplay incomingSplay oldExpose incomingExpose incomingPort oldPort =>
      have index := prepared_splay_rank reference p d prepared positive represented split
      have splitSame : Equivalent ⟨.node left (d-1) suffix,active.ports⟩ active :=
        ⟨split.inorder_eq.symm,fun _ _ => rfl⟩
      have incomingSame : Equivalent ⟨.node .empty d newTail,incoming.ports⟩ incoming :=
        ⟨incomingSplay.inorder_eq.symm,fun _ _ => rfl⟩
      have oldSame : Equivalent ⟨.node .empty d oldTail,(RawComponent.suffix left suffix active.ports).ports⟩
          (RawComponent.suffix left suffix active.ports) := ⟨oldSplay.inorder_eq.symm,fun _ _ => rfl⟩
      constructor
      · rw [join_portWord,incomingSame.portWord,index,prefix_portWord left suffix (d-1),splitSame.portWord]
      · rw [oldSame.portWord,index,suffix_portWord left suffix (d-1),splitSame.portWord]
  | minimum oldSplay incomingSplay oldExpose incomingExpose incomingPort oldPort =>
      have index : PathDecomposition.terminalIndex followsRight (source reference p) = 0 := by
        have restricted := suffixSource_terminalIndex reference p 0
          ⟨Nat.zero_le _,Secondary.reference_bounds reference⟩ prepared
        simpa only [suffixSource_minimum] using restricted.1
      have incomingSame : Equivalent ⟨_,incoming.ports⟩ incoming :=
        ⟨incomingSplay.inorder_eq.symm,fun _ _ => rfl⟩
      have oldSame : Equivalent ⟨_,active.ports⟩ active := ⟨oldSplay.inorder_eq.symm,fun _ _ => rfl⟩
      simpa only [index,List.take_zero,List.nil_append,List.drop_zero] using
        And.intro incomingSame.portWord oldSame.portWord

 theorem prepared_execution_exists {b : Nat} (reference : DepthTree 0 b) (p q : DepthSplit → Bool)
    (d : Nat) (upper : d < b)
    (preparedP : (Secondary.decodeDepth reference p).terminal = d)
    (preparedQ : (Secondary.decodeDepth reference q).terminal = d)
    (active incoming : RawComponent Nat Nat)
    (activeRep : Represents cutKey followsRight (source reference p) active)
    (incomingRep : Represents cutKey followsRight
      (suffixSource reference q d ⟨Nat.zero_le _,Nat.le_of_lt upper⟩) incoming) :
    ∃ out parked work, PreparedExecution active incoming d out parked work ∧
      Represents cutKey followsRight (source reference (Secondary.spliceBits d p q)) out ∧
      Represents cutKey followsRight (suffixSource reference p d ⟨Nat.zero_le _,Nat.le_of_lt upper⟩) parked ∧
      work+2*(potential out.core+potential parked.core) ≤
        2*(potential active.core+potential incoming.core)+
          20*Nat.log 2 (LocalReferences.depthReference reference).height+3 := by
  cases d with
  | zero =>
      have incomingPort := prepared_suffix_port reference q 0 ⟨Nat.zero_le _,Nat.le_of_lt upper⟩ preparedQ incomingRep
      have activeSuffix : Represents cutKey followsRight
          (suffixSource reference p 0 ⟨Nat.zero_le _,Nat.le_of_lt upper⟩) active := by
        simpa only [suffixSource_minimum] using activeRep
      have oldPort := prepared_suffix_port reference p 0 ⟨Nat.zero_le _,Nat.le_of_lt upper⟩ preparedP activeSuffix
      obtain ⟨oldTail,newTail,oldWork,incomingWork,oldSplay,incomingSplay,oldRep,newRep,oldExpose,incomingExpose,bound⟩ :=
        prepared_minimum_exchange reference p q preparedP preparedQ upper active incoming activeRep incomingRep
      refine ⟨_,_,_,.minimum oldSplay incomingSplay oldExpose incomingExpose incomingPort oldPort,newRep,oldRep,?_⟩
      dsimp only
      omega
  | succ depth =>
      obtain ⟨left,suffix,oldTail,newTail,splitWork,oldWork,incomingWork,split,oldSplay,incomingSplay,
        oldRep,newRep,oldExpose,incomingExpose,bound⟩ :=
        prepared_interior_exchange reference p q (depth+1) ⟨Nat.zero_le _,Nat.le_of_lt upper⟩
          preparedP preparedQ (Nat.zero_lt_succ _) upper active incoming activeRep incomingRep
      have incomingPort := prepared_suffix_port reference q (depth+1) ⟨Nat.zero_le _,Nat.le_of_lt upper⟩ preparedQ incomingRep
      have oldPort := prepared_suffix_port reference p (depth+1) ⟨Nat.zero_le _,Nat.le_of_lt upper⟩ preparedP oldRep
      refine ⟨_,_,_,.interior (Nat.zero_lt_succ _) split oldSplay incomingSplay oldExpose incomingExpose
        incomingPort oldPort,newRep,oldRep,?_⟩
      simpa only [join,prefixPart,source_shape] using bound

end ChaCha.Paper20261030.SplayAuxiliary
