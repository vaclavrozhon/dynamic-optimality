import TangoSquared.Paper20261030.LocalNeighborLeafRead
import TangoSquared.Paper20261030.LocalClosedNeighborProgram

/-! Opening the component and querying its terminal preserves the actual
leaf-read witness. A terminal component reads the leaf immediately; every
nonempty component reaches it through the same neighbor-query subprogram. -/

namespace TangoSquared.Paper20261030.BoundaryObservations.ClosedNeighborController

open Std Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open ColoredStorage Auxiliary AuxiliaryComponent SourcePointer SourceLocalProgram SecondaryDecomposition

theorem terminal_read {a b : Nat} (reference : DepthTree a b) (preferences : DepthSplit → Bool)
    (request : Nat) (terminal : (Secondary.decodeDepth reference preferences).terminal = request)
    (component : AuxiliaryComponent Nat Nat (Tagged Payload))
    (represented : PathDecomposition.Represents followsRight (source reference preferences) component) (outside) :
    ReachesLeafRead (program request) .start ⟨closed component,outside⟩ request := by
  obtain ⟨clean,marked⟩ := represented.invariant
  by_cases empty : component.core = .leaf
  · have atLeaf : component.tree = terminalLeaf request := by
      have reached := represented_terminal_port reference preferences request terminal component represented
      simpa only [AuxiliaryComponent.tree,empty,recordTree,GapSource.encode,gapIndex] using reached
    have focus : closed component = terminalLeaf request := (closed_terminal component empty marked).trans atLeaf
    refine ⟨.start,⟨closed component,outside⟩,(0,⟨request,((⟨request,request,request⟩,false),true)⟩),[],0,
      (fun record leaf => if leaf then State.done (none,none) else .openWrite (tag false record)),.nil _ _,focus,rfl⟩
  · have physicalFork : isLeaf (closed component) = false := by
      rw [closed,isLeaf_setRoot]
      cases shape : component.core with
      | leaf => exact False.elim (empty shape)
      | inner => simp only [AuxiliaryComponent.tree,shape,recordTree,GapSource.encode,isLeaf]
    have read := initial_read request (closed component) outside
    simp only [physicalFork,Bool.false_eq_true,ite_false] at read
    have write : Step (program request) (.openWrite (tag false (closed component).rootRecord))
        ⟨closed component,outside⟩ (.querying (.search 0 (none,none))) ⟨component.tree,outside⟩ none := by
      rw [← open_root component clean empty]
      exact .write rfl
    have reached := (NeighborController.terminal_read reference preferences request terminal component represented outside).mapState
      querying (querying_code request)
    exact reached.prepend (read.prefix.append write.prefix)

end TangoSquared.Paper20261030.BoundaryObservations.ClosedNeighborController
