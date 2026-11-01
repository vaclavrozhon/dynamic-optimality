import TangoSquared.Paper20261030.LocalClosedPortExposure

/-! After a secondary access the root preferred path ends at the request.
Its actual closed auxiliary can expose that terminal in logarithmic cost,
leaving its root marker and all other records unchanged.
-/

namespace TangoSquared.Paper20261030.BoundaryObservations.PortExposureController

open Std Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open ColoredStorage Auxiliary Auxiliary.Metadata SourcePointer SourceLocalProgram SecondaryDecomposition

theorem expose_terminal {a b : Nat} (reference : DepthTree a b) (preferences : DepthSplit → Bool)
    (request : Nat) (terminal : (Secondary.decodeDepth reference preferences).terminal = request)
    (component : AuxiliaryComponent Nat Nat (Tagged Payload))
    (represented : PathDecomposition.Represents followsRight (source reference preferences) component)
    (outside : List (Frame Nat Cached)) :
    ∃ targetContext reads cost,
      Run (program request) (.search true) ⟨closed component,outside⟩ .done ⟨terminalLeaf request,targetContext⟩ reads cost ∧
      (Cursor.mk (terminalLeaf request) targetContext).tree = (Cursor.mk (closed component) outside).tree ∧
      cost ≤ 6*Nat.clog 2 (component.core.size+1)+1 := by
  have port := represented_terminal_port reference preferences request terminal component represented
  obtain ⟨clean,marked⟩ := represented.invariant
  cases shape : component.core with
  | leaf =>
    have physical : closed component = terminalLeaf request := by
      rw [closed_terminal component shape marked]
      simpa only [AuxiliaryComponent.tree,shape,recordTree,GapSource.encode,gapIndex] using port
    have read : Step (program request) (.search true) ⟨terminalLeaf request,outside⟩ .done ⟨terminalLeaf request,outside⟩
        (some (terminalLeaf request).rootRecord) := by
      have actual := Step.read (program := program request) (state := .search true) (next := next request true)
        (cursor := ⟨terminalLeaf request,outside⟩) rfl
      simpa only [next,if_true,terminalLeaf,isLeaf] using actual
    refine ⟨outside,[(terminalLeaf request).rootRecord],1,?_,?_,by omega⟩
    · rw [physical]
      exact read.prefix.run rfl
    · rw [physical]
  | inner size key value left right =>
    have balanced : (inner size key value left right).Balanced := shape ▸ component.balanced
    rw [shape] at clean
    have marks : ∀ i, 0 ≤ i → i ≤ 0+left.size+right.size+1 → entry (component.ports i).rootRecord = true := by
      intro i lower upper
      apply marked
      rw [shape,size_inner]
      have sizes := balanced.eq
      omega
    obtain ⟨target,reads,cost,actual,same,bounded⟩ := expose_fork request key left right balanced.left balanced.right
      clean.2.1 clean.2.2 component.ports 0 marks (tag true (size,⟨key,value⟩)) rfl outside
    have atPort : component.ports (if request ≤ key then 0+gapIndex request left else 0+left.size+1+gapIndex request right) =
        terminalLeaf request := by
      simpa only [shape,gapIndex,Nat.zero_add] using port
    have physical : closed component = .fork (tag true (size,⟨key,value⟩))
        (GapSource.encode (recordTree left) component.ports 0)
        (GapSource.encode (recordTree right) component.ports (0+left.size+1)) := by
      simp only [closed,AuxiliaryComponent.tree,shape,recordTree,GapSource.encode,Source.rootRecord,Source.setRoot,
        recordTree_size_of_balanced left balanced.left]
    rw [atPort,← physical] at actual same
    refine ⟨target,reads,cost,actual,same,?_⟩
    have heightBound := balanced_height_log component.balanced
    rw [shape] at heightBound
    simp only [height] at heightBound
    omega

end TangoSquared.Paper20261030.BoundaryObservations.PortExposureController
