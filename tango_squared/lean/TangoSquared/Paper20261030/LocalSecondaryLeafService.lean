import TangoSquared.Paper20261030.LocalClosedNeighborLeafRead
import TangoSquared.Paper20261030.LocalSecondaryAccess

/-! The actual secondary loop reads its requested physical terminal.
This observation belongs to the final local departure query, so it adds no
extra search or cost. Determinism ties the witness to the completed run. -/

namespace TangoSquared.Paper20261030.SecondaryDecomposition.AccessController

open PreferredProjection ColoredStorage Auxiliary BoundaryObservations PathDecomposition SourceLocalProgram

theorem terminal_read {a b : Nat} (reference : DepthTree a b) (preferences : DepthSplit → Bool)
    (request : Nat) (terminal : (Secondary.decodeDepth reference preferences).terminal = request)
    (component : AuxiliaryComponent Nat Nat (Tagged Payload))
    (represented : Represents followsRight (source reference preferences) component) (outside) :
    ReachesLeafRead (program request) initial ⟨closed component,outside⟩ request := by
  have queried := (ClosedNeighborController.terminal_read reference preferences request terminal component represented outside).mapState
    (DepartureController.finishFirst request) (DepartureController.first_code request)
  have selected := queried.mapState RepairController.selecting (RepairController.selecting_code request)
  exact selected.mapState advance (code request)

theorem reads_request {a b : Nat} (reference : DepthTree a b) (preferences : DepthSplit → Bool)
    (request : Nat) (valid : a ≤ request ∧ request ≤ b)
    (component : AuxiliaryComponent Nat Nat (Tagged Payload))
    (represented : Represents followsRight (source reference preferences) component) (outside) :
    ReachesLeafRead (program request) initial ⟨closed component,outside⟩ request := by
  obtain ⟨last,out,decoded,outRep,reads,cost,steps,_⟩ := head_trace reference
    (PrefRouter.access_headTrace request (Secondary.decodeDepth reference preferences)) preferences rfl component represented outside
  have endpoint : (Secondary.decodeDepth reference last).terminal = request := by
    rw [decoded]
    exact PrefRouter.terminal_access _ _ ((Secondary.decodeDepth_mem reference preferences request).mpr valid)
  exact (terminal_read reference last request endpoint out outRep outside).prepend steps

theorem access_service {a b : Nat} (reference : DepthTree a b) (preferences : DepthSplit → Bool)
    (request : Nat) (valid : a ≤ request ∧ request ≤ b)
    (component : AuxiliaryComponent Nat Nat (Tagged Payload))
    (represented : Represents followsRight (source reference preferences) component) :
    ∃ out : AuxiliaryComponent Nat Nat (Tagged Payload),
      Represents followsRight (source reference (Secondary.intervalUpdate request preferences)) out ∧
      (∃ reads cost, Run (program request) initial ⟨closed component,[]⟩ (.done false)
        ⟨closed out,[]⟩ reads cost ∧
        cost ≤ ((Secondary.decodeDepth reference preferences).accessFlips request+1)*bound reference) ∧
      SourcePointer.VisitsLeaf request (closed component) (closed out)
        (((Secondary.decodeDepth reference preferences).accessFlips request+1)*bound reference) := by
  obtain ⟨out,outRep,reads,cost,run,costBound⟩ := access reference preferences request valid component represented []
  have reached := reads_request reference preferences request valid component represented []
  refine ⟨out,outRep,⟨reads,cost,run,costBound⟩,?_⟩
  intro outside
  have visit := (reached.extend outside).trace (run.extend outside)
  obtain ⟨atLeaf,record,firstReads,lastReads,firstCost,lastCost,front,focus,back,total⟩ := visit
  refine ⟨atLeaf,record,firstReads,lastReads,firstCost,lastCost,?_,focus,?_,by omega⟩
  · simpa only [SourcePointer.Cursor.extend,List.nil_append] using front
  · simpa only [SourcePointer.Cursor.extend,List.nil_append] using back

end TangoSquared.Paper20261030.SecondaryDecomposition.AccessController
