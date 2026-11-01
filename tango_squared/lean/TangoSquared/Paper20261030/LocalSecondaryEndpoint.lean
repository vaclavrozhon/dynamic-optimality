import TangoSquared.Paper20261030.LocalTerminalExposure
import TangoSquared.Paper20261030.LocalSecondaryAccess

/-! One actual secondary program performs all repairs and then exposes
the requested endpoint. It leaves the completed component unchanged
during exposure and finishes with its cursor on the terminal depth leaf.
This is the source-level endpoint postcondition used by AccessExit.
-/

namespace TangoSquared.Paper20261030.SecondaryDecomposition.EndpointController

open PreferredProjection ColoredStorage Auxiliary BoundaryObservations PathDecomposition SourcePointer SourceLocalProgram

inductive State where
  | access (state : AccessController.State)
  | exposing (state : PortExposureController.State)

def afterAccess : AccessController.State → State
  | .done false => .exposing (.search true)
  | state => .access state

def program (request : Nat) : Program State Cached
  | .access state => (AccessController.program request state).mapState afterAccess
  | .exposing state => (PortExposureController.program request state).mapState State.exposing

def initial : State := .access AccessController.initial
def finalState : State := .exposing .done

def bound {a b : Nat} (reference : DepthTree a b) : Nat :=
  AccessController.bound reference + 6*Nat.clog 2 ((LocalReferences.depthReference reference).height+1)+1

theorem access_code (request : Nat) (state : AccessController.State) (active : AccessController.program request state ≠ .halt) :
    program request (afterAccess state) = (AccessController.program request state).mapState afterAccess := by
  cases state with
  | selecting | repairing => rfl
  | done changed => exact False.elim (active rfl)

theorem access {a b : Nat} (reference : DepthTree a b) (preferences : DepthSplit → Bool)
    (request : Nat) (valid : a ≤ request ∧ request ≤ b)
    (component : AuxiliaryComponent Nat Nat (Tagged Payload))
    (represented : Represents followsRight (source reference preferences) component) (outside : List (Frame Nat Cached)) :
    ∃ (out : AuxiliaryComponent Nat Nat (Tagged Payload)), ∃ targetContext reads cost,
      Represents followsRight (source reference (Secondary.intervalUpdate request preferences)) out ∧
      Run (program request) initial ⟨closed component,outside⟩ finalState ⟨terminalLeaf request,targetContext⟩ reads cost ∧
      (Cursor.mk (terminalLeaf request) targetContext).tree = (Cursor.mk (closed out) outside).tree ∧
      cost ≤ ((Secondary.decodeDepth reference preferences).accessFlips request+1)*bound reference := by
  obtain ⟨out,outRep,firstReads,firstCost,firstRun,firstBound⟩ :=
    AccessController.access reference preferences request valid component represented outside
  have endpoint : (Secondary.decodeDepth reference (Secondary.intervalUpdate request preferences)).terminal = request := by
    rw [Secondary.decodeDepth_access]
    exact PrefRouter.terminal_access _ _ ((Secondary.decodeDepth_mem reference preferences request).mpr valid)
  obtain ⟨targetContext,lastReads,lastCost,lastRun,same,lastBound⟩ :=
    PortExposureController.expose_terminal reference (Secondary.intervalUpdate request preferences) request endpoint out outRep outside
  have prefixSteps := firstRun.map_prefix afterAccess (access_code request)
  have exposure := lastRun.map_prefix (target := program request) State.exposing (fun _ _ => rfl)
  have full := prefixSteps.then_run (exposure.run rfl)
  refine ⟨out,targetContext,_,_,outRep,full,same,?_⟩
  have size := represented_size reference (Secondary.intervalUpdate request preferences) out outRep
  have rank := Nat.clog_monotone 2 (Nat.add_le_add_right size 1)
  have extraBound : lastCost ≤ 6*Nat.clog 2 ((LocalReferences.depthReference reference).height+1)+1 := by omega
  have paid : 6*Nat.clog 2 ((LocalReferences.depthReference reference).height+1)+1 ≤
      ((Secondary.decodeDepth reference preferences).accessFlips request+1)*
        (6*Nat.clog 2 ((LocalReferences.depthReference reference).height+1)+1) :=
    Nat.le_mul_of_pos_left _ (by omega)
  have total := Nat.add_le_add firstBound (extraBound.trans paid)
  simpa only [bound,Nat.mul_add,Nat.mul_one,Nat.add_assoc] using total

end TangoSquared.Paper20261030.SecondaryDecomposition.EndpointController
