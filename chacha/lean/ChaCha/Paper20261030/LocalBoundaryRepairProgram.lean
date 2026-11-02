import ChaCha.Paper20261030.LocalPreferenceFlipProgram
import ChaCha.Paper20261030.LocalComponentJoin

/-! A local wrapper for repairing one side of an existing separator.
It exposes the boundary, closes the selected fragment, executes the
supplied local subprogram there, opens its result, and rejoins the two
fragments. Two nested wrappers handle an interior interval. The wrapper
stores the subprogram's scalar state, never a component or subtree. -/

namespace ChaCha.Paper20261030.BoundaryObservations.BoundaryRepairController

open Std Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open ColoredStorage Auxiliary AuxiliaryComponent SourceLocalProgram GapSource.Controller

variable {α κ ρ σ : Type*} [Ord κ]

inductive Phase where
  | openOuter | closeChild | openChild | closeOuter

def Phase.close : Phase → Bool
  | .closeChild | .closeOuter => true
  | _ => false

inductive State (σ κ ρ : Type*) where
  | marker (phase : Phase) (state : RootMarkerController.State κ ρ)
  | splitting (state : MarkedCutController.SplitState κ ρ)
  | down
  | repairing (state : σ)
  | up
  | joining (state : MarkedCutController.JoinState κ ρ)
  | done

def halted (instruction : Instruction σ (MarkedRecord κ ρ)) : Bool :=
  match instruction with | .halt => true | _ => false

def repairing (repair : Program σ (MarkedRecord κ ρ)) (state : σ) : State σ κ ρ :=
  if halted (repair state) then .marker .openChild .start else .repairing state

def after (repair : Program σ (MarkedRecord κ ρ)) (initial : σ) : Phase → State σ κ ρ
  | .openOuter => .splitting (.ready (.search 0))
  | .closeChild => repairing repair initial
  | .openChild => .up
  | .closeOuter => .done

def marking (repair : Program σ (MarkedRecord κ ρ)) (initial : σ) (phase : Phase) :
    RootMarkerController.State κ ρ → State σ κ ρ
  | .done => after repair initial phase
  | state => .marker phase state

def splitting : MarkedCutController.SplitState κ ρ → State σ κ ρ
  | .ready (.returning 0) => .down
  | state => .splitting state

def joining : MarkedCutController.JoinState κ ρ → State σ κ ρ
  | .ready (.returning 0) => .marker .closeOuter .start
  | state => .joining state

def program (key : κ) (right : Bool) (repair : Program σ (MarkedRecord κ ρ)) (initial : σ) :
    Program (State σ κ ρ) (MarkedRecord κ ρ)
  | .marker phase state => (RootMarkerController.program phase.close (!phase.close) state).mapState (marking repair initial phase)
  | .splitting state => (code (SplitController.program key) state).mapState splitting
  | .down => .nav (if right then .right else .left) (.marker .closeChild .start)
  | .repairing state => (repair state).mapState (repairing repair)
  | .up => .nav .up (.joining (.ready (.observing 0 (.read 3 []))))
  | .joining state => (code JoinController.program state).mapState joining
  | .done => .halt

theorem marking_code (key : κ) (right : Bool) (repair : Program σ (MarkedRecord κ ρ)) (initial : σ)
    (phase : Phase) (state : RootMarkerController.State κ ρ)
    (active : RootMarkerController.program phase.close (!phase.close) state ≠ .halt) :
    program key right repair initial (marking repair initial phase state) =
      (RootMarkerController.program phase.close (!phase.close) state).mapState (marking repair initial phase) := by
  cases state with
  | start | write => rfl
  | done => exact False.elim (active rfl)

theorem repairing_code (key : κ) (right : Bool) (repair : Program σ (MarkedRecord κ ρ)) (initial state : σ)
    (active : repair state ≠ .halt) :
    program key right repair initial (repairing repair state) = (repair state).mapState (repairing repair) := by
  unfold repairing
  cases equation : repair state with
  | halt => exact False.elim (active equation)
  | read | nav | write => simp only [halted,Bool.false_eq_true,ite_false,program,equation]; rfl

theorem run_halted {repair : Program σ (MarkedRecord κ ρ)} {state last : σ} {before after : SourcePointer.Cursor α (MarkedRecord κ ρ)}
    {reads cost} (run : Run repair state before last after reads cost) : repair last = .halt := by
  induction run with
  | halt instruction => exact instruction
  | next _ _ ih => exact ih

theorem splitting_code (key : κ) (right : Bool) (repair : Program σ (MarkedRecord κ ρ)) (initial : σ)
    (state : MarkedCutController.SplitState κ ρ) (active : code (SplitController.program key) state ≠ .halt) :
    program key right repair initial (splitting state) = (code (SplitController.program key) state).mapState splitting := by
  cases state with
  | ready state => cases state with
    | returning depth => cases depth with
      | zero => exact False.elim (active rfl)
      | succ => rfl
    | search | descend | parent | turn | enter | joining | up | write => rfl
  | reading | writing | error => rfl

theorem joining_code (key : κ) (right : Bool) (repair : Program σ (MarkedRecord κ ρ)) (initial : σ)
    (state : MarkedCutController.JoinState κ ρ) (active : code JoinController.program state ≠ .halt) :
    program key right repair initial (joining state) = (code JoinController.program state).mapState joining := by
  cases state with
  | ready state => cases state with
    | returning depth => cases depth with
      | zero => exact False.elim (active rfl)
      | succ => rfl
    | observing | turn | descend | refresh | balancing => rfl
  | reading | writing | error => rfl

theorem child_repair (key : κ) (right : Bool) (repair : Program σ (MarkedRecord κ ρ)) (initial last : σ)
    (record : MarkedRecord κ ρ) (sibling : Source α (MarkedRecord κ ρ))
    (child fresh : AuxiliaryComponent α κ (fun _ => ρ×Bool))
    (clean : Clean fresh.core) (marked : MarkedPorts fresh)
    (terminal : fresh.core = .leaf → isLeaf fresh.tree = true)
    (reads budget) (outside)
    (body : Run repair initial ⟨closed child,[]⟩ last ⟨closed fresh,[]⟩ reads budget) :
    ∃ observed cost, Steps (program key right repair initial) .down
      ⟨PreferenceFlipController.fork right record sibling child.tree,outside⟩ (.joining (.ready (.observing 0 (.read 3 []))))
      ⟨PreferenceFlipController.fork right record sibling fresh.tree,outside⟩ observed cost ∧ cost ≤ budget+6 := by
  let rest := PreferenceFlipController.frame right record sibling::outside
  have down : Step (program key right repair initial) .down
      ⟨PreferenceFlipController.fork right record sibling child.tree,outside⟩ (.marker .closeChild .start)
      ⟨child.tree,rest⟩ none := by cases right <;> exact .nav rfl rfl
  have closedSteps := (RootMarkerController.close_component child rest).map_prefix
    (marking repair initial .closeChild) (marking_code key right repair initial .closeChild)
  have repaired := (body.extend rest).map_prefix (repairing repair) (repairing_code key right repair initial)
  have stopped := run_halted body
  simp only [repairing,stopped,halted,ite_true] at repaired
  obtain ⟨openReads,openCost,openRun,openBound⟩ := RootMarkerController.open_component fresh clean marked terminal rest
  have opened := openRun.map_prefix (marking repair initial .openChild) (marking_code key right repair initial .openChild)
  have up : Step (program key right repair initial) .up ⟨fresh.tree,rest⟩ (.joining (.ready (.observing 0 (.read 3 []))))
      ⟨PreferenceFlipController.fork right record sibling fresh.tree,outside⟩ none := by cases right <;> exact .nav rfl rfl
  have full := (((down.prefix.append closedSteps).append repaired).append opened).append up.prefix
  exact ⟨_,_,full,by omega⟩

end ChaCha.Paper20261030.BoundaryObservations.BoundaryRepairController
