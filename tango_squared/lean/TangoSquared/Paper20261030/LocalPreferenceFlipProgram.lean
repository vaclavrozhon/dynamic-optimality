import TangoSquared.Paper20261030.LocalRootMarker
import TangoSquared.Paper20261030.ComponentPreferenceFlip

/-! A local head-preference flip. The new direction and the exposed head
key are scalar inputs. The new application payload is computed from the
record read at the exposed head; no replacement record is supplied by a
proof. The old preferred continuation is closed, the incoming component
is opened, and the existing join controller performs boundary insertion. -/

namespace TangoSquared.Paper20261030.BoundaryObservations.PreferenceFlipController

open Std Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open ColoredStorage Auxiliary AuxiliaryComponent SourceLocalProgram
open GapSource.Controller

variable {α κ ρ : Type*} [Ord κ]

inductive State (κ ρ : Type*) where
  | opening (state : RootMarkerController.State κ ρ)
  | splitting (state : MarkedCutController.SplitState κ ρ)
  | detach
  | closingDetached (state : RootMarkerController.State κ ρ)
  | upDetached
  | changeRead
  | changeWrite (record : MarkedRecord κ ρ)
  | goIncoming
  | openingIncoming (state : RootMarkerController.State κ ρ)
  | upIncoming
  | joining (state : MarkedCutController.JoinState κ ρ)
  | closing (state : RootMarkerController.State κ ρ)
  | done

def opening : RootMarkerController.State κ ρ → State κ ρ
  | .done => .splitting (.ready (.search 0))
  | state => .opening state

def splitting : MarkedCutController.SplitState κ ρ → State κ ρ
  | .ready (.returning 0) => .detach
  | state => .splitting state

def closingDetached : RootMarkerController.State κ ρ → State κ ρ
  | .done => .upDetached
  | state => .closingDetached state

def openingIncoming : RootMarkerController.State κ ρ → State κ ρ
  | .done => .upIncoming
  | state => .openingIncoming state

def joining : MarkedCutController.JoinState κ ρ → State κ ρ
  | .ready (.returning 0) => .closing .start
  | state => .joining state

def closing : RootMarkerController.State κ ρ → State κ ρ
  | .done => .done
  | state => .closing state

def updateRecord (update : κ → ρ → ρ) (record : MarkedRecord κ ρ) : MarkedRecord κ ρ :=
  (record.1,⟨record.2.1,(update record.2.1 record.2.2.1,false)⟩)

def program (key : κ) (newRight : Bool) (update : κ → ρ → ρ) : Program (State κ ρ) (MarkedRecord κ ρ)
  | .opening state => (RootMarkerController.program false true state).mapState opening
  | .splitting state => (code (SplitController.program key) state).mapState splitting
  | .detach => .nav (if newRight then .left else .right) (.closingDetached .start)
  | .closingDetached state => (RootMarkerController.program true false state).mapState closingDetached
  | .upDetached => .nav .up .changeRead
  | .changeRead => .read (fun record _ => .changeWrite (updateRecord update record))
  | .changeWrite record => .write record .goIncoming
  | .goIncoming => .nav (if newRight then .right else .left) (.openingIncoming .start)
  | .openingIncoming state => (RootMarkerController.program false true state).mapState openingIncoming
  | .upIncoming => .nav .up (.joining (.ready (.observing 0 (.read 3 []))))
  | .joining state => (code JoinController.program state).mapState joining
  | .closing state => (RootMarkerController.program true false state).mapState closing
  | .done => .halt

theorem opening_code (key : κ) (right : Bool) (update : κ → ρ → ρ) (state : RootMarkerController.State κ ρ)
    (active : RootMarkerController.program false true state ≠ .halt) :
    program key right update (opening state) = (RootMarkerController.program false true state).mapState opening := by
  cases state with
  | start | write => rfl
  | done => exact False.elim (active rfl)

theorem closingDetached_code (key : κ) (right : Bool) (update : κ → ρ → ρ) (state : RootMarkerController.State κ ρ)
    (active : RootMarkerController.program true false state ≠ .halt) :
    program key right update (closingDetached state) =
      (RootMarkerController.program true false state).mapState closingDetached := by
  cases state with
  | start | write => rfl
  | done => exact False.elim (active rfl)

theorem openingIncoming_code (key : κ) (right : Bool) (update : κ → ρ → ρ) (state : RootMarkerController.State κ ρ)
    (active : RootMarkerController.program false true state ≠ .halt) :
    program key right update (openingIncoming state) =
      (RootMarkerController.program false true state).mapState openingIncoming := by
  cases state with
  | start | write => rfl
  | done => exact False.elim (active rfl)

theorem closing_code (key : κ) (right : Bool) (update : κ → ρ → ρ) (state : RootMarkerController.State κ ρ)
    (active : RootMarkerController.program true false state ≠ .halt) :
    program key right update (closing state) = (RootMarkerController.program true false state).mapState closing := by
  cases state with
  | start | write => rfl
  | done => exact False.elim (active rfl)

theorem splitting_code (key : κ) (right : Bool) (update : κ → ρ → ρ) (state : MarkedCutController.SplitState κ ρ)
    (active : code (SplitController.program key) state ≠ .halt) :
    program key right update (splitting state) = (code (SplitController.program key) state).mapState splitting := by
  cases state with
  | ready state => cases state with
    | returning depth => cases depth with
      | zero => exact False.elim (active rfl)
      | succ => rfl
    | search | descend | parent | turn | enter | joining | up | write => rfl
  | reading | writing | error => rfl

theorem joining_code (key : κ) (right : Bool) (update : κ → ρ → ρ) (state : MarkedCutController.JoinState κ ρ)
    (active : code JoinController.program state ≠ .halt) :
    program key right update (joining state) = (code JoinController.program state).mapState joining := by
  cases state with
  | ready state => cases state with
    | returning depth => cases depth with
      | zero => exact False.elim (active rfl)
      | succ => rfl
    | observing | turn | descend | refresh | balancing => rfl
  | reading | writing | error => rfl

/-- Place a chosen child on the indicated side of its sibling. -/
def fork (right : Bool) (record : MarkedRecord κ ρ) (sibling child : Source α (MarkedRecord κ ρ)) :=
  if right then Source.fork record sibling child else Source.fork record child sibling

def frame (right : Bool) (record : MarkedRecord κ ρ) (sibling : Source α (MarkedRecord κ ρ)) :
    SourcePointer.Frame α (MarkedRecord κ ρ) :=
  if right then .right sibling record else .left record sibling

theorem detach_prefix (key : κ) (right : Bool) (update : κ → ρ → ρ) (record : MarkedRecord κ ρ)
    (sibling : Source α (MarkedRecord κ ρ)) (detached : AuxiliaryComponent α κ (fun _ => ρ×Bool)) (outside) :
    Steps (program key right update) .detach ⟨fork (!right) record sibling detached.tree,outside⟩ .changeRead
      ⟨fork (!right) record sibling (closed detached),outside⟩ [detached.tree.rootRecord] 4 := by
  have down : Step (program key right update) .detach ⟨fork (!right) record sibling detached.tree,outside⟩
      (.closingDetached .start) ⟨detached.tree,frame (!right) record sibling::outside⟩ none := by cases right <;> exact .nav rfl rfl
  have closedSteps := (RootMarkerController.close_component detached (frame (!right) record sibling::outside)).map_prefix
    closingDetached (closingDetached_code key right update)
  have up : Step (program key right update) .upDetached
      ⟨closed detached,frame (!right) record sibling::outside⟩ .changeRead
      ⟨fork (!right) record sibling (BoundaryObservations.closed detached),outside⟩ none := by cases right <;> exact .nav rfl rfl
  simpa only [Option.toList_none,List.nil_append,List.append_nil] using (down.prefix.append closedSteps).append up.prefix

theorem update_prefix (key : κ) (right : Bool) (update : κ → ρ → ρ)
    (source : Source α (MarkedRecord κ ρ)) (outside) :
    Steps (program key right update) .changeRead ⟨source,outside⟩ .goIncoming
      ⟨source.setRoot (updateRecord update source.rootRecord),outside⟩ [source.rootRecord] 2 := by
  have read : Step (program key right update) .changeRead ⟨source,outside⟩
      (.changeWrite (updateRecord update source.rootRecord)) ⟨source,outside⟩ (some source.rootRecord) := by
    apply Step.read (next := fun record _ => State.changeWrite (updateRecord update record)); rfl
  have write : Step (program key right update) (.changeWrite (updateRecord update source.rootRecord))
      ⟨source,outside⟩ .goIncoming ⟨source.setRoot (updateRecord update source.rootRecord),outside⟩ none := .write rfl
  exact .next read (.next write (.nil _ _))

theorem incoming_prefix (key : κ) (right : Bool) (update : κ → ρ → ρ) (record : MarkedRecord κ ρ)
    (sibling : Source α (MarkedRecord κ ρ)) (incoming : AuxiliaryComponent α κ (fun _ => ρ×Bool))
    (clean : Clean incoming.core) (marked : MarkedPorts incoming)
    (terminal : incoming.core = .leaf → isLeaf incoming.tree = true) (outside) :
    ∃ reads cost, Steps (program key right update) .goIncoming
      ⟨fork right record sibling (closed incoming),outside⟩ (.joining (.ready (.observing 0 (.read 3 []))))
      ⟨fork right record sibling incoming.tree,outside⟩ reads cost ∧ cost ≤ 4 := by
  have down : Step (program key right update) .goIncoming ⟨fork right record sibling (closed incoming),outside⟩
      (.openingIncoming .start) ⟨closed incoming,frame right record sibling::outside⟩ none := by cases right <;> exact .nav rfl rfl
  obtain ⟨reads,cost,run,bound⟩ := RootMarkerController.open_component incoming clean marked terminal (frame right record sibling::outside)
  have opened := run.map_prefix openingIncoming (openingIncoming_code key right update)
  have up : Step (program key right update) .upIncoming ⟨incoming.tree,frame right record sibling::outside⟩
      (.joining (.ready (.observing 0 (.read 3 [])))) ⟨fork right record sibling incoming.tree,outside⟩ none := by cases right <;> exact .nav rfl rfl
  exact ⟨_,_,(down.prefix.append opened).append up.prefix,by omega⟩

end TangoSquared.Paper20261030.BoundaryObservations.PreferenceFlipController
