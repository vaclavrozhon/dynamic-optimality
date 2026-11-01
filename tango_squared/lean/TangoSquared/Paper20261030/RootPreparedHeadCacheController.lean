import TangoSquared.Paper20261030.RootPreparedHeadReturnController
import TangoSquared.Paper20261030.PrimaryHeaderPairRefresh
import TangoSquared.Paper20261030.RootSwitchedHeaderRepresentation

set_option autoImplicit false

/-! Install the switched primary headers after the prepared head exchange
and the charged route to the dormant root. The values are computed from
the retained old headers and the newly repaired logical boundary records. -/

namespace TangoSquared.Paper20261030.SecondaryDecomposition.RootPreparedHeadCacheController

open ColoredStorage SourcePointer MultiSourceProgram
open ObservedPreparedExposure (CachedCell)
open RootPreparedHeadController (Data Parameters)
open RootPreparedPairHeaderController (Inputs)

variable {η G : Type*} [DecidableEq η] [DecidableEq G]

def select {σ : Type*} : MultiSourceFinish.State σ (RootPreparedHeadReturnController.State η) (Parameters η) → Parameters η
  | .second parameters (some (some (.done _))) => parameters
  | _ => none

abbrev RefreshState (η : Type*) := Option (RootRecordTour.State (CachedCell Nat η))
abbrev State (η : Type*) := MultiSourceFinish.State (RefreshState η) (RefreshState η) Unit

def source (activeAnchor dormantAnchor : G) : Parameters η → Program (State η) (Sum (Option Bool) G) (CachedCell Nat η)
  | none => fun _ => .halt
  | some (inputs,data) =>
    let headers := PrimaryHeaderController.switchedMinimum inputs.active inputs.incoming data.fresh
    PrimaryHeaderPairRefresh.program (.inr activeAnchor) (.inr dormantAnchor) headers.1 headers.2

def initial (_ : Parameters η) : State η := .first (some .reading)

def program (entry : Sum (Option Bool) G) (markerId count : Nat) (hasParent : Bool)
    (activeAnchor dormantAnchor : G) (depth : Nat) :=
  MultiSourceFinish.program
    (RootPreparedHeadReturnController.program (η := η) entry markerId count hasParent activeAnchor dormantAnchor depth)
    select initial (source activeAnchor dormantAnchor)

set_option backward.isDefEq.respectTransparency false in
theorem append_refresh {β : Type*} (entry : Sum (Option Bool) G) (markerId count : Nat) (hasParent : Bool)
    (activeAnchor dormantAnchor : G) (depth : Nat)
    (before middle after : Configuration (Sum (Option Bool) G) β (CachedCell Nat η))
    (inputs : Inputs η) (data : Data η) (record : CachedCell Nat η)
    {firstReads firstCost lastReads}
    (front : Run (RootPreparedHeadReturnController.program entry markerId count hasParent activeAnchor dormantAnchor depth)
      (.first (.first (.first (.first (.first .start))))) before
      (.second (some (inputs,data)) (some (some (.done record)))) middle firstReads firstCost)
    (back : Run (PrimaryHeaderPairRefresh.program (.inr activeAnchor) (.inr dormantAnchor)
      (PrimaryHeaderController.switchedMinimum inputs.active inputs.incoming data.fresh).1
      (PrimaryHeaderController.switchedMinimum inputs.active inputs.incoming data.fresh).2)
      (.first (some .reading)) middle (.second () (some .done)) after lastReads 4) :
    Run (program entry markerId count hasParent activeAnchor dormantAnchor depth)
      (.first (.first (.first (.first (.first (.first .start)))))) before
      (.second (some (inputs,data)) (.second () (some .done))) after (firstReads++lastReads) (firstCost+4) := by
  have actual := MultiSourceFinish.finish select initial (source activeAnchor dormantAnchor) front back
  change Run (program entry markerId count hasParent activeAnchor dormantAnchor depth)
    (.first (.first (.first (.first (.first (.first .start)))))) _ _ _ _ _ at actual
  exact actual

end TangoSquared.Paper20261030.SecondaryDecomposition.RootPreparedHeadCacheController
