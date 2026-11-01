import TangoSquared.Paper20261030.RootPreparedHeadController
import TangoSquared.Paper20261030.ObservedRootDormantRoute

set_option autoImplicit false

/-! The full prepared head program followed by a charged route to the new
dormant root. Both primary headers and the computed boundary data remain
in registers, ready for cache replacement and balanced restoration. -/

namespace TangoSquared.Paper20261030.SecondaryDecomposition.RootPreparedHeadReturnController

open ColoredStorage SourcePointer MultiSourceProgram
open ObservedPreparedExposure (CachedCell)
open RootPreparedHeadController (Data Parameters)
open RootPreparedPairHeaderController (Inputs)

variable {η G : Type*} [DecidableEq η] [DecidableEq G]

def select {σ : Type*} : MultiSourceFinish.State σ (RootPreparedHeadController.State η G) (Parameters η) → Parameters η
  | .second parameters (.ready (some (.done (.inr (.ready []))))) => parameters
  | _ => none

abbrev State (η : Type*) := Option (Option (PathRecordRead.State (CachedCell Nat η)))

def source (activeAnchor dormantAnchor : G) : Parameters η → Program (State η) (Sum (Option Bool) G) (CachedCell Nat η)
  | none => fun _ => .halt
  | some (_,data) => PathRecordRead.program (.inr activeAnchor) (.inr dormantAnchor) id (ObservedRootDormantRoute.path data)

def initial (_ : Parameters η) : State η := none

def program (entry : Sum (Option Bool) G) (markerId count : Nat) (hasParent : Bool)
    (activeAnchor dormantAnchor : G) (depth : Nat) :=
  MultiSourceFinish.program
    (RootPreparedHeadController.program (η := η) entry markerId count hasParent activeAnchor dormantAnchor depth)
    select initial (source activeAnchor dormantAnchor)

set_option backward.isDefEq.respectTransparency false in
theorem append_route {β : Type*} (entry : Sum (Option Bool) G) (markerId count : Nat) (hasParent : Bool)
    (activeAnchor dormantAnchor : G) (depth : Nat)
    (before middle after : Configuration (Sum (Option Bool) G) β (CachedCell Nat η))
    (inputs : Inputs η) (data : Data η) (record : CachedCell Nat η)
    {firstReads firstCost lastReads lastCost}
    (front : Run (RootPreparedHeadController.program entry markerId count hasParent activeAnchor dormantAnchor depth)
      (.first (.first (.first (.first .start)))) before
      (.second (some (inputs,data)) (.ready (some (.done (.inr (.ready [])))))) middle firstReads firstCost)
    (back : Run (PathRecordRead.program (.inr activeAnchor) (.inr dormantAnchor) id (ObservedRootDormantRoute.path data))
      none middle (some (some (.done record))) after lastReads lastCost) :
    Run (program entry markerId count hasParent activeAnchor dormantAnchor depth)
      (.first (.first (.first (.first (.first .start))))) before
      (.second (some (inputs,data)) (some (some (.done record)))) after (firstReads++lastReads) (firstCost+lastCost) := by
  have actual := MultiSourceFinish.finish select initial (source activeAnchor dormantAnchor) front back
  change Run (program entry markerId count hasParent activeAnchor dormantAnchor depth)
    (.first (.first (.first (.first (.first .start))))) _ _ _ _ _ at actual
  exact actual

end TangoSquared.Paper20261030.SecondaryDecomposition.RootPreparedHeadReturnController
