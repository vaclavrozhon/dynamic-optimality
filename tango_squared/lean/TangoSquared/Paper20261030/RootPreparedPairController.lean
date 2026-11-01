import TangoSquared.Paper20261030.CachedIncomingPreparation
import TangoSquared.Paper20261030.MultiSourceParkContinuation

set_option autoImplicit false

/-! One concrete controller for the two preparation phases of an minimum-depth
head switch. It retains the active boundary observations, parks the active
root with one charged copy, and prepares the incoming component using its
stored cache and the known two-entry attachment. Both sets of observed
records remain available to the following head computation.

The composition theorem below joins actual runs on exactly the same
configuration. Deriving all phase premises from a single primary
representation, including the restored enclosing routing view, is a
separate integration obligation. The zero-depth case uses two sentinel splits and has no retained prefix. -/

namespace TangoSquared.Paper20261030.SecondaryDecomposition.RootPreparedPairController

open ColoredStorage SourcePointer Structural PhysicalForestMetadata MultiSourceProgram PrimaryHeaderController BoundaryObservations
open ObservedPreparedExposure (CachedCell)

variable {β ι η G : Type*} [DecidableEq ι] [DecidableEq η] [DecidableEq G]

abbrev Values (η : Type*) := BoundaryReadController.State (LocalColoredCompiler.LogicalRecord Cached η (Option Bool))

def active (entry : Sum (Option Bool) G) (count : Nat) (hasParent : Bool) (depth : Nat) :=
  CachedObservedComponent.program (α := Nat) (ι := ι) entry count hasParent false
    (fun (_ : Header η) => OpenSplitController.program (ρ := DepthSplit × Bool) depth) (fun _ => .start)

def incoming (anchor : G) (depth : Nat) :=
  CachedObservedComponent.program (α := Nat) (ι := ι) (.inr anchor) 2 true false
    (fun (_ : Header η) => OpenSplitController.program (ρ := DepthSplit × Bool) depth) (fun _ => .start)

def parameters {σ τ π : Type*} : MultiSourceFinish.State σ τ (Option π) → Option π
  | .second values _ => values
  | _ => none

def program (entry : Sum (Option Bool) G) (count : Nat) (hasParent : Bool)
    (activeAnchor incomingAnchor : G) (depth : Nat) :=
  MultiSourceFinish.program (active (ι := ι) (η := η) entry count hasParent depth) parameters (fun _ => none)
    (fun _ => MultiSourceParkContinuation.program (.inr activeAnchor) (.inl none)
      (incoming (ι := ι) (η := η) incomingAnchor depth) (.first .start))

theorem compose (entry : Sum (Option Bool) G) (count : Nat) (hasParent : Bool)
    (activeAnchor incomingAnchor : G) (depth : Nat)
    (before middle after : Configuration (Sum (Option Bool) G) β (CachedCell ι η))
    (activeHeader incomingHeader : Header η) (activeRoot incomingRoot : η)
    (activeValues incomingValues : Values η) {firstReads lastReads firstCost lastCost}
    (front : Run (active entry count hasParent depth) (.first .start) before
      (.second (some (activeHeader,activeRoot,.inl none,some activeValues)) (some .done)) middle firstReads firstCost)
    (back : Run (incoming incomingAnchor depth) (.first .start) (copyResult middle (.inr activeAnchor) (.inl none))
      (.second (some (incomingHeader,incomingRoot,.inl none,some incomingValues)) (some .done)) after lastReads lastCost) :
    Run (program entry count hasParent activeAnchor incomingAnchor depth) (.first (.first .start)) before
      (.second (some (activeHeader,activeRoot,.inl none,some activeValues))
        (some (.second (some (incomingHeader,incomingRoot,.inl none,some incomingValues)) (some .done)))) after
      (firstReads++lastReads) (firstCost+lastCost+1) := by
  have parked := MultiSourceParkContinuation.execute (.inr activeAnchor) (.inl none)
    (incoming incomingAnchor depth) (.first .start) _ middle after back
  have actual := MultiSourceFinish.finish parameters (fun _ => none)
    (fun _ => MultiSourceParkContinuation.program (.inr activeAnchor) (.inl none)
      (incoming incomingAnchor depth) (.first .start)) front parked
  change Run (program (ι := ι) (η := η) entry count hasParent activeAnchor incomingAnchor depth)
    (.first (.first .start)) _ _ _ _ _ at actual
  simpa only [parameters,Nat.add_assoc] using actual

end TangoSquared.Paper20261030.SecondaryDecomposition.RootPreparedPairController
