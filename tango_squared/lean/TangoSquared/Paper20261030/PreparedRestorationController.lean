import TangoSquared.Paper20261030.PreparedHeadCacheController
import TangoSquared.Paper20261030.CachedPreparedRestoration

set_option autoImplicit false

/-! The interior controller restores the dormant component, parks its
new root, restores the active component, and parks the new active root.
Both copies are charged. The composition lemma takes the two executed
restoration phases as premises; proving their maintained enclosing
representations in sequence is still a separate obligation. -/

namespace TangoSquared.Paper20261030.SecondaryDecomposition.PreparedRestorationController

open ColoredStorage SourcePointer MultiSourceProgram BoundaryObservations
open ObservedPreparedExposure (CachedCell)
open PreparedHeadController (Data)
open PreparedPairHeaderController (Inputs)

variable {η G : Type*} [DecidableEq η] [DecidableEq G]

def restore (entry : Sum (Option Bool) G) (count : Nat) (hasParent prefixPresent : Bool) :=
  CachedRootedComponentExecution.program (α := Nat) (ρ := Cached) (ι := Nat) (η := η) entry count hasParent
    (fun _ => HeadRestoreController.program prefixPresent) (fun _ => HeadRestoreController.initial prefixPresent)

def parkActive (activeAnchor : G) : Program Bool (Sum (Option Bool) G) (CachedCell Nat η)
  | false => .copy (.inr activeAnchor) (.inl none) true
  | true => .halt

theorem park_run {β : Type*} (activeAnchor : G) (config : Configuration (Sum (Option Bool) G) β (CachedCell Nat η)) :
    Run (parkActive activeAnchor) false config true (copyResult config (.inr activeAnchor) (.inl none)) [] 1 :=
  .next (.copy (program := parkActive activeAnchor) (state := false) rfl) (.halt rfl)

def active (activeAnchor : G) (count : Nat) (hasParent : Bool) :=
  MultiSourceFinish.program (restore (η := η) (.inr activeAnchor) count hasParent true)
    (fun _ => ()) (fun _ => false) (fun _ => parkActive activeAnchor)

def restoring (activeAnchor dormantAnchor : G) (count : Nat) (hasParent : Bool) :=
  MultiSourceFinish.program (restore (η := η) (.inr dormantAnchor) 2 true false)
    (fun _ => ()) (fun _ => none)
    (fun _ => MultiSourceParkContinuation.program (.inr dormantAnchor) (.inl none)
      (active activeAnchor count hasParent) (.first (.first .start)))

def program (entry : Sum (Option Bool) G) (markerId count : Nat) (hasParent : Bool)
    (activeAnchor dormantAnchor : G) (depth : Nat) :=
  MultiSourceFinish.program
    (PreparedHeadCacheController.program (η := η) entry markerId count hasParent activeAnchor dormantAnchor depth)
    (fun _ => ()) (fun _ => .first (.first .start))
    (fun _ => restoring activeAnchor dormantAnchor count hasParent)

set_option backward.isDefEq.respectTransparency false in
theorem compose {β : Type*} (entry : Sum (Option Bool) G) (markerId count : Nat) (hasParent : Bool)
    (activeAnchor dormantAnchor : G) (depth : Nat) (inputs : Inputs η) (data : Data η)
    (before afterHead afterDormant afterActive : Configuration (Sum (Option Bool) G) β (CachedCell Nat η))
    {headReads headCost dormantReads dormantCost activeReads activeCost dormantLast activeLast}
    (headRun : Run (PreparedHeadCacheController.program entry markerId count hasParent activeAnchor dormantAnchor depth)
      (.first (.first (.first (.first (.first (.first .start)))))) before
      (.second (some (inputs,data)) (.second () (some .done))) afterHead headReads headCost)
    (dormantRun : Run (restore (.inr dormantAnchor) 2 true false) (.first .start) afterHead dormantLast afterDormant dormantReads dormantCost)
    (activeRun : Run (restore (.inr activeAnchor) count hasParent true) (.first .start)
      (copyResult afterDormant (.inr dormantAnchor) (.inl none)) activeLast afterActive activeReads activeCost) :
    Run (program entry markerId count hasParent activeAnchor dormantAnchor depth)
      (.first (.first (.first (.first (.first (.first (.first .start))))))) before
      (.second () (.second () (some (.second () true))))
      (copyResult afterActive (.inr activeAnchor) (.inl none))
      (headReads++dormantReads++activeReads) (headCost+dormantCost+activeCost+2) := by
  have activeFinished := MultiSourceFinish.finish (fun _ => ()) (fun _ => false) (fun _ => parkActive activeAnchor)
    activeRun (park_run activeAnchor afterActive)
  change Run (active activeAnchor count hasParent) (.first (.first .start)) _ _ _ _ _ at activeFinished
  have parkedDormant := MultiSourceParkContinuation.execute (.inr dormantAnchor) (.inl none)
    (active activeAnchor count hasParent) (.first (.first .start)) (.second () true) afterDormant _ activeFinished
  have restored := MultiSourceFinish.finish (fun _ => ()) (fun _ => none)
    (fun _ => MultiSourceParkContinuation.program (.inr dormantAnchor) (.inl none)
      (active activeAnchor count hasParent) (.first (.first .start))) dormantRun parkedDormant
  change Run (restoring activeAnchor dormantAnchor count hasParent) (.first (.first .start)) _ _ _ _ _ at restored
  have complete := MultiSourceFinish.finish (fun _ => ()) (fun _ => .first (.first .start))
    (fun _ => restoring activeAnchor dormantAnchor count hasParent) headRun restored
  change Run (program entry markerId count hasParent activeAnchor dormantAnchor depth)
    (.first (.first (.first (.first (.first (.first (.first .start))))))) _ _ _ _ _ at complete
  simpa only [List.append_nil,List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using complete

end TangoSquared.Paper20261030.SecondaryDecomposition.PreparedRestorationController
