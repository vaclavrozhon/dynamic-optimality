import TangoSquared.Paper20261030.PreparedPairHeaderController
import TangoSquared.Paper20261030.ObservedHeadExchangeExecution

set_option autoImplicit false

/-! One runtime controller for preparation, seven observations, parameter
calculation, and the physical head exchange. The cached application field
is carried through every physical edit. Both acquired primary headers are
retained for the subsequent installation of the switched caches. -/

namespace TangoSquared.Paper20261030.SecondaryDecomposition.PreparedHeadController

open ColoredStorage SourcePointer MultiSourceProgram
open ObservedPreparedExposure (CachedCell ReentryCell)
open PreparedPairHeaderController (Inputs PairState Virtual)

variable {η G : Type*} [DecidableEq η] [DecidableEq G]

abbrev Data (η : Type*) := ObservedHeadParameters.Data Nat (η × Cached) η
abbrev Parameters (η : Type*) := Option (Inputs η × Data η)

def select {σ : Type*} : MultiSourceFinish.State σ (PairState Nat η) (Option (Inputs η)) → Parameters η
  | .second (some inputs) (.second (some active) (some (some (.done (some incoming))))) =>
    (ObservedHeadParameters.compute Prod.fst inputs.activeValues inputs.incomingValues active incoming).map
      (fun data => (inputs,data))
  | _ => none

abbrev State (η G : Type*) := MultiSourceAugment.State
  (ObservedHeadExchangeExecution.State Nat (η × Cached) η) (Sum (Option Bool) G)
  (ReentryCell Nat η) (Option (PrimaryHeaderController.Header η))

def source (activeAnchor : G) (markerId count : Nat) (hasParent : Bool) :
    Parameters η → Program (State η G) (Sum (Option Bool) G) (CachedCell Nat η)
  | none => fun _ => .halt
  | some (_,data) => MultiSourceAugment.program
      (ObservedHeadExchangeExecution.program (.inr activeAnchor) markerId count hasParent data)

def initial (_ : Parameters η) : State η G := .ready (some (.transferring .start))

def program (entry : Sum (Option Bool) G) (markerId count : Nat) (hasParent : Bool)
    (activeAnchor incomingAnchor : G) (depth : Nat) :=
  MultiSourceFinish.program
    (PreparedPairHeaderController.program (ι := Nat) (η := η) entry count hasParent activeAnchor incomingAnchor depth)
    select initial (source activeAnchor markerId count hasParent)

set_option backward.isDefEq.respectTransparency false in
theorem append_head {β : Type*} (entry : Sum (Option Bool) G) (markerId count : Nat) (hasParent : Bool)
    (activeAnchor incomingAnchor : G) (depth : Nat)
    (before middle : Configuration (Sum (Option Bool) G) β (CachedCell Nat η))
    (inputs : Inputs η) (activeVirtual incomingVirtual : Virtual Nat η) (data : Data η)
    (computed : ObservedHeadParameters.compute Prod.fst inputs.activeValues inputs.incomingValues activeVirtual incomingVirtual = some data)
    {firstReads firstCost}
    (front : Run (PreparedPairHeaderController.program entry count hasParent activeAnchor incomingAnchor depth)
      (.first (.first (.first .start))) before
      (.second (some inputs) (.second (some activeVirtual) (some (some (.done (some incomingVirtual)))))) middle firstReads firstCost)
    (rawFinal : Configuration (Sum (Option Bool) G) β (ReentryCell Nat η)) {lastReads lastCost}
    (back : Run (ObservedHeadExchangeExecution.program (.inr activeAnchor) markerId count hasParent data)
      (some (.transferring .start)) (middle.mapRecords Prod.fst)
      (some (.done (.inr (.ready [])))) rawFinal lastReads lastCost) :
    ∃ final reads cost,
      Run (program entry markerId count hasParent activeAnchor incomingAnchor depth)
        (.first (.first (.first (.first .start)))) before
        (.second (some (inputs,data)) (.ready (some (.done (.inr (.ready [])))))) final reads cost ∧
      final.mapRecords Prod.fst = rawFinal ∧ cost ≤ firstCost+2*lastCost := by
  obtain ⟨final,reads,cost,compiled,erases,_,bound⟩ := MultiSourceAugment.compile_run back middle rfl
  have continuation : Run (source activeAnchor markerId count hasParent (some (inputs,data)))
      (initial (some (inputs,data))) middle (.ready (some (.done (.inr (.ready []))))) final reads cost := compiled
  have actual := MultiSourceFinish.finish select initial (source activeAnchor markerId count hasParent) front
    (by simpa only [select,computed,Option.map_some] using continuation)
  change Run (program entry markerId count hasParent activeAnchor incomingAnchor depth)
    (.first (.first (.first (.first .start)))) _ _ _ _ _ at actual
  refine ⟨final,firstReads++reads,firstCost+cost,?_,erases,by omega⟩
  simpa only [select,computed,Option.map_some] using actual

end TangoSquared.Paper20261030.SecondaryDecomposition.PreparedHeadController
