import TangoSquared.Paper20261030.HeadCacheFrameExecution
import TangoSquared.Paper20261030.PreparedHeadController
import TangoSquared.Paper20261030.RootPreparedHeadController

set_option autoImplicit false

/-! The two prepared head controllers expose cache preservation through
their physical exchange phase. The preparation frame is composed by the
caller, and subsequent explicit root refreshes supply their own frames.
-/

namespace TangoSquared.Paper20261030.SecondaryDecomposition.PreparedHeadController

open ColoredStorage SourcePointer MultiSourceProgram
open ObservedPreparedExposure (CachedCell ReentryCell)
open PreparedPairHeaderController (Inputs Virtual)

variable {η G : Type*} [DecidableEq η] [DecidableEq G]

set_option backward.isDefEq.respectTransparency false in
theorem append_head_frame {β : Type*} (entry : Sum (Option Bool) G) (markerId count : Nat) (hasParent : Bool)
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
      (some (.done (.inr (.ready [])))) rawFinal lastReads lastCost)
    (order : rawFinal.tree.inorderLabels Prod.fst = (middle.mapRecords Prod.fst).tree.inorderLabels Prod.fst)
    (unique : (middle.tree.inventory (fun record => record.1.1)).Nodup) :
    ∃ final reads cost,
      Run (program entry markerId count hasParent activeAnchor incomingAnchor depth)
        (.first (.first (.first (.first .start)))) before
        (.second (some (inputs,data)) (.ready (some (.done (.inr (.ready [])))))) final reads cost ∧
      final.mapRecords Prod.fst = rawFinal ∧
      HeadCacheFrame.MetadataFrame Prod.fst [] middle.tree final.tree ∧
      cost ≤ firstCost+2*lastCost := by
  obtain ⟨final,reads,cost,compiled,erases,_,bound⟩ := MultiSourceAugment.compile_run back middle rfl
  have frame := HeadCacheFrame.augment_frame Prod.fst back order middle rfl unique compiled
  have continuation : Run (source activeAnchor markerId count hasParent (some (inputs,data)))
      (initial (some (inputs,data))) middle (.ready (some (.done (.inr (.ready []))))) final reads cost := compiled
  have actual := MultiSourceFinish.finish select initial (source activeAnchor markerId count hasParent) front
    (by simpa only [select,computed,Option.map_some] using continuation)
  change Run (program entry markerId count hasParent activeAnchor incomingAnchor depth)
    (.first (.first (.first (.first .start)))) _ _ _ _ _ at actual
  refine ⟨final,firstReads++reads,firstCost+cost,?_,erases,frame,by omega⟩
  simpa only [select,computed,Option.map_some] using actual

end TangoSquared.Paper20261030.SecondaryDecomposition.PreparedHeadController

namespace TangoSquared.Paper20261030.SecondaryDecomposition.RootPreparedHeadController

open ColoredStorage SourcePointer MultiSourceProgram
open ObservedPreparedExposure (CachedCell ReentryCell)
open RootPreparedPairHeaderController (Inputs Virtual)

variable {η G : Type*} [DecidableEq η] [DecidableEq G]

set_option backward.isDefEq.respectTransparency false in
theorem append_head_frame {β : Type*} (entry : Sum (Option Bool) G) (markerId count : Nat) (hasParent : Bool)
    (activeAnchor incomingAnchor : G) (depth : Nat)
    (before middle : Configuration (Sum (Option Bool) G) β (CachedCell Nat η))
    (inputs : Inputs η) (activeVirtual incomingVirtual : Virtual Nat η) (data : Data η)
    (computed : ObservedRootHeadParameters.compute Prod.fst inputs.activeValues inputs.incomingValues activeVirtual incomingVirtual = some data)
    {firstReads firstCost}
    (front : Run (RootPreparedPairHeaderController.program entry count hasParent activeAnchor incomingAnchor depth)
      (.first (.first (.first .start))) before
      (.second (some inputs) (.second (some activeVirtual) (some (some (.done (some incomingVirtual)))))) middle firstReads firstCost)
    (rawFinal : Configuration (Sum (Option Bool) G) β (ReentryCell Nat η)) {lastReads lastCost}
    (back : Run (ObservedHeadExchangeExecution.program (.inr activeAnchor) markerId count hasParent data)
      (some (.transferring .start)) (middle.mapRecords Prod.fst)
      (some (.done (.inr (.ready [])))) rawFinal lastReads lastCost)
    (order : rawFinal.tree.inorderLabels Prod.fst = (middle.mapRecords Prod.fst).tree.inorderLabels Prod.fst)
    (unique : (middle.tree.inventory (fun record => record.1.1)).Nodup) :
    ∃ final reads cost,
      Run (program entry markerId count hasParent activeAnchor incomingAnchor depth)
        (.first (.first (.first (.first .start)))) before
        (.second (some (inputs,data)) (.ready (some (.done (.inr (.ready [])))))) final reads cost ∧
      final.mapRecords Prod.fst = rawFinal ∧
      HeadCacheFrame.MetadataFrame Prod.fst [] middle.tree final.tree ∧
      cost ≤ firstCost+2*lastCost := by
  obtain ⟨final,reads,cost,compiled,erases,_,bound⟩ := MultiSourceAugment.compile_run back middle rfl
  have frame := HeadCacheFrame.augment_frame Prod.fst back order middle rfl unique compiled
  have continuation : Run (source activeAnchor markerId count hasParent (some (inputs,data)))
      (initial (some (inputs,data))) middle (.ready (some (.done (.inr (.ready []))))) final reads cost := compiled
  have actual := MultiSourceFinish.finish select initial (source activeAnchor markerId count hasParent) front
    (by simpa only [select,computed,Option.map_some] using continuation)
  change Run (program entry markerId count hasParent activeAnchor incomingAnchor depth)
    (.first (.first (.first (.first .start)))) _ _ _ _ _ at actual
  refine ⟨final,firstReads++reads,firstCost+cost,?_,erases,frame,by omega⟩
  simpa only [select,computed,Option.map_some] using actual

end TangoSquared.Paper20261030.SecondaryDecomposition.RootPreparedHeadController
