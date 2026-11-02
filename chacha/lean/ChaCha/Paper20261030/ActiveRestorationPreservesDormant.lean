import ChaCha.Paper20261030.CachedPreparedRestoration
import ChaCha.Paper20261030.PreparedSplitWitnesses
import ChaCha.Paper20261030.CanonicalRetainedPayloadHandoff
import ChaCha.Paper20261030.CachedAnchorHandoff
import ChaCha.Paper20261030.DecompositionLeaves

set_option autoImplicit false

/-! Active restoration preserves the already restored dormant payload.
The parked finger reaches that same physical subtree after rebalancing,
and its cache survives the active-root refresh. No navigation to an
existentially chosen output cursor is added to the runtime program. -/

namespace ChaCha.Paper20261030.SecondaryDecomposition.ActiveRestorationPreservesDormant

open ColoredStorage SourcePointer Structural PhysicalForestMetadata MultiSourceProgram
open Auxiliary AuxiliaryComponent BoundaryObservations PathDecomposition
open LocalComponentForestCompiler LocalComponentCompiler ForestConnector.ThreeColors
open EnclosedRootedComponentExecution (Packet Cell)
open CachedRootedComponentExecution (CachedCell)

variable {β ι η G : Type*} [DecidableEq ι] [DecidableEq η] [DecidableEq G]

local instance activeRestorationDormantColorOrder : LinearOrder (Option Bool) :=
  inferInstanceAs (LinearOrder (WithBot Bool))

theorem execute (markerId : ι) {a b : Nat} (reference : DepthTree a b) (preferences incomingPreferences : DepthSplit → Bool)
    (d : Nat) (depthValid : a ≤ d ∧ d ≤ b) (lower : a < d)
    (prepared : (Secondary.decodeDepth reference preferences).terminal = d)
    (incomingPrepared : (Secondary.decodeDepth reference incomingPreferences).terminal = d)
    (old incoming left oldRight incomingRight : AuxiliaryComponent Nat Nat (Tagged Payload))
    (oldRep : Represents followsRight (source reference preferences) old)
    (incomingRep : Represents followsRight (suffixSource reference incomingPreferences d depthValid) incoming)
    (low high incomingHigh : Cached)
    (split : PreparedSplitWitnesses.Active old d left oldRight low high)
    (incomingSplit : PreparedSplitWitnesses.Sentinel incoming d incomingRight incomingHigh)
    (color : Nat → Option Bool) (decorated : Source Nat (η × Cached)) (erases : decorated.mapRecords Prod.snd = .fork low left.tree (.fork incomingHigh (terminalLeaf d) incomingRight.tree))
    (logicalUnique : (decorated.inventory Prod.fst).Nodup)
    (forest : TaggedForest (Option Bool) Nat (LocalColoredCompiler.LogicalRecord Cached η (Option Bool)) ι)
    (represented : ProjectionForest.Represents color ⟨annotate Prod.fst color none decorated,[]⟩ (erase forest))
    (physicalUnique : Unique forest) (headerKey : Nat) (payload : Option Bool → Nat → Source β (Packet Nat Cached ι η))
    (config : Configuration (Option Bool) β (Packet Nat Cached ι η))
    (assembled : ForestConnector.assemble (representation none wingOrientation headerKey payload forest)
      (layout (representation none wingOrientation headerKey payload forest)) = some config)
    (current : Cursor β (Cell Nat Cached ι η)) (saved : Packet Nat Cached ι η)
    (view : current.focus.mapRecords Prod.snd = config.tree.setRoot (saved ++ config.tree.rootRecord))
    (global : Configuration (Sum (Option Bool) G) β (Cell Nat Cached ι η))
    (valid : WellFormed global) (physical : CanonicalComponentUniqueness.Valid markerId global.tree)
    (reserved : markerId ∉ global.tree.inventory Prod.fst)
    (entry : Sum (Option Bool) G) (entryRep : MultiSourceSingleCursor.Represents entry current global)
    (header : PrimaryHeaderController.Header η) (bottom : Int) (start : Nat)
    (headerRep : PrimaryHeaderController.Represents header bottom start decorated forest headerKey payload)
    (cached : Configuration (Sum (Option Bool) G) β (CachedCell Nat Cached ι η))
    (cachedErases : cached.mapRecords Prod.fst = global)
    (cachedCurrent : Cursor β (CachedCell Nat Cached ι η))
    (cachedAtRoot : MultiSourceSingleCursor.Represents entry cachedCurrent cached)
    (cachedHeader : cachedCurrent.focus.rootRecord.2 = some header)
    (anchor : G) (dormant : Cursor β (CachedCell Nat Cached ι η))
    (dormantRep : MultiSourceSingleCursor.Represents (.inr anchor) dormant cached)
    (dormantPayload : CanonicalRetainedPayloadHandoff.PayloadAt (payload (color d) d) (dormant.mapRecords Prod.fst))
    (real : color d ≠ none) (distinct : global.tree.shape.leaves.Nodup) :
    ∃ (out : AuxiliaryComponent Nat Nat (Tagged Payload)) (target : Source Nat (η × Cached)), ∃ finalForest finalConfig,
      ∃ (finalComponent : Configuration (Option Bool) β (Cell Nat Cached ι η)), ∃ actualConfig reads cost,
      ∃ reached returnedDormant : Cursor β (CachedCell Nat Cached ι η),
      ∃ dormantTarget : Cursor β (Cell Nat Cached ι η),
      Represents followsRight (source reference (Secondary.spliceBits d preferences incomingPreferences)) out ∧
      Run (CachedRootedComponentExecution.program entry saved.length (!current.ancestors.isEmpty) (fun _ => HeadRestoreController.program true) (fun _ => HeadRestoreController.initial true))
        (.first .start) cached (.second (some (header,target.rootRecord.1,.inl none)) (some .done)) actualConfig reads cost ∧
      target.mapRecords Prod.snd = closed out ∧ target.inventory Prod.fst = decorated.inventory Prod.fst ∧
      ProjectionForest.Represents color ⟨annotate Prod.fst color none target,[]⟩ (erase finalForest) ∧ Unique finalForest ∧
      ForestConnector.assemble (representation none wingOrientation headerKey payload finalForest)
        (layout (representation none wingOrientation headerKey payload finalForest)) = some finalConfig ∧
      (∀ q, (representation none wingOrientation headerKey payload finalForest q).isSome =
        (representation none wingOrientation headerKey payload forest q).isSome) ∧
      finalComponent.mapRecords Prod.snd = finalConfig ∧
      reached.mapRecords Prod.fst = EnclosingPacketOperation.output saved current.focus.rootRecord.1 ⟨finalComponent.tree,current.ancestors⟩ ∧
      MultiSourceSingleCursor.Represents (.inl none) (PrimaryHeaderRefresh.refreshed header target.rootRecord.1 reached) actualConfig ∧
      (PrimaryHeaderRefresh.refreshed header target.rootRecord.1 reached).focus.rootRecord.2 = some {header with rootId := target.rootRecord.1} ∧
      (actualConfig.mapRecords Prod.fst).tree.inventory Prod.fst = global.tree.inventory Prod.fst ∧
      CanonicalComponentUniqueness.Valid markerId (actualConfig.mapRecords Prod.fst).tree ∧
      markerId ∉ (actualConfig.mapRecords Prod.fst).tree.inventory Prod.fst ∧ WellFormed actualConfig ∧
      CachedRootOperation.RetainedMetadata Prod.fst finalComponent.tree.rootRecord.1 cached.tree actualConfig.tree ∧
      (actualConfig.mapRecords Prod.fst).tree.inorderLabels Prod.fst = global.tree.inorderLabels Prod.fst ∧
      (∀ extra : G, fingerLabel Prod.fst (actualConfig.mapRecords Prod.fst) (.inr extra) = fingerLabel Prod.fst global (.inr extra)) ∧
      PrimaryHeaderController.Represents {header with rootId := target.rootRecord.1} bottom start target finalForest headerKey payload ∧
      MultiSourceSingleCursor.Represents (.inr anchor) returnedDormant actualConfig ∧
      returnedDormant.mapRecords Prod.fst = dormantTarget ∧
      returnedDormant.focus.rootRecord.2 = dormant.focus.rootRecord.2 ∧
      CanonicalRetainedPayloadHandoff.PayloadAt (payload (color d) d) dormantTarget ∧
      dormantTarget.focus.rootRecord.1 ≠ finalComponent.tree.rootRecord.1 ∧ dormantTarget.ancestors ≠ [] ∧
      (∃ packet : Packet Nat Cached ι η, packet.length = 2 ∧ dormantTarget.focus.mapRecords Prod.snd =
        (payload (color d) d).setRoot (packet ++ (payload (color d) d).rootRecord)) ∧
      (SubtreeMetadata.replacePayload (dormant.mapRecords Prod.fst) (payload (color d) d).rootRecord).focus =
        (SubtreeMetadata.replacePayload dormantTarget (payload (color d) d).rootRecord).focus ∧
      cost ≤ 1896960*(6300*Nat.clog 2 ((LocalReferences.depthReference reference).height+1)+620)+45 := by
  obtain ⟨out,target,finalForest,finalConfig,finalComponent,actualConfig,reads,cost,reached,outRep,actual,targetErases,sourceIds,
    finalRep,finalUnique,finalAssembly,presence,componentErases,reachedErases,finalLocated,finalHeader,
    globalIds,finalPhysical,finalReserved,finalValid,metadata,order,anchors,finalCacheRep,bound⟩ :=
    CachedPreparedRestoration.active markerId reference preferences incomingPreferences d depthValid lower prepared incomingPrepared
      old incoming left oldRight incomingRight oldRep incomingRep low high incomingHigh split incomingSplit
      color decorated erases logicalUnique forest represented physicalUnique headerKey payload config assembled current saved view
      global valid physical reserved entry entryRep header bottom start headerRep cached cachedErases cachedCurrent cachedAtRoot cachedHeader
  have member : d ∈ target.shape.leaves := by
    rw [← Source.mapRecords_shape Prod.snd target,targetErases,
      represented_leaf_word reference (Secondary.spliceBits d preferences incomingPreferences) out outRep]
    apply List.mem_range'.mpr
    exact ⟨d-a,by omega,by simp only [Nat.one_mul]; omega⟩
  have returned := finalLocated.mapRecords Prod.fst
  rw [PrimaryHeaderRefresh.refreshed_erases,reachedErases] at returned
  have componentTree : finalComponent.tree.mapRecords Prod.snd = finalConfig.tree := congrArg Configuration.tree componentErases
  have leafWord : (cached.mapRecords Prod.fst).tree.shape.leaves = (actualConfig.mapRecords Prod.fst).tree.shape.leaves := by
    simpa only [Configuration.mapRecords,Source.mapRecords_shape] using actual.leaves
  have actualOrder : (actualConfig.mapRecords Prod.fst).tree.inorderLabels Prod.fst =
      (cached.mapRecords Prod.fst).tree.inorderLabels Prod.fst := by rw [cachedErases]; exact order
  have parked : fingerLabel Prod.fst (actualConfig.mapRecords Prod.fst) (.inr anchor) =
      fingerLabel Prod.fst (cached.mapRecords Prod.fst) (.inr anchor) := by rw [cachedErases]; exact anchors anchor
  have rawDormant := dormantRep.mapRecords Prod.fst
  obtain ⟨dormantTarget,dormantLocated,dormantPayloadRep,different,proper,attachment,samePayload⟩ :=
    CanonicalRetainedPayloadHandoff.handoff color target finalForest finalRep headerKey payload finalConfig finalAssembly
      finalComponent.tree componentTree current.ancestors saved current.focus.rootRecord.1
      (cached.mapRecords Prod.fst) (actualConfig.mapRecords Prod.fst) (.inl none) returned leafWord actualOrder
      (cachedErases.symm ▸ distinct) finalPhysical.2.2 (.inr anchor) parked (dormant.mapRecords Prod.fst) rawDormant d member real dormantPayload
  have originalLabel := fingerLabel_of_represents Prod.fst (cached.mapRecords Prod.fst) (.inr anchor) _ rawDormant
  have newLabel := fingerLabel_of_represents Prod.fst (actualConfig.mapRecords Prod.fst) (.inr anchor) dormantTarget dormantLocated
  rw [parked,originalLabel] at newLabel
  have sameId : dormantTarget.focus.rootRecord.1 = dormant.focus.rootRecord.1.1 := by
    simpa only [Cursor.mapRecords,Source.mapRecords_root] using (Option.some.inj newLabel).symm
  obtain ⟨returnedDormant,returnedDormantRep,dormantErases,dormantHeader⟩ := CachedRootOperation.retained_anchor
    Prod.fst finalComponent.tree.rootRecord.1 cached actualConfig metadata (.inr anchor) dormant dormantRep
      dormantTarget dormantLocated sameId different
  exact ⟨out,target,finalForest,finalConfig,finalComponent,actualConfig,reads,cost,reached,returnedDormant,dormantTarget,
    outRep,actual,targetErases,sourceIds,finalRep,finalUnique,finalAssembly,presence,componentErases,reachedErases,finalLocated,finalHeader,
    globalIds,finalPhysical,finalReserved,finalValid,metadata,order,anchors,finalCacheRep,
    returnedDormantRep,dormantErases,dormantHeader,dormantPayloadRep,different,proper,attachment,samePayload,bound⟩

end ChaCha.Paper20261030.SecondaryDecomposition.ActiveRestorationPreservesDormant
