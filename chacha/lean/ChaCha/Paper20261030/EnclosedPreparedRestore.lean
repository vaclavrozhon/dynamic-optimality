import ChaCha.Paper20261030.EnclosedRootedComponentAlignment
import ChaCha.Paper20261030.CompiledPreparedRestore
import ChaCha.Paper20261030.LocalPreparedRestore

set_option autoImplicit false

/-! Balanced restoration inside an enclosing shared tree. The same
secondary source controllers run through the aligned nested compiler,
including actual restoration of the enclosing prefix and parent fields. -/

namespace ChaCha.Paper20261030.SecondaryDecomposition.PreparedRestoreExecution

open Std Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open ColoredStorage SourcePointer Structural PhysicalForestMetadata Auxiliary AuxiliaryComponent BoundaryObservations PathDecomposition
open LocalComponentForestCompiler LocalComponentCompiler ForestConnector.ThreeColors

variable {β ι η G : Type*} [DecidableEq ι] [DecidableEq η] [DecidableEq G]

local instance : LinearOrder (Option Bool) := inferInstanceAs (LinearOrder (WithBot Bool))

abbrev Cell (ι η : Type*) := ι × List (Option (Datum ι η))

def enclosedProgram (entry : Sum (Option Bool) G) (count levels : Nat) (hasParent prefixPresent : Bool) (initialId : η) :=
  EnclosedComponentExecution.program entry count levels hasParent (program (ι := ι) prefixPresent)
    (ready (HeadRestoreController.initial prefixPresent) initialId)

theorem sentinel_enclosed (markerId : ι) {a b : Nat} (reference : DepthTree a b) (preferences : DepthSplit → Bool)
    (d : Nat) (valid : a ≤ d ∧ d ≤ b) (terminal : (Secondary.decodeDepth reference preferences).terminal = d)
    (component : AuxiliaryComponent Nat Nat (Tagged Payload))
    (represented : Represents followsRight (suffixSource reference preferences d valid) component)
    (found : searchResult d component.core = true)
    (color : Nat → Option Bool) (decorated : Source Nat (η × Cached))
    (erases : decorated.mapRecords Prod.snd =
      .fork (component.core.size,⟨d,(splitAt d component.core component.balanced found).value⟩)
        (terminalLeaf d) (cutRight component d found).tree)
    (logicalUnique : (decorated.inventory Prod.fst).Nodup)
    (forest : TaggedForest (Option Bool) Nat (Logical η) ι)
    (forestRep : ProjectionForest.Represents color ⟨annotate Prod.fst color none decorated,[]⟩ (erase forest))
    (physicalUnique : Unique forest) (headerKey : Nat)
    (payload : Option Bool → Nat → Source β (List (Option (Datum ι η))))
    (config : MultiSourceProgram.Configuration (Option Bool) β (List (Option (Datum ι η))))
    (assembled : ForestConnector.assemble (representation none wingOrientation headerKey payload forest)
      (layout (representation none wingOrientation headerKey payload forest)) = some config)
    (stored : MultiSourceProgram.Configuration (Option Bool) β (Cell ι η))
    (storedErases : stored.mapRecords Prod.snd = config)
    (outside : List (Frame β (Cell ι η)))
    (global : MultiSourceProgram.Configuration (Sum (Option Bool) G) β (Cell ι η))
    (globalRep : MultiSourceRegisterExtension.project global = stored.extend outside)
    (wellFormed : MultiSourceProgram.WellFormed global)
    (physical : CanonicalComponentUniqueness.Valid markerId global.tree)
    (reserved : markerId ∉ global.tree.inventory Prod.fst)
    (entry : Sum (Option Bool) G)
    (entryRep : MultiSourceSingleCursor.Represents entry ⟨stored.tree,outside⟩ global)
    (saved : List (Option (Datum ι η))) :
    ∃ (out : AuxiliaryComponent Nat Nat (Tagged Payload)) (target : Source Nat (η × Cached)),
      ∃ finalForest finalConfig,
      ∃ (finalComponent : MultiSourceProgram.Configuration (Option Bool) β (Cell ι η)), ∃ actualConfig reads cost,
      Equivalent out component ∧ Represents followsRight (suffixSource reference preferences d valid) out ∧
      MultiSourceProgram.Run
        (enclosedProgram entry saved.length (headerPath (representation none wingOrientation headerKey payload forest)).length
          (!outside.isEmpty) false decorated.rootRecord.1)
        (.first .start) (MultiSourcePacketPrefix.attached saved stored.tree outside global)
        (.second (some ⟨stored.tree.rootRecord.1,finalComponent.tree.rootRecord.1,.ready (ready .done target.rootRecord.1)⟩)
          (some .done)) actualConfig reads cost ∧
      target.mapRecords Prod.snd = closed out ∧ target.inventory Prod.fst = decorated.inventory Prod.fst ∧
      ProjectionForest.Represents color ⟨annotate Prod.fst color none target,[]⟩ (erase finalForest) ∧ Unique finalForest ∧
      ForestConnector.assemble (representation none wingOrientation headerKey payload finalForest)
        (layout (representation none wingOrientation headerKey payload finalForest)) = some finalConfig ∧
      (∀ q, (representation none wingOrientation headerKey payload finalForest q).isSome =
        (representation none wingOrientation headerKey payload forest q).isSome) ∧
      finalComponent.mapRecords Prod.snd = finalConfig ∧
      MultiSourceSingleCursor.Represents (.inl none)
        (EnclosingPacketOperation.output saved stored.tree.rootRecord.1 ⟨finalComponent.tree,outside⟩) actualConfig ∧
      actualConfig.tree.inventory Prod.fst = global.tree.inventory Prod.fst ∧
      CanonicalComponentUniqueness.Valid markerId actualConfig.tree ∧
      markerId ∉ actualConfig.tree.inventory Prod.fst ∧ MultiSourceProgram.WellFormed actualConfig ∧
      cost ≤ 948480*(2100*Nat.clog 2 ((LocalReferences.depthReference reference).height+1)+310)+13 := by
  obtain ⟨out,equivalent,outRep,sourceReads,sourceCost,sourceRun,sourceBound⟩ :=
    PreparedRestoreController.sentinel reference preferences d valid terminal component represented found []
  obtain ⟨target,finalForest,finalConfig,finalComponent,actualConfig,reads,cost,actual,targetErases,ids,
    finalRep,finalUnique,finalAssembly,presence,componentErases,returned,globalIds,finalPhysical,finalReserved,finalValid,bound⟩ :=
    EnclosedRootedComponentExecution.execute_aligned markerId (HeadRestoreController.program false) color headerKey payload sourceRun
      decorated erases logicalUnique forest forestRep physicalUnique config assembled stored storedErases outside global globalRep
      wellFormed physical reserved entry entryRep saved
  exact ⟨out,target,finalForest,finalConfig,finalComponent,actualConfig,reads,cost,equivalent,outRep,
    actual,targetErases,ids,finalRep,finalUnique,finalAssembly,presence,componentErases,returned,globalIds,
    finalPhysical,finalReserved,finalValid,by omega⟩

theorem active_enclosed (markerId : ι) {a b : Nat} (reference : DepthTree a b) (oldPreferences incomingPreferences : DepthSplit → Bool)
    (d : Nat) (valid : a ≤ d ∧ d ≤ b) (lower : a < d)
    (preparedOld : (Secondary.decodeDepth reference oldPreferences).terminal = d)
    (preparedIncoming : (Secondary.decodeDepth reference incomingPreferences).terminal = d)
    (old incoming : AuxiliaryComponent Nat Nat (Tagged Payload))
    (oldRep : Represents followsRight (source reference oldPreferences) old)
    (incomingRep : Represents followsRight (suffixSource reference incomingPreferences d valid) incoming)
    (lowFound : searchResult (d-1) old.core = true) (highFound : searchResult d incoming.core = true)
    (color : Nat → Option Bool) (decorated : Source Nat (η × Cached))
    (erases : decorated.mapRecords Prod.snd =
      .fork (old.core.size,⟨d-1,(splitAt (d-1) old.core old.balanced lowFound).value⟩)
        (cutLeft old (d-1) lowFound).tree
        (.fork (incoming.core.size,⟨d,(splitAt d incoming.core incoming.balanced highFound).value⟩)
          (terminalLeaf d) (cutRight incoming d highFound).tree))
    (logicalUnique : (decorated.inventory Prod.fst).Nodup)
    (forest : TaggedForest (Option Bool) Nat (Logical η) ι)
    (forestRep : ProjectionForest.Represents color ⟨annotate Prod.fst color none decorated,[]⟩ (erase forest))
    (physicalUnique : Unique forest) (headerKey : Nat)
    (payload : Option Bool → Nat → Source β (List (Option (Datum ι η))))
    (config : MultiSourceProgram.Configuration (Option Bool) β (List (Option (Datum ι η))))
    (assembled : ForestConnector.assemble (representation none wingOrientation headerKey payload forest)
      (layout (representation none wingOrientation headerKey payload forest)) = some config)
    (stored : MultiSourceProgram.Configuration (Option Bool) β (Cell ι η))
    (storedErases : stored.mapRecords Prod.snd = config)
    (outside : List (Frame β (Cell ι η)))
    (global : MultiSourceProgram.Configuration (Sum (Option Bool) G) β (Cell ι η))
    (globalRep : MultiSourceRegisterExtension.project global = stored.extend outside)
    (wellFormed : MultiSourceProgram.WellFormed global)
    (physical : CanonicalComponentUniqueness.Valid markerId global.tree)
    (reserved : markerId ∉ global.tree.inventory Prod.fst)
    (entry : Sum (Option Bool) G)
    (entryRep : MultiSourceSingleCursor.Represents entry ⟨stored.tree,outside⟩ global)
    (saved : List (Option (Datum ι η))) :
    ∃ (out : AuxiliaryComponent Nat Nat (Tagged Payload)) (target : Source Nat (η × Cached)),
      ∃ finalForest finalConfig,
      ∃ (finalComponent : MultiSourceProgram.Configuration (Option Bool) β (Cell ι η)), ∃ actualConfig reads cost,
      Represents followsRight (source reference (Secondary.spliceBits d oldPreferences incomingPreferences)) out ∧
      MultiSourceProgram.Run
        (enclosedProgram entry saved.length (headerPath (representation none wingOrientation headerKey payload forest)).length
          (!outside.isEmpty) true decorated.rootRecord.1)
        (.first .start) (MultiSourcePacketPrefix.attached saved stored.tree outside global)
        (.second (some ⟨stored.tree.rootRecord.1,finalComponent.tree.rootRecord.1,.ready (ready .done target.rootRecord.1)⟩)
          (some .done)) actualConfig reads cost ∧
      target.mapRecords Prod.snd = closed out ∧ target.inventory Prod.fst = decorated.inventory Prod.fst ∧
      ProjectionForest.Represents color ⟨annotate Prod.fst color none target,[]⟩ (erase finalForest) ∧ Unique finalForest ∧
      ForestConnector.assemble (representation none wingOrientation headerKey payload finalForest)
        (layout (representation none wingOrientation headerKey payload finalForest)) = some finalConfig ∧
      (∀ q, (representation none wingOrientation headerKey payload finalForest q).isSome =
        (representation none wingOrientation headerKey payload forest q).isSome) ∧
      finalComponent.mapRecords Prod.snd = finalConfig ∧
      MultiSourceSingleCursor.Represents (.inl none)
        (EnclosingPacketOperation.output saved stored.tree.rootRecord.1 ⟨finalComponent.tree,outside⟩) actualConfig ∧
      actualConfig.tree.inventory Prod.fst = global.tree.inventory Prod.fst ∧
      CanonicalComponentUniqueness.Valid markerId actualConfig.tree ∧
      markerId ∉ actualConfig.tree.inventory Prod.fst ∧ MultiSourceProgram.WellFormed actualConfig ∧
      cost ≤ 948480*(6300*Nat.clog 2 ((LocalReferences.depthReference reference).height+1)+620)+13 := by
  obtain ⟨out,outRep,sourceReads,sourceCost,sourceRun,sourceBound⟩ :=
    PreparedRestoreController.active reference oldPreferences incomingPreferences d valid lower preparedOld preparedIncoming
      old incoming oldRep incomingRep lowFound highFound []
  obtain ⟨target,finalForest,finalConfig,finalComponent,actualConfig,reads,cost,actual,targetErases,ids,
    finalRep,finalUnique,finalAssembly,presence,componentErases,returned,globalIds,finalPhysical,finalReserved,finalValid,bound⟩ :=
    EnclosedRootedComponentExecution.execute_aligned markerId (HeadRestoreController.program true) color headerKey payload sourceRun
      decorated erases logicalUnique forest forestRep physicalUnique config assembled stored storedErases outside global globalRep
      wellFormed physical reserved entry entryRep saved
  exact ⟨out,target,finalForest,finalConfig,finalComponent,actualConfig,reads,cost,outRep,
    actual,targetErases,ids,finalRep,finalUnique,finalAssembly,presence,componentErases,returned,globalIds,
    finalPhysical,finalReserved,finalValid,by omega⟩

theorem root_active_enclosed (markerId : ι) {a b : Nat} (reference : DepthTree a b) (oldPreferences incomingPreferences : DepthSplit → Bool)
    (preparedOld : (Secondary.decodeDepth reference oldPreferences).terminal = a)
    (preparedIncoming : (Secondary.decodeDepth reference incomingPreferences).terminal = a)
    (incoming : AuxiliaryComponent Nat Nat (Tagged Payload))
    (incomingRep : Represents followsRight
      (suffixSource reference incomingPreferences a ⟨le_rfl,Secondary.reference_bounds reference⟩) incoming)
    (found : searchResult a incoming.core = true)
    (color : Nat → Option Bool) (decorated : Source Nat (η × Cached))
    (erases : decorated.mapRecords Prod.snd =
      .fork (incoming.core.size,⟨a,(splitAt a incoming.core incoming.balanced found).value⟩)
        (terminalLeaf a) (cutRight incoming a found).tree)
    (logicalUnique : (decorated.inventory Prod.fst).Nodup)
    (forest : TaggedForest (Option Bool) Nat (Logical η) ι)
    (forestRep : ProjectionForest.Represents color ⟨annotate Prod.fst color none decorated,[]⟩ (erase forest))
    (physicalUnique : Unique forest) (headerKey : Nat)
    (payload : Option Bool → Nat → Source β (List (Option (Datum ι η))))
    (config : MultiSourceProgram.Configuration (Option Bool) β (List (Option (Datum ι η))))
    (assembled : ForestConnector.assemble (representation none wingOrientation headerKey payload forest)
      (layout (representation none wingOrientation headerKey payload forest)) = some config)
    (stored : MultiSourceProgram.Configuration (Option Bool) β (Cell ι η))
    (storedErases : stored.mapRecords Prod.snd = config)
    (outside : List (Frame β (Cell ι η)))
    (global : MultiSourceProgram.Configuration (Sum (Option Bool) G) β (Cell ι η))
    (globalRep : MultiSourceRegisterExtension.project global = stored.extend outside)
    (wellFormed : MultiSourceProgram.WellFormed global)
    (physical : CanonicalComponentUniqueness.Valid markerId global.tree)
    (reserved : markerId ∉ global.tree.inventory Prod.fst)
    (entry : Sum (Option Bool) G)
    (entryRep : MultiSourceSingleCursor.Represents entry ⟨stored.tree,outside⟩ global)
    (saved : List (Option (Datum ι η))) :
    ∃ (out : AuxiliaryComponent Nat Nat (Tagged Payload)) (target : Source Nat (η × Cached)),
      ∃ finalForest finalConfig,
      ∃ (finalComponent : MultiSourceProgram.Configuration (Option Bool) β (Cell ι η)), ∃ actualConfig reads cost,
      Represents followsRight (source reference (Secondary.spliceBits a oldPreferences incomingPreferences)) out ∧
      MultiSourceProgram.Run
        (enclosedProgram entry saved.length (headerPath (representation none wingOrientation headerKey payload forest)).length
          (!outside.isEmpty) false decorated.rootRecord.1)
        (.first .start) (MultiSourcePacketPrefix.attached saved stored.tree outside global)
        (.second (some ⟨stored.tree.rootRecord.1,finalComponent.tree.rootRecord.1,.ready (ready .done target.rootRecord.1)⟩)
          (some .done)) actualConfig reads cost ∧
      target.mapRecords Prod.snd = closed out ∧ target.inventory Prod.fst = decorated.inventory Prod.fst ∧
      ProjectionForest.Represents color ⟨annotate Prod.fst color none target,[]⟩ (erase finalForest) ∧ Unique finalForest ∧
      ForestConnector.assemble (representation none wingOrientation headerKey payload finalForest)
        (layout (representation none wingOrientation headerKey payload finalForest)) = some finalConfig ∧
      (∀ q, (representation none wingOrientation headerKey payload finalForest q).isSome =
        (representation none wingOrientation headerKey payload forest q).isSome) ∧
      finalComponent.mapRecords Prod.snd = finalConfig ∧
      MultiSourceSingleCursor.Represents (.inl none)
        (EnclosingPacketOperation.output saved stored.tree.rootRecord.1 ⟨finalComponent.tree,outside⟩) actualConfig ∧
      actualConfig.tree.inventory Prod.fst = global.tree.inventory Prod.fst ∧
      CanonicalComponentUniqueness.Valid markerId actualConfig.tree ∧
      markerId ∉ actualConfig.tree.inventory Prod.fst ∧ MultiSourceProgram.WellFormed actualConfig ∧
      cost ≤ 948480*(2100*Nat.clog 2 ((LocalReferences.depthReference reference).height+1)+310)+13 := by
  obtain ⟨out,outRep,sourceReads,sourceCost,sourceRun,sourceBound⟩ :=
    PreparedRestoreController.root_active reference oldPreferences incomingPreferences preparedOld preparedIncoming incoming incomingRep found []
  obtain ⟨target,finalForest,finalConfig,finalComponent,actualConfig,reads,cost,actual,targetErases,ids,
    finalRep,finalUnique,finalAssembly,presence,componentErases,returned,globalIds,finalPhysical,finalReserved,finalValid,bound⟩ :=
    EnclosedRootedComponentExecution.execute_aligned markerId (HeadRestoreController.program false) color headerKey payload sourceRun
      decorated erases logicalUnique forest forestRep physicalUnique config assembled stored storedErases outside global globalRep
      wellFormed physical reserved entry entryRep saved
  exact ⟨out,target,finalForest,finalConfig,finalComponent,actualConfig,reads,cost,outRep,
    actual,targetErases,ids,finalRep,finalUnique,finalAssembly,presence,componentErases,returned,globalIds,
    finalPhysical,finalReserved,finalValid,by omega⟩

end ChaCha.Paper20261030.SecondaryDecomposition.PreparedRestoreExecution
