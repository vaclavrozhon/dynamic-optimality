import ChaCha.Paper20261030.ObservedPreparedWriteLabels
import ChaCha.Paper20261030.EnclosedCanonicalComponent

set_option autoImplicit false

/-! Actual preparation and boundary observation inside an enclosing
component. Both phases are one controller; its final registers contain
the reached boundary data. Prefix and parent repair preserve whole-tree
physical invariants and the observed values for the following phase. -/

namespace ChaCha.Paper20261030.SecondaryDecomposition.ObservedPreparedExposure

open ColoredStorage SourcePointer Structural PhysicalForestMetadata Auxiliary AuxiliaryComponent BoundaryObservations PathDecomposition
open LocalComponentForestCompiler LocalComponentCompiler ForestConnector.ThreeColors
open PreparedExposureExecution (Logical Datum)

variable {β ι η G : Type*} [DecidableEq ι] [DecidableEq η] [DecidableEq G]

local instance : LinearOrder (Option Bool) := inferInstanceAs (LinearOrder (WithBot Bool))

abbrev Cell (ι η : Type*) := ι × List (Option (Datum ι η))

theorem active_enclosed (markerId : ι) {a b : Nat} (reference : DepthTree a b) (preferences : DepthSplit → Bool)
    (d : Nat) (terminal : (Secondary.decodeDepth reference preferences).terminal = d) (lower : a < d) (upper : d < b)
    (component : AuxiliaryComponent Nat Nat (Tagged Payload))
    (represented : Represents followsRight (source reference preferences) component)
    (color : Nat → Option Bool) (decorated : Source Nat (η × Cached))
    (erases : decorated.mapRecords Prod.snd = closed component) (logicalUnique : (decorated.inventory Prod.fst).Nodup)
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
    ∃ (left right : AuxiliaryComponent Nat Nat (Tagged Payload)) (low high : Cached),
      ∃ lowId highId terminalId, ∃ taggedHead taggedTail : Source Nat (η × Cached), ∃ finalForest finalConfig,
      ∃ (finalComponent : MultiSourceProgram.Configuration (Option Bool) β (Cell ι η)), ∃ target reads cost,
      low.2.1 = d-1 ∧ high.2.1 = d ∧ Clean left.core ∧ MarkedPorts left ∧ Clean right.core ∧ MarkedPorts right ∧
      taggedHead.mapRecords Prod.snd = left.tree ∧ taggedTail.mapRecords Prod.snd = right.tree ∧
      MultiSourceProgram.Run
        (EnclosedComponentExecution.program entry saved.length
          (headerPath (representation none wingOrientation headerKey payload forest)).length (!outside.isEmpty)
          (ComponentBoundaryContinuation.program (AdjacentExposureController.program (d-1)) true decorated.rootRecord.1) (ComponentBoundaryContinuation.initial (AdjacentExposureController.program (d-1)) true decorated.rootRecord.1 (.first .start)))
        (.first .start) (MultiSourcePacketPrefix.attached saved stored.tree outside global)
        (.second (some ⟨stored.tree.rootRecord.1,finalComponent.tree.rootRecord.1,.ready (.second lowId (ComponentObserverCompiler.ready
          (BoundaryReadController.activeResult Prod.fst color (lowId,low) (highId,high)
            (terminalId,(terminalLeaf d).rootRecord) d taggedHead taggedTail) lowId))⟩) (some .done))
        target reads cost ∧
      (Source.fork (lowId,low) taggedHead
        (.fork (highId,high) (.leaf d (terminalId,(terminalLeaf d).rootRecord)) taggedTail)).inventory Prod.fst =
        decorated.inventory Prod.fst ∧
      ProjectionForest.Represents color
        ⟨annotate Prod.fst color none (.fork (lowId,low) taggedHead
          (.fork (highId,high) (.leaf d (terminalId,(terminalLeaf d).rootRecord)) taggedTail)),[]⟩ (erase finalForest) ∧
      Unique finalForest ∧
      ForestConnector.assemble (representation none wingOrientation headerKey payload finalForest)
        (layout (representation none wingOrientation headerKey payload finalForest)) = some finalConfig ∧
      (∀ q, (representation none wingOrientation headerKey payload finalForest q).isSome =
        (representation none wingOrientation headerKey payload forest q).isSome) ∧
      finalComponent.mapRecords Prod.snd = finalConfig ∧
      MultiSourceSingleCursor.Represents (.inl none)
        (EnclosingPacketOperation.output saved stored.tree.rootRecord.1 ⟨finalComponent.tree,outside⟩) target ∧
      target.tree.inventory Prod.fst = global.tree.inventory Prod.fst ∧
      CanonicalComponentUniqueness.Valid markerId target.tree ∧
      markerId ∉ target.tree.inventory Prod.fst ∧ MultiSourceProgram.WellFormed target ∧
      cost ≤ 2*(474240*(80220*Nat.clog 2 ((LocalReferences.depthReference reference).height+1)+4)+87360)+13 := by
  obtain ⟨left,right,low,high,lowId,highId,terminalId,taggedHead,taggedTail,finalForest,finalConfig,bodyReads,bodyCost,
    lowKey,highKey,leftClean,leftMarked,rightClean,rightMarked,_,headEq,tailEq,body,ids,_,finalRep,finalUnique,finalAssembly,presence,_,bound⟩ :=
    active_labels reference preferences d terminal lower upper component represented color decorated erases logicalUnique
      forest forestRep physicalUnique headerKey payload config assembled
  obtain ⟨header,headerPresent⟩ := virtual_present_root none wingOrientation headerKey payload finalForest
  obtain ⟨finalComponent,target,reads,cost,actual,componentErases,returned,globalIds,finalPhysical,finalReserved,finalValid,bounded⟩ :=
    EnclosedComponentExecution.canonical_aligned markerId _ body stored storedErases outside global globalRep
      wellFormed physical reserved entry entryRep saved
      (representation none wingOrientation headerKey payload forest)
      (representation none wingOrientation headerKey payload finalForest) header headerPresent finalAssembly presence
  exact ⟨left,right,low,high,lowId,highId,terminalId,taggedHead,taggedTail,finalForest,finalConfig,finalComponent,target,reads,cost,
    lowKey,highKey,leftClean,leftMarked,rightClean,rightMarked,headEq,tailEq,actual,ids,finalRep,finalUnique,finalAssembly,presence,componentErases,returned,
    globalIds,finalPhysical,finalReserved,finalValid,by omega⟩

theorem sentinel_enclosed (markerId : ι) {a b : Nat} (reference : DepthTree a b) (preferences : DepthSplit → Bool)
    (d : Nat) (valid : a ≤ d ∧ d ≤ b) (terminal : (Secondary.decodeDepth reference preferences).terminal = d) (upper : d < b)
    (component : AuxiliaryComponent Nat Nat (Tagged Payload))
    (represented : Represents followsRight (suffixSource reference preferences d valid) component)
    (color : Nat → Option Bool) (decorated : Source Nat (η × Cached))
    (erases : decorated.mapRecords Prod.snd = closed component) (logicalUnique : (decorated.inventory Prod.fst).Nodup)
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
    ∃ (right : AuxiliaryComponent Nat Nat (Tagged Payload)) (high : Cached),
      ∃ highId terminalId, ∃ taggedTail : Source Nat (η × Cached), ∃ finalForest finalConfig,
      ∃ (finalComponent : MultiSourceProgram.Configuration (Option Bool) β (Cell ι η)), ∃ target reads cost,
      high.2.1 = d ∧ Clean right.core ∧ MarkedPorts right ∧ taggedTail.mapRecords Prod.snd = right.tree ∧
      MultiSourceProgram.Run
        (EnclosedComponentExecution.program entry saved.length
          (headerPath (representation none wingOrientation headerKey payload forest)).length (!outside.isEmpty)
          (ComponentBoundaryContinuation.program (OpenSplitController.program d) false decorated.rootRecord.1) (ComponentBoundaryContinuation.initial (OpenSplitController.program d) false decorated.rootRecord.1 .start))
        (.first .start) (MultiSourcePacketPrefix.attached saved stored.tree outside global)
        (.second (some ⟨stored.tree.rootRecord.1,finalComponent.tree.rootRecord.1,.ready (.second highId (ComponentObserverCompiler.ready
          (BoundaryReadController.sentinelResult Prod.fst color (highId,high)
            (terminalId,(terminalLeaf d).rootRecord) d taggedTail) highId))⟩) (some .done))
        target reads cost ∧
      (Source.fork (highId,high) (.leaf d (terminalId,(terminalLeaf d).rootRecord)) taggedTail).inventory Prod.fst =
        decorated.inventory Prod.fst ∧
      ProjectionForest.Represents color
        ⟨annotate Prod.fst color none (.fork (highId,high) (.leaf d (terminalId,(terminalLeaf d).rootRecord)) taggedTail),[]⟩ (erase finalForest) ∧
      Unique finalForest ∧
      ForestConnector.assemble (representation none wingOrientation headerKey payload finalForest)
        (layout (representation none wingOrientation headerKey payload finalForest)) = some finalConfig ∧
      (∀ q, (representation none wingOrientation headerKey payload finalForest q).isSome =
        (representation none wingOrientation headerKey payload forest q).isSome) ∧
      finalComponent.mapRecords Prod.snd = finalConfig ∧
      MultiSourceSingleCursor.Represents (.inl none)
        (EnclosingPacketOperation.output saved stored.tree.rootRecord.1 ⟨finalComponent.tree,outside⟩) target ∧
      target.tree.inventory Prod.fst = global.tree.inventory Prod.fst ∧
      CanonicalComponentUniqueness.Valid markerId target.tree ∧
      markerId ∉ target.tree.inventory Prod.fst ∧ MultiSourceProgram.WellFormed target ∧
      cost ≤ 2*(474240*(40110*Nat.clog 2 ((LocalReferences.depthReference reference).height+1)+2)+49920)+13 := by
  obtain ⟨right,high,highId,terminalId,taggedTail,finalForest,finalConfig,bodyReads,bodyCost,
    highKey,rightClean,rightMarked,_,tailEq,body,ids,_,finalRep,finalUnique,finalAssembly,presence,_,bound⟩ :=
    sentinel_labels reference preferences d valid terminal upper component represented color decorated erases logicalUnique
      forest forestRep physicalUnique headerKey payload config assembled
  obtain ⟨header,headerPresent⟩ := virtual_present_root none wingOrientation headerKey payload finalForest
  obtain ⟨finalComponent,target,reads,cost,actual,componentErases,returned,globalIds,finalPhysical,finalReserved,finalValid,bounded⟩ :=
    EnclosedComponentExecution.canonical_aligned markerId _ body stored storedErases outside global globalRep
      wellFormed physical reserved entry entryRep saved
      (representation none wingOrientation headerKey payload forest)
      (representation none wingOrientation headerKey payload finalForest) header headerPresent finalAssembly presence
  exact ⟨right,high,highId,terminalId,taggedTail,finalForest,finalConfig,finalComponent,target,reads,cost,
    highKey,rightClean,rightMarked,tailEq,actual,ids,finalRep,finalUnique,finalAssembly,presence,componentErases,returned,
    globalIds,finalPhysical,finalReserved,finalValid,by omega⟩

end ChaCha.Paper20261030.SecondaryDecomposition.ObservedPreparedExposure
