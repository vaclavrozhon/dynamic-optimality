import TangoSquared.Paper20261030.ObservedPreparedWriteLabels
import TangoSquared.Paper20261030.ReenteredRootedComponent

set_option autoImplicit false

/-! Preparing a component and reading its exposed boundary from one
reached root. Working fingers may initially point anywhere. The setup,
preparation, observations, and enclosing repair form one actual program;
all parked extra fingers keep their immutable physical vertex ids. -/

namespace TangoSquared.Paper20261030.SecondaryDecomposition.ObservedPreparedExposure

open ColoredStorage SourcePointer Structural PhysicalForestMetadata Auxiliary AuxiliaryComponent BoundaryObservations PathDecomposition
open LocalComponentForestCompiler LocalComponentCompiler ForestConnector.ThreeColors
open PreparedExposureExecution (Logical Datum)

variable {β ι η G : Type*} [DecidableEq ι] [DecidableEq η] [DecidableEq G]

local instance reenteredPreparationColorOrder : LinearOrder (Option Bool) := inferInstanceAs (LinearOrder (WithBot Bool))

abbrev ReentryCell (ι η : Type*) := ι × List (Option (Datum ι η))

theorem active_reentered (markerId : ι) {a b : Nat} (reference : DepthTree a b) (preferences : DepthSplit → Bool)
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
    (tree : Source β (ReentryCell ι η))
    (treeErases : tree.mapRecords Prod.snd = config.tree)
    (outside : List (Frame β (ReentryCell ι η)))
    (global : MultiSourceProgram.Configuration (Sum (Option Bool) G) β (ReentryCell ι η))
    (wellFormed : MultiSourceProgram.WellFormed global)
    (physical : CanonicalComponentUniqueness.Valid markerId global.tree)
    (reserved : markerId ∉ global.tree.inventory Prod.fst)
    (entry : Sum (Option Bool) G)
    (entryRep : MultiSourceSingleCursor.Represents entry ⟨tree,outside⟩ global)
    (saved : List (Option (Datum ι η))) :
    ∃ (left right : AuxiliaryComponent Nat Nat (Tagged Payload)) (low high : Cached),
      ∃ lowId highId terminalId, ∃ taggedHead taggedTail : Source Nat (η × Cached), ∃ finalForest finalConfig,
      ∃ (finalComponent : MultiSourceProgram.Configuration (Option Bool) β (ReentryCell ι η)), ∃ entryBits finalBits target reads cost,
      low.2.1 = d-1 ∧ high.2.1 = d ∧ Clean left.core ∧ MarkedPorts left ∧ Clean right.core ∧ MarkedPorts right ∧
      PreparedSplitWitnesses.Active component d left right low high ∧
      taggedHead.mapRecords Prod.snd = left.tree ∧ taggedTail.mapRecords Prod.snd = right.tree ∧
      MultiSourceProgram.Run
        (ReenteredComponentExecution.program entry
          (representation none wingOrientation headerKey payload forest (some true)).isSome
          (representation none wingOrientation headerKey payload forest (some false)).isSome saved.length
          (headerPath (representation none wingOrientation headerKey payload forest)).length (!outside.isEmpty)
          (ComponentBoundaryContinuation.program (AdjacentExposureController.program (d-1)) true decorated.rootRecord.1) (ComponentBoundaryContinuation.initial (AdjacentExposureController.program (d-1)) true decorated.rootRecord.1 (.first .start)))
        (.first .start) (MultiSourcePacketPrefix.attached saved tree outside global)
        (.second (some ⟨tree.rootRecord.1,finalComponent.tree.rootRecord.1,.second entryBits (finalBits,.ready (.second lowId (ComponentObserverCompiler.ready
          (BoundaryReadController.activeResult Prod.fst color (lowId,low) (highId,high)
            (terminalId,(terminalLeaf d).rootRecord) d taggedHead taggedTail) lowId)))⟩) (some .done))
        target reads cost ∧
      (Source.fork (lowId,low) taggedHead
        (.fork (highId,high) (.leaf d (terminalId,(terminalLeaf d).rootRecord)) taggedTail)).inventory Prod.fst =
        decorated.inventory Prod.fst ∧
      (Source.fork (lowId,low) taggedHead
        (.fork (highId,high) (.leaf d (terminalId,(terminalLeaf d).rootRecord)) taggedTail)).shape.leaves =
        decorated.shape.leaves ∧
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
        (EnclosingPacketOperation.output saved tree.rootRecord.1 ⟨finalComponent.tree,outside⟩) target ∧
      target.tree.inventory Prod.fst = global.tree.inventory Prod.fst ∧
      CanonicalComponentUniqueness.Valid markerId target.tree ∧
      markerId ∉ target.tree.inventory Prod.fst ∧ MultiSourceProgram.WellFormed target ∧
      target.tree.inorderLabels Prod.fst = global.tree.inorderLabels Prod.fst ∧
      (∀ extra : G, MultiSourceProgram.fingerLabel Prod.fst target (.inr extra) =
        MultiSourceProgram.fingerLabel Prod.fst global (.inr extra)) ∧
      cost ≤ 2*(474240*(80220*Nat.clog 2 ((LocalReferences.depthReference reference).height+1)+4)+87360)+21 := by
  obtain ⟨left,right,low,high,lowId,highId,terminalId,taggedHead,taggedTail,finalForest,finalConfig,bodyReads,bodyCost,
    lowKey,highKey,leftClean,leftMarked,rightClean,rightMarked,splitWitness,headEq,tailEq,body,ids,sourceLeaves,finalRep,finalUnique,finalAssembly,presence,_,bound⟩ :=
    active_labels reference preferences d terminal lower upper component represented color decorated erases logicalUnique
      forest forestRep physicalUnique headerKey payload config assembled
  let firstPieces := representation none wingOrientation headerKey payload forest
  let finalPieces := representation none wingOrientation headerKey payload finalForest
  obtain ⟨firstHeader,firstPresent⟩ := virtual_present_root none wingOrientation headerKey payload forest
  obtain ⟨finalHeader,finalPresent⟩ := virtual_present_root none wingOrientation headerKey payload finalForest
  have firstCanonical : config = configuration firstPieces ⟨firstHeader,[]⟩ :=
    Option.some.inj (assembled.symm.trans (assemble_configuration firstPieces ⟨firstHeader,[]⟩ firstPresent))
  have finalCanonical : finalConfig = configuration finalPieces ⟨finalHeader,[]⟩ :=
    Option.some.inj (finalAssembly.symm.trans (assemble_configuration finalPieces ⟨finalHeader,[]⟩ finalPresent))
  rw [firstCanonical] at body treeErases
  obtain ⟨finalComponent,entryBits,finalBits,target,reads,cost,actual,componentErases,returned,globalIds,
    finalPhysical,finalReserved,finalValid,order,anchors,bounded⟩ :=
    ReenteredComponentExecution.execute markerId entry firstPieces finalPieces firstHeader finalHeader
      (LocalComponentCompiler.representation_root color decorated forest forestRep none wingOrientation headerKey payload)
      _ body tree treeErases outside global entryRep wellFormed physical reserved saved finalCanonical presence
  exact ⟨left,right,low,high,lowId,highId,terminalId,taggedHead,taggedTail,finalForest,finalConfig,finalComponent,entryBits,finalBits,target,reads,cost,
    lowKey,highKey,leftClean,leftMarked,rightClean,rightMarked,splitWitness,headEq,tailEq,actual,ids,sourceLeaves,finalRep,finalUnique,finalAssembly,presence,componentErases,returned,
    globalIds,finalPhysical,finalReserved,finalValid,order,anchors,by omega⟩

theorem sentinel_reentered (markerId : ι) {a b : Nat} (reference : DepthTree a b) (preferences : DepthSplit → Bool)
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
    (tree : Source β (ReentryCell ι η))
    (treeErases : tree.mapRecords Prod.snd = config.tree)
    (outside : List (Frame β (ReentryCell ι η)))
    (global : MultiSourceProgram.Configuration (Sum (Option Bool) G) β (ReentryCell ι η))
    (wellFormed : MultiSourceProgram.WellFormed global)
    (physical : CanonicalComponentUniqueness.Valid markerId global.tree)
    (reserved : markerId ∉ global.tree.inventory Prod.fst)
    (entry : Sum (Option Bool) G)
    (entryRep : MultiSourceSingleCursor.Represents entry ⟨tree,outside⟩ global)
    (saved : List (Option (Datum ι η))) :
    ∃ (right : AuxiliaryComponent Nat Nat (Tagged Payload)) (high : Cached),
      ∃ highId terminalId, ∃ taggedTail : Source Nat (η × Cached), ∃ finalForest finalConfig,
      ∃ (finalComponent : MultiSourceProgram.Configuration (Option Bool) β (ReentryCell ι η)), ∃ entryBits finalBits target reads cost,
      high.2.1 = d ∧ Clean right.core ∧ MarkedPorts right ∧
      PreparedSplitWitnesses.Sentinel component d right high ∧ taggedTail.mapRecords Prod.snd = right.tree ∧
      MultiSourceProgram.Run
        (ReenteredComponentExecution.program entry
          (representation none wingOrientation headerKey payload forest (some true)).isSome
          (representation none wingOrientation headerKey payload forest (some false)).isSome saved.length
          (headerPath (representation none wingOrientation headerKey payload forest)).length (!outside.isEmpty)
          (ComponentBoundaryContinuation.program (OpenSplitController.program d) false decorated.rootRecord.1) (ComponentBoundaryContinuation.initial (OpenSplitController.program d) false decorated.rootRecord.1 .start))
        (.first .start) (MultiSourcePacketPrefix.attached saved tree outside global)
        (.second (some ⟨tree.rootRecord.1,finalComponent.tree.rootRecord.1,.second entryBits (finalBits,.ready (.second highId (ComponentObserverCompiler.ready
          (BoundaryReadController.sentinelResult Prod.fst color (highId,high)
            (terminalId,(terminalLeaf d).rootRecord) d taggedTail) highId)))⟩) (some .done))
        target reads cost ∧
      (Source.fork (highId,high) (.leaf d (terminalId,(terminalLeaf d).rootRecord)) taggedTail).inventory Prod.fst =
        decorated.inventory Prod.fst ∧
      (Source.fork (highId,high) (.leaf d (terminalId,(terminalLeaf d).rootRecord)) taggedTail).shape.leaves =
        decorated.shape.leaves ∧
      ProjectionForest.Represents color
        ⟨annotate Prod.fst color none (.fork (highId,high) (.leaf d (terminalId,(terminalLeaf d).rootRecord)) taggedTail),[]⟩ (erase finalForest) ∧
      Unique finalForest ∧
      ForestConnector.assemble (representation none wingOrientation headerKey payload finalForest)
        (layout (representation none wingOrientation headerKey payload finalForest)) = some finalConfig ∧
      (∀ q, (representation none wingOrientation headerKey payload finalForest q).isSome =
        (representation none wingOrientation headerKey payload forest q).isSome) ∧
      finalComponent.mapRecords Prod.snd = finalConfig ∧
      MultiSourceSingleCursor.Represents (.inl none)
        (EnclosingPacketOperation.output saved tree.rootRecord.1 ⟨finalComponent.tree,outside⟩) target ∧
      target.tree.inventory Prod.fst = global.tree.inventory Prod.fst ∧
      CanonicalComponentUniqueness.Valid markerId target.tree ∧
      markerId ∉ target.tree.inventory Prod.fst ∧ MultiSourceProgram.WellFormed target ∧
      target.tree.inorderLabels Prod.fst = global.tree.inorderLabels Prod.fst ∧
      (∀ extra : G, MultiSourceProgram.fingerLabel Prod.fst target (.inr extra) =
        MultiSourceProgram.fingerLabel Prod.fst global (.inr extra)) ∧
      cost ≤ 2*(474240*(40110*Nat.clog 2 ((LocalReferences.depthReference reference).height+1)+2)+49920)+21 := by
  obtain ⟨right,high,highId,terminalId,taggedTail,finalForest,finalConfig,bodyReads,bodyCost,
    highKey,rightClean,rightMarked,splitWitness,tailEq,body,ids,sourceLeaves,finalRep,finalUnique,finalAssembly,presence,_,bound⟩ :=
    sentinel_labels reference preferences d valid terminal upper component represented color decorated erases logicalUnique
      forest forestRep physicalUnique headerKey payload config assembled
  let firstPieces := representation none wingOrientation headerKey payload forest
  let finalPieces := representation none wingOrientation headerKey payload finalForest
  obtain ⟨firstHeader,firstPresent⟩ := virtual_present_root none wingOrientation headerKey payload forest
  obtain ⟨finalHeader,finalPresent⟩ := virtual_present_root none wingOrientation headerKey payload finalForest
  have firstCanonical : config = configuration firstPieces ⟨firstHeader,[]⟩ :=
    Option.some.inj (assembled.symm.trans (assemble_configuration firstPieces ⟨firstHeader,[]⟩ firstPresent))
  have finalCanonical : finalConfig = configuration finalPieces ⟨finalHeader,[]⟩ :=
    Option.some.inj (finalAssembly.symm.trans (assemble_configuration finalPieces ⟨finalHeader,[]⟩ finalPresent))
  rw [firstCanonical] at body treeErases
  obtain ⟨finalComponent,entryBits,finalBits,target,reads,cost,actual,componentErases,returned,globalIds,
    finalPhysical,finalReserved,finalValid,order,anchors,bounded⟩ :=
    ReenteredComponentExecution.execute markerId entry firstPieces finalPieces firstHeader finalHeader
      (LocalComponentCompiler.representation_root color decorated forest forestRep none wingOrientation headerKey payload)
      _ body tree treeErases outside global entryRep wellFormed physical reserved saved finalCanonical presence
  exact ⟨right,high,highId,terminalId,taggedTail,finalForest,finalConfig,finalComponent,entryBits,finalBits,target,reads,cost,
    highKey,rightClean,rightMarked,splitWitness,tailEq,actual,ids,sourceLeaves,finalRep,finalUnique,finalAssembly,presence,componentErases,returned,
    globalIds,finalPhysical,finalReserved,finalValid,order,anchors,by omega⟩

end TangoSquared.Paper20261030.SecondaryDecomposition.ObservedPreparedExposure
