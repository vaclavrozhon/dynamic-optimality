import TangoSquared.Paper20261030.ReenteredObservedPreparation
import TangoSquared.Paper20261030.CanonicalRetainedPayloadHandoff

set_option autoImplicit false

/-! Actual active preparation returns the parked incoming component.
The representation supplies the outgoing depth payload in the prepared
forest. Its complete physical metadata is unchanged after removing its
new enclosing root packet, and its original extra finger is still at its
root. The next incoming operation can therefore use that finger directly. -/

namespace TangoSquared.Paper20261030.SecondaryDecomposition.ObservedPreparedExposure

open ColoredStorage SourcePointer Structural PhysicalForestMetadata Auxiliary AuxiliaryComponent BoundaryObservations PathDecomposition
open LocalComponentForestCompiler LocalComponentCompiler ForestConnector.ThreeColors
open PreparedExposureExecution (Logical Datum)

variable {β ι η G : Type*} [DecidableEq ι] [DecidableEq η] [DecidableEq G]

local instance preparedHandoffColorOrder : LinearOrder (Option Bool) := inferInstanceAs (LinearOrder (WithBot Bool))

theorem active_handoff (markerId : ι) {a b : Nat} (reference : DepthTree a b) (preferences : DepthSplit → Bool)
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
    (saved : List (Option (Datum ι η)))
    (anchor : G) (incoming : Cursor β (ReentryCell ι η))
    (incomingRep : MultiSourceSingleCursor.Represents (.inr anchor) incoming global)
    (incomingPayload : CanonicalRetainedPayloadHandoff.PayloadAt (payload (color d) d) incoming)
    (real : color d ≠ none) (distinct : global.tree.shape.leaves.Nodup) :
    ∃ (left right : AuxiliaryComponent Nat Nat (Tagged Payload)) (low high : Cached),
      ∃ lowId highId terminalId, ∃ taggedHead taggedTail : Source Nat (η × Cached), ∃ finalForest finalConfig,
      ∃ (finalComponent : MultiSourceProgram.Configuration (Option Bool) β (ReentryCell ι η)), ∃ entryBits finalBits target reads cost, ∃ incomingTarget : Cursor β (ReentryCell ι η),
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
      MultiSourceSingleCursor.Represents (.inr anchor) incomingTarget target ∧
      CanonicalRetainedPayloadHandoff.PayloadAt (payload (color d) d) incomingTarget ∧
      incomingTarget.focus.rootRecord.1 ≠ finalComponent.tree.rootRecord.1 ∧ incomingTarget.ancestors ≠ [] ∧
      (∃ packet : List (Option (Datum ι η)), packet.length = 2 ∧ incomingTarget.focus.mapRecords Prod.snd =
        (payload (color d) d).setRoot (packet ++ (payload (color d) d).rootRecord)) ∧
      (SubtreeMetadata.replacePayload incoming (payload (color d) d).rootRecord).focus =
        (SubtreeMetadata.replacePayload incomingTarget (payload (color d) d).rootRecord).focus ∧
      cost ≤ 2*(474240*(80220*Nat.clog 2 ((LocalReferences.depthReference reference).height+1)+4)+87360)+21 := by
  obtain ⟨left,right,low,high,lowId,highId,terminalId,taggedHead,taggedTail,finalForest,finalConfig,finalComponent,
    entryBits,finalBits,target,reads,cost,lowKey,highKey,leftClean,leftMarked,rightClean,rightMarked,splitWitness,headEq,tailEq,
    actual,ids,sourceLeaves,finalRep,finalUnique,finalAssembly,presence,componentErases,returned,globalIds,
    finalPhysical,finalReserved,finalValid,order,anchors,bound⟩ :=
    active_reentered markerId reference preferences d terminal lower upper component represented color decorated erases logicalUnique
      forest forestRep physicalUnique headerKey payload config assembled tree treeErases outside global wellFormed physical reserved entry entryRep saved
  have attachedLeaves : (MultiSourcePacketPrefix.attached saved tree outside global).tree.shape.leaves = global.tree.shape.leaves := by
    rw [entryRep.1]
    exact (SourcePointer.Step.write tree (tree.rootRecord.1,saved++tree.rootRecord.2) outside).leaves.symm
  have leafWord : global.tree.shape.leaves = target.tree.shape.leaves := by
    have same := actual.leaves
    rw [attachedLeaves] at same
    exact same
  have componentTree : finalComponent.tree.mapRecords Prod.snd = finalConfig.tree :=
    congrArg MultiSourceProgram.Configuration.tree componentErases
  obtain ⟨incomingTarget,positioned,payloadRep,differentRoots,incomingProper,attachment,samePayload⟩ := CanonicalRetainedPayloadHandoff.handoff color
    (.fork (lowId,low) taggedHead (.fork (highId,high) (.leaf d (terminalId,(terminalLeaf d).rootRecord)) taggedTail))
    finalForest finalRep headerKey payload finalConfig finalAssembly finalComponent.tree componentTree outside saved tree.rootRecord.1
    global target (.inl none) returned leafWord order distinct finalPhysical.2.2 (.inr anchor) (anchors anchor)
    incoming incomingRep d (by simp [Source.shape,RouterProjection.Router.leaves]) real incomingPayload
  exact ⟨left,right,low,high,lowId,highId,terminalId,taggedHead,taggedTail,finalForest,finalConfig,finalComponent,
    entryBits,finalBits,target,reads,cost,incomingTarget,lowKey,highKey,leftClean,leftMarked,rightClean,rightMarked,splitWitness,headEq,tailEq,
    actual,ids,sourceLeaves,finalRep,finalUnique,finalAssembly,presence,componentErases,returned,globalIds,
    finalPhysical,finalReserved,finalValid,order,anchors,positioned,payloadRep,differentRoots,incomingProper,attachment,samePayload,bound⟩

end TangoSquared.Paper20261030.SecondaryDecomposition.ObservedPreparedExposure
