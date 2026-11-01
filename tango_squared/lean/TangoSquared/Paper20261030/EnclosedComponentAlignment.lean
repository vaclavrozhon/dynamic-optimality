import TangoSquared.Paper20261030.PacketWriteLabels
import TangoSquared.Paper20261030.EnclosedComponentExecution
import TangoSquared.Paper20261030.MultiSourceEnclosingOperation
import TangoSquared.Paper20261030.NestedComponentReturn

set_option autoImplicit false

/-! A nested component controller preserving physical packet labels
also preserves global packet/id agreement and marker freedom. The
original prefix/parent wrapper is reused with the same cost bound. -/

namespace TangoSquared.Paper20261030.EnclosedComponentExecution

open ColoredStorage SourcePointer MultiSourceProgram PhysicalPacketStaging PacketLayers
open ForestConnector.ThreeColors

variable {α β ρ ι G σ : Type*} [DecidableEq G] [DecidableEq ι]

theorem execute_aligned (markerId : ι) (source : Program σ (Option Bool) (Packet α ρ ι)) {initial last : σ}
    {before after : Configuration (Option Bool) β (Packet α ρ ι)} {reads cost}
    (run : MultiSourceWriteLabels.Run (List.map PacketWriteLabels.label) source initial before last after reads cost)
    (component : Configuration (Option Bool) β (Context.Cell α ρ ι))
    (erases : component.mapRecords Prod.snd = before)
    (outside : List (Frame β (Context.Cell α ρ ι)))
    (global : Configuration (Sum (Option Bool) G) β (Context.Cell α ρ ι))
    (represented : MultiSourceRegisterExtension.project global = component.extend outside)
    (valid : WellFormed global) (physical : CanonicalComponentUniqueness.Valid markerId global.tree)
    (reserved : markerId ∉ global.tree.inventory Prod.fst)
    (entry : Sum (Option Bool) G)
    (entryRep : MultiSourceSingleCursor.Represents entry ⟨component.tree,outside⟩ global)
    (saved : Packet α ρ ι)
    (forest : ProjectionForest.State (Option Bool) β (Option (Datum α ρ ι)))
    (header : Source β (Packet α ρ ι))
    (assembled : after = configuration forest ⟨header,[]⟩)
    (levels : Nat) (knownReturn : levels = (headerPath forest).length) :
    ∃ (finalComponent : Configuration (Option Bool) β (Context.Cell α ρ ι)), ∃ target observed total,
      Run (program entry saved.length levels (!outside.isEmpty) source initial) (.first .start)
        (MultiSourcePacketPrefix.attached saved component.tree outside global)
        (.second (some ⟨component.tree.rootRecord.1,finalComponent.tree.rootRecord.1,.ready last⟩) (some .done))
        target observed total ∧
      finalComponent.mapRecords Prod.snd = after ∧
      MultiSourceSingleCursor.Represents (.inl none)
        (EnclosingPacketOperation.output saved component.tree.rootRecord.1 ⟨finalComponent.tree,outside⟩) target ∧
      target.tree.inventory Prod.fst = global.tree.inventory Prod.fst ∧
      CanonicalComponentUniqueness.Valid markerId target.tree ∧
      markerId ∉ target.tree.inventory Prod.fst ∧ WellFormed target ∧ total ≤ 2*cost+13 := by
  obtain ⟨finalComponent,middle,bodyReads,bodyCost,body,finalErases,finalRep,middleTree,ids,middleInvariant,middleValid,bound⟩ :=
    MultiSourceNestedImmutable.execute_predicate (List.map PacketWriteLabels.label)
      (PacketWriteLabels.Relation markerId) source run component erases outside global represented valid
      ((PacketWriteLabels.holds_iff markerId global.tree).mpr ⟨physical.1,physical.2.1⟩)
  obtain ⟨focus,inside,returned,rootEq,length,short⟩ := NestedComponentReturn.header forest header
    finalComponent (finalErases.trans assembled) outside middle finalRep
  have finalUnique : (middle.tree.inventory Prod.fst).Nodup := ids ▸ physical.2.2
  have inputValid := MultiSourcePacketPrefix.attached_wellFormed saved component.tree outside global entryRep.1 valid
  obtain ⟨target,observed,total,actual,targetRep,finalIds,finalValid,bounded⟩ :=
    MultiSourceEnclosingOperation.execute entry (fun _ => .inl none) saved
      (MultiSourceNestedImmutable.program source) (.ready initial) (.ready last) global middle body
      component.tree focus outside inside outside entryRep returned finalUnique inputValid
  rw [rootEq] at actual targetRep
  have levelEq : inside.length = levels := length.trans knownReturn.symm
  rw [levelEq] at actual
  have barePhysical : CanonicalComponentUniqueness.Valid markerId (plug finalComponent.tree outside) := by
    rw [← middleTree]
    obtain ⟨aligned,clear⟩ := (PacketWriteLabels.holds_iff markerId middle.tree).mp middleInvariant
    exact ⟨aligned,clear,finalUnique⟩
  have bareReserved : markerId ∉ (plug finalComponent.tree outside).inventory Prod.fst := by
    rw [← middleTree,ids]
    exact reserved
  obtain ⟨outputPhysical,outputReserved⟩ := EnclosingPacketOperation.valid markerId saved
    component.tree.rootRecord.1 ⟨finalComponent.tree,outside⟩ bareReserved barePhysical
  refine ⟨finalComponent,target,observed,total,actual,finalErases,targetRep,
    finalIds.trans ids,?_,?_,finalValid,by omega⟩
  · rw [targetRep.1]
    exact outputPhysical
  · rw [targetRep.1]
    exact outputReserved

end TangoSquared.Paper20261030.EnclosedComponentExecution
