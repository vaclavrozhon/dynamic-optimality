import TangoSquared.Paper20261030.MultiSourceNestedImmutable
import TangoSquared.Paper20261030.MultiSourceEnclosingOperation
import TangoSquared.Paper20261030.NestedComponentReturn

set_option autoImplicit false

/-!
# Actual execution of a nested component with enclosing packet repair

This combines immutable metadata, extra component anchors, unchanged
outer context, the return route supplied by the three-piece assembly,
and prefix/parent repair. A payload controller of cost c costs at most
2*c+13. Its final scalar state remains available to the continuation.

The enclosing-prefix length and return depth are scalar layout data.
The latter is determined by wing-presence bits, whose preservation is
proved by the rooted component compiler. This theorem does not establish
packet-id alignment for an arbitrary payload controller; that stronger
invariant still has to be proved for the component compiler itself.
-/

namespace TangoSquared.Paper20261030.EnclosedComponentExecution

open ColoredStorage SourcePointer MultiSourceProgram PhysicalPacketStaging PacketLayers
open ForestConnector.ThreeColors

variable {α β ρ ι G σ : Type*} [DecidableEq G] [DecidableEq ι]

def program (entry : Sum (Option Bool) G) (count levels : Nat) (hasParent : Bool)
    (source : Program σ (Option Bool) (Packet α ρ ι)) (initial : σ) :=
  MultiSourceEnclosingOperation.program entry (fun _ => .inl none) count levels hasParent
    (MultiSourceNestedImmutable.program source) (.ready initial)

theorem execute (source : Program σ (Option Bool) (Packet α ρ ι)) {initial last : σ}
    {before after : Configuration (Option Bool) β (Packet α ρ ι)} {reads cost}
    (run : Run source initial before last after reads cost)
    (component : Configuration (Option Bool) β (Context.Cell α ρ ι))
    (erases : component.mapRecords Prod.snd = before)
    (outside : List (Frame β (Context.Cell α ρ ι)))
    (global : Configuration (Sum (Option Bool) G) β (Context.Cell α ρ ι))
    (represented : MultiSourceRegisterExtension.project global = component.extend outside)
    (valid : WellFormed global) (unique : (global.tree.inventory Prod.fst).Nodup)
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
      WellFormed target ∧ total ≤ 2*cost+13 := by
  obtain ⟨finalComponent,middle,bodyReads,bodyCost,body,finalErases,finalRep,_,ids,middleValid,bound⟩ :=
    MultiSourceNestedImmutable.execute source run component erases outside global represented valid
  obtain ⟨focus,inside,returned,rootEq,length,short⟩ := NestedComponentReturn.header forest header
    finalComponent (finalErases.trans assembled) outside middle finalRep
  have finalUnique : (middle.tree.inventory Prod.fst).Nodup := ids ▸ unique
  have inputValid := MultiSourcePacketPrefix.attached_wellFormed saved component.tree outside global entryRep.1 valid
  obtain ⟨target,observed,total,actual,targetRep,finalIds,finalValid,bounded⟩ :=
    MultiSourceEnclosingOperation.execute entry (fun _ => .inl none) saved
      (MultiSourceNestedImmutable.program source) (.ready initial) (.ready last) global middle body
      component.tree focus outside inside outside entryRep returned finalUnique inputValid
  rw [rootEq] at actual targetRep
  have levelEq : inside.length = levels := length.trans knownReturn.symm
  rw [levelEq] at actual
  exact ⟨finalComponent,target,observed,total,actual,finalErases,targetRep,
    finalIds.trans ids,finalValid,by omega⟩

end TangoSquared.Paper20261030.EnclosedComponentExecution
