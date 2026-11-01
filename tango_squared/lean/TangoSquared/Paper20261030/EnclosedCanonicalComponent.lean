import TangoSquared.Paper20261030.EnclosedComponentAlignment
import TangoSquared.Paper20261030.ComponentVirtualRoot

set_option autoImplicit false

/-! A canonical assembled component run, including a composed observer,
can execute inside the enclosing physical tree. Its initial wing bits
determine the return route; preserved presence proves this route valid. -/

namespace TangoSquared.Paper20261030.EnclosedComponentExecution

open ColoredStorage SourcePointer MultiSourceProgram PhysicalPacketStaging PacketLayers
open ForestConnector.ThreeColors

variable {α β ρ ι G σ : Type*} [DecidableEq G] [DecidableEq ι]

theorem canonical_aligned (markerId : ι) (source : Program σ (Option Bool) (Packet α ρ ι))
    {initial last : σ} {before after : Configuration (Option Bool) β (Packet α ρ ι)} {reads cost}
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
    (firstForest finalForest : ProjectionForest.State (Option Bool) β (Option (Datum α ρ ι)))
    (header : Source β (Packet α ρ ι)) (present : finalForest none = some ⟨header,[]⟩)
    (assembled : ForestConnector.assemble finalForest (layout finalForest) = some after)
    (presence : ∀ q, (finalForest q).isSome = (firstForest q).isSome) :
    ∃ (finalComponent : Configuration (Option Bool) β (Context.Cell α ρ ι)), ∃ target observed total,
      Run (program entry saved.length (headerPath firstForest).length (!outside.isEmpty) source initial) (.first .start)
        (MultiSourcePacketPrefix.attached saved component.tree outside global)
        (.second (some ⟨component.tree.rootRecord.1,finalComponent.tree.rootRecord.1,.ready last⟩) (some .done))
        target observed total ∧
      finalComponent.mapRecords Prod.snd = after ∧
      MultiSourceSingleCursor.Represents (.inl none)
        (EnclosingPacketOperation.output saved component.tree.rootRecord.1 ⟨finalComponent.tree,outside⟩) target ∧
      target.tree.inventory Prod.fst = global.tree.inventory Prod.fst ∧
      CanonicalComponentUniqueness.Valid markerId target.tree ∧
      markerId ∉ target.tree.inventory Prod.fst ∧ WellFormed target ∧ total ≤ 2*cost+13 := by
  have canonical : after = configuration finalForest ⟨header,[]⟩ :=
    Option.some.inj (assembled.symm.trans (assemble_configuration finalForest ⟨header,[]⟩ present))
  have samePath : headerPath finalForest = headerPath firstForest := by
    exact congrArg₂ (fun (right left : Bool) =>
      (if right then [false] else []) ++ (if left then [true] else []))
      (presence (some false)) (presence (some true))
  exact execute_aligned markerId source run component erases outside global represented valid physical reserved
    entry entryRep saved finalForest header canonical (headerPath firstForest).length
    (congrArg List.length samePath.symm)

end TangoSquared.Paper20261030.EnclosedComponentExecution
