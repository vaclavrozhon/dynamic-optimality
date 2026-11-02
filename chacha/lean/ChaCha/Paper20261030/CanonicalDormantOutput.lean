import ChaCha.Paper20261030.CanonicalComponentReconstruction
import ChaCha.Paper20261030.CanonicalComponentUniqueness

set_option autoImplicit false

/-!
# The repaired dormant component satisfies the maintained forest invariant

This endpoint theorem combines the finite mixed-layout proof with the
existing three-color component representation and its actual assembly.
The virtual witness is the tagged tree supplied by the checked bounded
header encoder. Its root remains a stored cursor, not a new physical
vertex. The real tagged projections use identifiers reached by the
reassembly and repair.
-/

namespace ChaCha.Paper20261030.CanonicalDormantOutput

open ColoredStorage SourcePointer Structural PhysicalPacketStaging PhysicalForestMetadata PacketLayers
open CanonicalPacketLayerViews MixedPacketRepair LocalComponentCompiler

variable {α β ρ ι η : Type*} [DecidableEq α]

local instance : LinearOrder (Option Bool) := inferInstanceAs (LinearOrder (WithBot Bool))

abbrev Logical (ρ η : Type*) := HeadBoundary.Record ρ η (Option Bool)

theorem reconstruct (markerId : ι) (blocks : Fin 8 → Source β (Packet α (Logical ρ η) ι))
    (payload : Option Bool → α → Source β (Packet α (Logical ρ η) ι))
    (bits : Fin 8 → Bool) (l b r : Fin 8) (high : Logical ρ η)
    (leftPlain rightPlain : ProjectionLocal.Projected α (Logical ρ η))
    (leftRep : CanonicalRepairedRouting.Layout markerId blocks (payload (some true)) false leftPlain
      (HeadPacketRepair.block bits l) (HeadPacketLayout.block bits l))
    (rightRep : CanonicalRepairedRouting.Layout markerId blocks (payload (some false)) true rightPlain
      (HeadPacketRepair.block bits r) (HeadPacketLayout.block bits r))
    (color : α → Option Bool) (logical : Source α (Logical ρ η))
    (virtual : Option (Tagged α (Logical ρ η) ι))
    (leftPacking : packed color (some true) logical = ProjectionLocal.decorate (ObservedHeadBlueprint.owned (some true) high) leftPlain)
    (rightPacking : packed color (some false) logical = ProjectionLocal.decorate (ObservedHeadBlueprint.owned (some false) high) rightPlain)
    (virtualPacking : virtual.map (Source.mapRecords Prod.snd) = packed color none logical)
    (headerKey : α) (bottom : payload none headerKey = blocks b)
    (plan : Source (Fin 8) Layers) (context : Source (Fin 8) (Expression α (Logical ρ η) ι))
    (planFound : HeadPacketRepair.dormant bits l b r (CanonicalComponentReconstruction.header virtual).length = some plan)
    (contextFound : HeadPacketLayout.dormant markerId bits l b r high (CanonicalComponentReconstruction.header virtual) = some context)
    (source : Source β (Cell α (Logical ρ η) ι)) (repacked : Reached.Repacked blocks context source)
    (aligned : SourceRecordPredicate.Holds (PacketAlignment.Predicate markerId) source) :
    ∃ (forest : TaggedForest (Option Bool) α (Logical ρ η) ι)
      (config : MultiSourceProgram.Configuration (Option Bool) β (Packet α (Logical ρ η) ι)),
      ProjectionForest.Represents color ⟨logical,[]⟩ (erase forest) ∧
      ForestConnector.assemble (ComponentPhysicalRepair.view none wingOrientation headerKey payload (encode forest))
        (ForestConnector.ThreeColors.layout (ComponentPhysicalRepair.view none wingOrientation headerKey payload (encode forest))) = some config ∧
      (output plan none source).mapRecords Prod.snd = config.tree := by
  have represented := CanonicalRepairedDormant.represents markerId blocks (payload (some true)) (payload (some false))
    bits l b r high (CanonicalComponentReconstruction.header virtual) leftPlain rightPlain leftRep rightRep
  rw [planFound,contextFound] at represented
  obtain ⟨left,right,leftErases,rightErases,outputView⟩ := represented.2 source repacked aligned
  obtain ⟨config,assembly,view⟩ := CanonicalComponentReconstruction.assembled left virtual right headerKey payload
  refine ⟨CanonicalComponentReconstruction.forest left virtual right,config,?_,assembly,?_⟩
  · exact CanonicalComponentReconstruction.represents color logical left virtual right
      (leftErases.trans leftPacking.symm) virtualPacking (rightErases.trans rightPacking.symm)
  · rw [bottom] at view
    exact Option.some.inj (outputView.trans view.symm)

/-- Reconstructing from the canonical result also recovers the physical
forest uniqueness required by the next secondary operation. -/
theorem reconstruct_unique (markerId : ι) (color : α → Option Bool) (logical : Source α ρ)
    (virtual : Option (Tagged α ρ ι)) (virtualPacking : virtual.map (Source.mapRecords Prod.snd) = packed color none logical)
    (virtualUnique : ∀ tree, virtual = some tree → (tree.inventory Prod.fst).Nodup)
    (headerKey : α) (payload : Option Bool → α → Source β (Packet α ρ ι))
    (target : Source β (Context.Cell α ρ ι))
    (valid : CanonicalComponentUniqueness.Valid markerId target)
    (result : CanonicalRepairedDormant.Result (payload (some true)) (payload (some false))
      (packed color (some true) logical) (packed color (some false) logical)
      (CanonicalComponentReconstruction.header virtual) (payload none headerKey) (some (target.mapRecords Prod.snd))) :
    ∃ (forest : TaggedForest (Option Bool) α ρ ι)
      (config : MultiSourceProgram.Configuration (Option Bool) β (Packet α ρ ι)),
      ProjectionForest.Represents color ⟨logical,[]⟩ (erase forest) ∧ Unique forest ∧
      ForestConnector.assemble (ComponentPhysicalRepair.view none wingOrientation headerKey payload (encode forest))
        (ForestConnector.ThreeColors.layout (ComponentPhysicalRepair.view none wingOrientation headerKey payload (encode forest))) = some config ∧
      target.mapRecords Prod.snd = config.tree := by
  obtain ⟨left,right,leftErases,rightErases,view⟩ := result
  obtain ⟨config,assembly,assembledView⟩ := CanonicalComponentReconstruction.assembled left virtual right headerKey payload
  have realized := CanonicalComponentUniqueness.of_source markerId target valid
  rw [view] at realized
  have unique := CanonicalComponentUniqueness.forest markerId (payload (some true)) (payload (some false)) left virtual right
    (CanonicalComponentReconstruction.header virtual) (payload none headerKey) realized virtualUnique
  refine ⟨CanonicalComponentReconstruction.forest left virtual right,config,?_,unique,assembly,?_⟩
  · exact CanonicalComponentReconstruction.represents color logical left virtual right leftErases virtualPacking rightErases
  · exact Option.some.inj (view.trans assembledView.symm)

end ChaCha.Paper20261030.CanonicalDormantOutput
