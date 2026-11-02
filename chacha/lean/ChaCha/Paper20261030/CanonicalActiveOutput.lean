import ChaCha.Paper20261030.CanonicalRepairedActive
import ChaCha.Paper20261030.CanonicalComponentReconstruction
import ChaCha.Paper20261030.CanonicalComponentUniqueness

set_option autoImplicit false

/-! Reassembling a canonical active forest while retaining the semantic
predicate of every attached component. In particular the boundary port
can carry the already reconstructed dormant component. -/

namespace ChaCha.Paper20261030.CanonicalActiveOutput

open ColoredStorage SourcePointer Structural PhysicalPacketStaging PhysicalForestMetadata
open CanonicalPacketLayerViews LocalComponentCompiler RepairedPayloadLayouts

variable {α β ρ ι : Type*} [DecidableEq α]

local instance : LinearOrder (Option Bool) := inferInstanceAs (LinearOrder (WithBot Bool))

def payload (left right : α → Source β (Packet α ρ ι)) (bottom : Source β (Packet α ρ ι)) :
    Option Bool → α → Source β (Packet α ρ ι)
  | some true => left
  | some false => right
  | none => fun _ => bottom

theorem reconstruct (color : α → Option Bool) (logical : Source α ρ)
    (virtual : Option (Tagged α ρ ι)) (virtualPacking : virtual.map (Source.mapRecords Prod.snd) = packed color none logical)
    (good : Bool → α → Source β (Packet α ρ ι) → Prop)
    (headerKey : α) (bottom target : Source β (Packet α ρ ι))
    (result : CanonicalRepairedActive.Result good (packed color (some true) logical) (packed color (some false) logical)
      (CanonicalComponentReconstruction.header virtual) bottom (some target)) :
    ∃ (forest : TaggedForest (Option Bool) α ρ ι)
      (payload : Option Bool → α → Source β (Packet α ρ ι))
      (config : MultiSourceProgram.Configuration (Option Bool) β (Packet α ρ ι)),
      ProjectionForest.Represents color ⟨logical,[]⟩ (erase forest) ∧
      ForestConnector.assemble (ComponentPhysicalRepair.view none wingOrientation headerKey payload (encode forest))
        (ForestConnector.ThreeColors.layout (ComponentPhysicalRepair.view none wingOrientation headerKey payload (encode forest))) = some config ∧
      target = config.tree ∧ payload none headerKey = bottom ∧
      (∀ side key, key ∈ ports (packed color (some side) logical) → good side key (payload (some side) key)) := by
  obtain ⟨left,right,lp,rp,leftErases,rightErases,leftGood,rightGood,view⟩ := result
  obtain ⟨config,assembly,assembledView⟩ := CanonicalComponentReconstruction.assembled left virtual right headerKey (payload lp rp bottom)
  refine ⟨CanonicalComponentReconstruction.forest left virtual right,payload lp rp bottom,config,?_,assembly,?_,rfl,?_⟩
  · exact CanonicalComponentReconstruction.represents color logical left virtual right leftErases virtualPacking rightErases
  · exact Option.some.inj (view.trans assembledView.symm)
  · intro side key member
    cases side with
    | false => exact rightGood key member
    | true => exact leftGood key member

/-- The actual physical endpoint supplies uniqueness of the rebuilt real
pieces. Only the virtual witness needs its separate local-id certificate. -/
theorem reconstruct_unique (markerId : ι) (color : α → Option Bool) (logical : Source α ρ)
    (virtual : Option (Tagged α ρ ι)) (virtualPacking : virtual.map (Source.mapRecords Prod.snd) = packed color none logical)
    (virtualUnique : ∀ tree, virtual = some tree → (tree.inventory Prod.fst).Nodup)
    (good : Bool → α → Source β (Packet α ρ ι) → Prop)
    (headerKey : α) (bottom : Source β (Packet α ρ ι))
    (target : Source β (PacketLayers.Context.Cell α ρ ι))
    (valid : CanonicalComponentUniqueness.Valid markerId target)
    (result : CanonicalRepairedActive.Result good (packed color (some true) logical) (packed color (some false) logical)
      (CanonicalComponentReconstruction.header virtual) bottom (some (target.mapRecords Prod.snd))) :
    ∃ (forest : TaggedForest (Option Bool) α ρ ι)
      (payload : Option Bool → α → Source β (Packet α ρ ι))
      (config : MultiSourceProgram.Configuration (Option Bool) β (Packet α ρ ι)),
      ProjectionForest.Represents color ⟨logical,[]⟩ (erase forest) ∧ Unique forest ∧
      ForestConnector.assemble (ComponentPhysicalRepair.view none wingOrientation headerKey payload (encode forest))
        (ForestConnector.ThreeColors.layout (ComponentPhysicalRepair.view none wingOrientation headerKey payload (encode forest))) = some config ∧
      target.mapRecords Prod.snd = config.tree ∧ payload none headerKey = bottom ∧
      (∀ side key, key ∈ ports (packed color (some side) logical) → good side key (payload (some side) key)) := by
  obtain ⟨left,right,lp,rp,leftErases,rightErases,leftGood,rightGood,view⟩ := result
  obtain ⟨config,assembly,assembledView⟩ := CanonicalComponentReconstruction.assembled left virtual right headerKey (payload lp rp bottom)
  have realized := CanonicalComponentUniqueness.of_source markerId target valid
  rw [view] at realized
  have unique := CanonicalComponentUniqueness.forest markerId lp rp left virtual right
    (CanonicalComponentReconstruction.header virtual) bottom realized virtualUnique
  refine ⟨CanonicalComponentReconstruction.forest left virtual right,payload lp rp bottom,config,?_,unique,assembly,?_,rfl,?_⟩
  · exact CanonicalComponentReconstruction.represents color logical left virtual right leftErases virtualPacking rightErases
  · exact Option.some.inj (view.trans assembledView.symm)
  · intro side key member
    cases side with
    | false => exact rightGood key member
    | true => exact leftGood key member

end ChaCha.Paper20261030.CanonicalActiveOutput
