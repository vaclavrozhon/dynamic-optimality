import ChaCha.Paper20261030.ComputedVirtualHeaderReadiness
import ChaCha.Paper20261030.CanonicalComponentUniqueness
import ChaCha.Paper20261030.CanonicalRepairedActive

set_option autoImplicit false

/-! Rebuilding a maintained component from its actual repaired output.
The real routing trees come from the output predicate, and the virtual
tree comes from the computed header. Physical validity supplies uniqueness
of the real ids; the encoder supplies uniqueness of the virtual ids. -/

namespace ChaCha.Paper20261030.ComputedComponentReconstruction

open ColoredStorage SourcePointer Structural PhysicalForestMetadata PhysicalPacketStaging
open CanonicalPacketLayerViews LocalComponentCompiler RepairedPayloadLayouts

variable {α β ρ : Type*} [DecidableEq α]

local instance computedComponentReconstructionColorOrder : LinearOrder (Option Bool) :=
  inferInstanceAs (LinearOrder (WithBot Bool))

def payload (left right : α → Source β (Packet α ρ Nat)) (bottom : Source β (Packet α ρ Nat)) :
    Option Bool → α → Source β (Packet α ρ Nat)
  | none,_ => bottom
  | some true,key => left key
  | some false,key => right key

theorem pieces (markerId : Nat) (color : α → Option Bool) (source : Source α ρ)
    (left right : Option (Tagged α ρ Nat))
    (leftPacked : left.map (Source.mapRecords Prod.snd) = packed color (some true) source)
    (rightPacked : right.map (Source.mapRecords Prod.snd) = packed color (some false) source)
    (leftPayload rightPayload : α → Source β (Packet α ρ Nat)) (bottom : Source β (Packet α ρ Nat))
    (stored : VirtualHeaderController.Virtual α (PhysicalForestMetadata.Record ρ Nat))
    (ready : VirtualPhysicalPackets.Ready stored)
    (decoded : VirtualPhysicalPackets.decode stored = (packed color none source).map (fun tree => ⟨tree,[]⟩))
    (actual : Source β (PacketLayers.Context.Cell α ρ Nat))
    (valid : CanonicalComponentUniqueness.Valid markerId actual)
    (view : some (actual.mapRecords Prod.snd) =
      CanonicalRepairedDormant.view leftPayload rightPayload left right [some (.header stored),none] bottom)
    (headerKey : α) :
    ∃ forest config,
      ProjectionForest.Represents color ⟨source,[]⟩ (erase forest) ∧ Unique forest ∧
      ForestConnector.assemble
        (ComponentPhysicalRepair.view none wingOrientation headerKey (payload leftPayload rightPayload bottom) (encode forest))
        (ForestConnector.ThreeColors.layout
          (ComponentPhysicalRepair.view none wingOrientation headerKey (payload leftPayload rightPayload bottom) (encode forest))) = some config ∧
      config.tree = actual.mapRecords Prod.snd := by
  obtain ⟨virtual,encoded,virtualPacked,virtualUnique⟩ := VirtualPhysicalPackets.ready_erases stored ready _ decoded
  have represented := CanonicalComponentReconstruction.represents color source left virtual right leftPacked virtualPacked rightPacked
  have headerEq : ([some (.header stored),none] : Packet α ρ Nat) = CanonicalComponentReconstruction.header virtual := by
    rw [encoded]
    rfl
  rw [headerEq] at view
  have realized : CanonicalComponentUniqueness.Realized markerId
      (CanonicalRepairedDormant.view leftPayload rightPayload left right (CanonicalComponentReconstruction.header virtual) bottom) := by
    rw [← view]
    exact CanonicalComponentUniqueness.of_source markerId actual valid
  have unique := CanonicalComponentUniqueness.forest markerId leftPayload rightPayload left virtual right
    (CanonicalComponentReconstruction.header virtual) bottom realized virtualUnique
  obtain ⟨config,assembled,tree⟩ := CanonicalComponentReconstruction.assembled left virtual right headerKey
    (payload leftPayload rightPayload bottom)
  exact ⟨_,config,represented,unique,assembled,Option.some.inj (tree.trans view.symm)⟩

theorem active (markerId : Nat) (color : α → Option Bool) (source : Source α ρ)
    (good : Bool → α → Source β (Packet α ρ Nat) → Prop) (bottom : Source β (Packet α ρ Nat))
    (stored : VirtualHeaderController.Virtual α (PhysicalForestMetadata.Record ρ Nat))
    (ready : VirtualPhysicalPackets.Ready stored)
    (decoded : VirtualPhysicalPackets.decode stored = (packed color none source).map (fun tree => ⟨tree,[]⟩))
    (actual : Source β (PacketLayers.Context.Cell α ρ Nat))
    (valid : CanonicalComponentUniqueness.Valid markerId actual)
    (result : CanonicalRepairedActive.Result good (packed color (some true) source) (packed color (some false) source)
      [some (.header stored),none] bottom (some (actual.mapRecords Prod.snd))) (headerKey : α) :
    ∃ leftPayload rightPayload forest config,
      ProjectionForest.Represents color ⟨source,[]⟩ (erase forest) ∧ Unique forest ∧
      ForestConnector.assemble
        (ComponentPhysicalRepair.view none wingOrientation headerKey (payload leftPayload rightPayload bottom) (encode forest))
        (ForestConnector.ThreeColors.layout
          (ComponentPhysicalRepair.view none wingOrientation headerKey (payload leftPayload rightPayload bottom) (encode forest))) = some config ∧
      config.tree = actual.mapRecords Prod.snd ∧
      ∀ side key, key ∈ ports (packed color (some side) source) →
        good side key (payload leftPayload rightPayload bottom (some side) key) := by
  obtain ⟨left,right,leftPayload,rightPayload,leftPacked,rightPacked,leftGood,rightGood,view⟩ := result
  obtain ⟨forest,config,represented,unique,assembled,exactTree⟩ := pieces markerId color source left right leftPacked rightPacked
    leftPayload rightPayload bottom stored ready decoded actual valid view headerKey
  refine ⟨leftPayload,rightPayload,forest,config,represented,unique,assembled,exactTree,?_⟩
  intro side
  cases side
  · exact rightGood
  · exact leftGood

theorem dormant (markerId : Nat) (color : α → Option Bool) (source : Source α ρ)
    (leftPayload rightPayload : α → Source β (Packet α ρ Nat)) (bottom : Source β (Packet α ρ Nat))
    (stored : VirtualHeaderController.Virtual α (PhysicalForestMetadata.Record ρ Nat))
    (ready : VirtualPhysicalPackets.Ready stored)
    (decoded : VirtualPhysicalPackets.decode stored = (packed color none source).map (fun tree => ⟨tree,[]⟩))
    (actual : Source β (PacketLayers.Context.Cell α ρ Nat))
    (valid : CanonicalComponentUniqueness.Valid markerId actual)
    (result : CanonicalRepairedDormant.Result leftPayload rightPayload
      (packed color (some true) source) (packed color (some false) source)
      [some (.header stored),none] bottom (some (actual.mapRecords Prod.snd))) (headerKey : α) :
    ∃ forest config,
      ProjectionForest.Represents color ⟨source,[]⟩ (erase forest) ∧ Unique forest ∧
      ForestConnector.assemble
        (ComponentPhysicalRepair.view none wingOrientation headerKey (payload leftPayload rightPayload bottom) (encode forest))
        (ForestConnector.ThreeColors.layout
          (ComponentPhysicalRepair.view none wingOrientation headerKey (payload leftPayload rightPayload bottom) (encode forest))) = some config ∧
      config.tree = actual.mapRecords Prod.snd := by
  obtain ⟨left,right,leftPacked,rightPacked,view⟩ := result
  exact pieces markerId color source left right leftPacked rightPacked leftPayload rightPayload bottom stored ready decoded
    actual valid view headerKey

end ChaCha.Paper20261030.ComputedComponentReconstruction
