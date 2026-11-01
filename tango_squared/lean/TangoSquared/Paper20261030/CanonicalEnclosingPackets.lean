import TangoSquared.Paper20261030.EnclosingPacketInvariants

set_option autoImplicit false

/-!
# Canonical enclosing layers under a moved component root

Several enclosing components can share the same physical root. Each
enclosing layer is either a virtual header or an attached routing leaf.
The packet sequence below encodes those layers in outer-to-inner order.
Moving this sequence reassigns precisely the real leaf ids while retaining
logical records, routing parents, delimiters, and stored virtual cursors.
-/

namespace TangoSquared.Paper20261030.CanonicalEnclosingPackets

open ColoredStorage SourcePointer Structural PhysicalPacketStaging PacketLayers
open CanonicalPacketLayerViews

variable {α β ρ ι : Type*}

inductive Layer (α ρ ι : Type*) where
  | virtual (cursor : VirtualHeaderController.Virtual α (PhysicalForestMetadata.Record ρ ι))
  | leaf (records : List ρ) (parent : Option ι)

def layer (vertexId : ι) : Layer α ρ ι → Packet α ρ ι
  | .virtual cursor => [some (.header cursor),none]
  | .leaf records parent => [some (.real ((vertexId,records),MixedPacketRepair.neighbors parent false none)),none]

def packet (vertexId : ι) (layers : List (Layer α ρ ι)) : Packet α ρ ι := layers.flatMap (layer vertexId)

theorem packet_length (vertexId : ι) (layers : List (Layer α ρ ι)) :
    (packet vertexId layers).length = 2*layers.length := by
  induction layers with
  | nil => rfl
  | cons first rest ih =>
    cases first <;> simp only [packet,List.flatMap_cons,List.length_append,layer,List.length_cons,List.length_nil,
      show (rest.flatMap (layer vertexId)).length = 2*rest.length from ih] <;> omega

theorem reidentify (old fresh : ι) (layers : List (Layer α ρ ι)) :
    PacketPrefixTransfer.reidentify fresh (packet old layers) = packet fresh layers := by
  induction layers with
  | nil => rfl
  | cons first rest ih =>
    simp only [packet,List.flatMap_cons,PacketPrefixTransfer.reidentify,List.map_append] at ih ⊢
    rw [ih]
    cases first <;> rfl

theorem moved (old : ι) (layers : List (Layer α ρ ι)) (source : Source β (Context.Cell α ρ ι)) :
    PacketPrefixTransfer.output (packet old layers) source =
      PacketPrefixTransfer.attach (packet source.rootRecord.1 layers) source := by
  rw [PacketPrefixTransfer.output,reidentify]

theorem leaf_view (records : List ρ) (parent : Option ι) (key : α) (reverse : Bool)
    (source : Source β (Context.Cell α ρ ι)) :
    (PacketPrefixTransfer.attach (layer source.rootRecord.1 (.leaf records parent)) source).mapRecords Prod.snd =
      routing (fun _ => source.mapRecords Prod.snd) reverse parent (.leaf key (source.rootRecord.1,records)) := by
  rw [CanonicalPacketLayerViews.leaf]
  simp only [PacketPrefixTransfer.attach,Source.mapRecords_setRoot,Source.mapRecords_root,layer,
    fields,Source.support,MixedPacketRepair.neighbors,Option.map_none,List.cons_append,List.nil_append]

theorem virtual_view (cursor : VirtualHeaderController.Virtual α (PhysicalForestMetadata.Record ρ ι))
    (source : Source β (Context.Cell α ρ ι)) :
    (PacketPrefixTransfer.attach (layer source.rootRecord.1 (.virtual cursor)) source).mapRecords Prod.snd =
      (source.mapRecords Prod.snd).setRoot (some (.header cursor)::none::source.rootRecord.2) := by
  simp only [PacketPrefixTransfer.attach,Source.mapRecords_setRoot,layer,List.cons_append,List.nil_append]

theorem parent_preserves [DecidableEq ι] (old fresh vertexId : ι) (layers : List (Layer α ρ ι)) :
    (packet vertexId layers).map (PacketParentRepair.entry old fresh) = packet vertexId layers := by
  induction layers with
  | nil => rfl
  | cons first rest ih =>
    simp only [packet,List.flatMap_cons,List.map_append] at ih ⊢
    rw [ih]
    cases first <;> rfl

/-- All outer leaf/header layers are unchanged while the final routing
fork's physical-child references are repaired, including mirrored forks. -/
theorem parent_left [DecidableEq ι] (layers : List (Layer α ρ ι))
    (vertexId old fresh sibling : ι) (different : sibling ≠ old)
    (records : List ρ) (parent : Option ι) (reverse : Bool) :
    PacketParentRepair.edit old fresh (vertexId,packet vertexId layers++
      [some (.real ((vertexId,records),MixedPacketRepair.neighbors parent reverse (some (old,sibling))))]) =
      (vertexId,packet vertexId layers++
        [some (.real ((vertexId,records),MixedPacketRepair.neighbors parent reverse (some (fresh,sibling))))]) := by
  simp only [PacketParentRepair.edit,List.map_append,parent_preserves,List.map_cons,List.map_nil,
    PacketParentRepair.neighbors_left parent reverse old fresh sibling different vertexId records]

theorem parent_right [DecidableEq ι] (layers : List (Layer α ρ ι))
    (vertexId old fresh sibling : ι) (different : sibling ≠ old)
    (records : List ρ) (parent : Option ι) (reverse : Bool) :
    PacketParentRepair.edit old fresh (vertexId,packet vertexId layers++
      [some (.real ((vertexId,records),MixedPacketRepair.neighbors parent reverse (some (sibling,old))))]) =
      (vertexId,packet vertexId layers++
        [some (.real ((vertexId,records),MixedPacketRepair.neighbors parent reverse (some (sibling,fresh))))]) := by
  simp only [PacketParentRepair.edit,List.map_append,parent_preserves,List.map_cons,List.map_nil,
    PacketParentRepair.neighbors_right parent reverse old fresh sibling different vertexId records]

end TangoSquared.Paper20261030.CanonicalEnclosingPackets
