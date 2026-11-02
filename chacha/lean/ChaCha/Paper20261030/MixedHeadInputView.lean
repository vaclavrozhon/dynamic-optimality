import ChaCha.Paper20261030.MixedPacketRepresentation

/-!
# The complete physical input view of a prepared head boundary

All exposed joins have their actual old immutable id, packet id, and
physical fields. Retained block trees include their full payloads. The
theorem derives the staging relation for their nested active/dormant view
for every pattern of absent wings; ids and fields are proof parameters.

The remaining canonical-input bridge is to obtain this finite view from
the maintained tagged color projections after boundary preparation.
-/

namespace ChaCha.Paper20261030.MixedHeadInputView

open ColoredStorage SourcePointer Structural HeadBoundary PhysicalPacketStaging PacketLayers
open Representation

variable {α β ρ ι η : Type*}

local instance : LinearOrder (Option Bool) := inferInstanceAs (LinearOrder (WithBot Bool))

structure JoinFields (ι : Type*) where
  vertexId : ι
  packetId : ι
  fields : Fields ι Unit

structure PrimaryFields (ι : Type*) where
  first : ι
  root : ι

structure ActiveFields (ι : Type*) where
  lowerLeft : JoinFields ι
  lowerRight : JoinFields ι
  upperLeft : JoinFields ι
  upperRight : JoinFields ι
  attachmentId : ι
  attachmentFields : Fields ι Unit
  primary : PrimaryFields ι

abbrev Physical (β α ρ ι : Type*) := Option (Source β (Context.Cell α ρ ι))

def join (fields : JoinFields ι) (records : List ρ) :=
  physicalJoin (β := β) (α := α) fields.vertexId fields.packetId fields.fields records

def rawBlock (header : Packet α ρ ι) (source : Source β (Context.Cell α ρ ι)) : Source β (Context.Cell α ρ ι) :=
  source.setRoot (source.rootRecord.1,header++source.rootRecord.2)

theorem rawBlock_stored (blocks : Fin 8 → Source β (Packet α ρ ι)) (key : Fin 8)
    (header : Packet α ρ ι) (source : Source β (Context.Cell α ρ ι))
    (erases : source.mapRecords Prod.snd = blocks key) :
    Reached.Stored blocks (.leaf key (.raw header .base)) (rawBlock header source) := by
  have sourceRoot : source.rootRecord.2 = (blocks key).rootRecord := by
    simpa only [Source.mapRecords_root] using congrArg Source.rootRecord erases
  exact Representation.setRoot blocks (.leaf key (.prefix [])) source (Representation.block blocks key source erases)
    (.raw header .base) (header++source.rootRecord.2) ⟨source.rootRecord.2,rfl,sourceRoot⟩

def block (bits : Fin 8 → Bool) (sources : Fin 8 → Source β (Context.Cell α ρ ι)) (key : Fin 8) : Physical β α ρ ι :=
  if bits key then some (sources key) else none

theorem block_stored (markerId : ι) (bits : Fin 8 → Bool) (sources : Fin 8 → Source β (Context.Cell α ρ ι))
    (blocks : Fin 8 → Source β (Packet α ρ ι)) (erases : ∀ key, (sources key).mapRecords Prod.snd = blocks key) (key : Fin 8) :
    Holds blocks (HeadPacketLayout.block bits key) (block bits sources key) := by
  cases present : bits key <;> simp only [HeadPacketLayout.block,block,present,Bool.false_eq_true,if_false,if_true]
  · trivial
  · exact Representation.block blocks key (sources key) (erases key)

theorem logical_stored (blocks : Fin 8 → Source β (Packet α ρ ι)) (records : List ρ)
    (layout : HeadPacketLayout.Layout (Fin 8) α ρ ι) (source : Physical β α ρ ι)
    (stored : Holds blocks layout source) (routing : HeadPacketLayout.RoutingRoot layout) :
    Holds blocks (HeadPacketLayout.push (HeadPacketLayout.addLogical records) layout) (source.map (addRoot records)) := by
  cases layout <;> cases source <;> try exact False.elim stored
  · trivial
  · exact Representation.logical blocks _ _ stored records routing

def attach (packetId : ι) (fields : Fields ι Unit) (record : ρ) (child : Physical β α ρ ι) : Physical β α ρ ι :=
  child.map (fun source => source.setRoot
    (source.rootRecord.1,some (.real ((packetId,[record]),fields)) :: none :: source.rootRecord.2))

theorem attachment_stored (markerId packetId : ι) (fields : Fields ι Unit) (record : ρ)
    (blocks : Fin 8 → Source β (Packet α ρ ι)) (layout : HeadPacketLayout.Layout (Fin 8) α ρ ι)
    (source : Physical β α ρ ι) (stored : Holds blocks layout source) :
    Holds blocks (HeadPacketLayout.attachment markerId record layout) (attach packetId fields record source) := by
  cases layout <;> cases source <;> try exact False.elim stored
  · trivial
  · exact Representation.attachment markerId packetId fields record blocks _ _ stored

def dormant (bits : Fin 8 → Bool) (sources : Fin 8 → Source β (Context.Cell α (HeadBoundary.Record ρ η (Option Bool)) ι))
    (l b r : Fin 8) (fields : PrimaryFields ι) (high : HeadBoundary.Record ρ η (Option Bool))
    (header : Packet α (HeadBoundary.Record ρ η (Option Bool)) ι) : Physical β α (HeadBoundary.Record ρ η (Option Bool)) ι :=
  physicalPrimaryJoin fields.root
    (physicalPrimaryJoin fields.first
      ((block bits sources l).map (addRoot (ObservedHeadBlueprint.owned (some true) high)))
      (some (rawBlock header (sources b))))
    ((block bits sources r).map (addRoot (ObservedHeadBlueprint.owned (some false) high)))

theorem dormant_stored (markerId : ι) (bits : Fin 8 → Bool)
    (sources : Fin 8 → Source β (Context.Cell α (HeadBoundary.Record ρ η (Option Bool)) ι))
    (blocks : Fin 8 → Source β (Packet α (HeadBoundary.Record ρ η (Option Bool)) ι))
    (erases : ∀ key, (sources key).mapRecords Prod.snd = blocks key)
    (l b r : Fin 8) (fields : PrimaryFields ι) (high : HeadBoundary.Record ρ η (Option Bool))
    (header : Packet α (HeadBoundary.Record ρ η (Option Bool)) ι) :
    Holds blocks (HeadPacketLayout.dormant markerId bits l b r high header) (dormant bits sources l b r fields high header) :=
  Representation.primaryJoin fields.root blocks _ _ _ _
    (Representation.primaryJoin fields.first blocks _ _ _ _
      (logical_stored blocks _ _ _ (block_stored markerId bits sources blocks erases l) (HeadPacketLayout.block_routing bits l))
      (rawBlock_stored blocks b header (sources b) (erases b)))
    (logical_stored blocks _ _ _ (block_stored markerId bits sources blocks erases r) (HeadPacketLayout.block_routing bits r))

def active (bits : Fin 8 → Bool) (sources : Fin 8 → Source β (Context.Cell α (HeadBoundary.Record ρ η (Option Bool)) ι))
    (l r tl b tr : Fin 8) (child : Physical β α (HeadBoundary.Record ρ η (Option Bool)) ι) (fields : ActiveFields ι)
    (direction : Bool) (low high terminal : HeadBoundary.Record ρ η (Option Bool))
    (header : Packet α (HeadBoundary.Record ρ η (Option Bool)) ι) : Physical β α (HeadBoundary.Record ρ η (Option Bool)) ι :=
  let attached := attach fields.attachmentId fields.attachmentFields terminal child
  let left := if direction then join fields.upperLeft (ObservedHeadBlueprint.owned (some true) high) attached (block bits sources tl)
    else (block bits sources tl).map (addRoot (ObservedHeadBlueprint.owned (some true) high))
  let right := if direction then (block bits sources tr).map (addRoot (ObservedHeadBlueprint.owned (some false) high))
    else join fields.upperRight (ObservedHeadBlueprint.owned (some false) high) (block bits sources tr) attached
  physicalPrimaryJoin fields.primary.root
    (physicalPrimaryJoin fields.primary.first
      (join fields.lowerLeft (ObservedHeadBlueprint.owned (some true) low) (block bits sources l) left)
      (some (rawBlock header (sources b))))
    (join fields.lowerRight (ObservedHeadBlueprint.owned (some false) low) right (block bits sources r))

theorem active_stored (markerId : ι) (bits : Fin 8 → Bool)
    (sources : Fin 8 → Source β (Context.Cell α (HeadBoundary.Record ρ η (Option Bool)) ι))
    (blocks : Fin 8 → Source β (Packet α (HeadBoundary.Record ρ η (Option Bool)) ι))
    (erases : ∀ key, (sources key).mapRecords Prod.snd = blocks key)
    (l r tl b tr : Fin 8) (boundary : HeadPacketLayout.Layout (Fin 8) α (HeadBoundary.Record ρ η (Option Bool)) ι)
    (child : Physical β α (HeadBoundary.Record ρ η (Option Bool)) ι) (childStored : Holds blocks boundary child)
    (fields : ActiveFields ι) (direction : Bool) (low high terminal : HeadBoundary.Record ρ η (Option Bool))
    (header : Packet α (HeadBoundary.Record ρ η (Option Bool)) ι) :
    Holds blocks (HeadPacketLayout.active markerId bits l r tl b tr boundary direction low high terminal header)
      (active bits sources l r tl b tr child fields direction low high terminal header) := by
  have blockStored (key : Fin 8) := block_stored markerId bits sources blocks erases key
  have blockRouting (key : Fin 8) := HeadPacketLayout.block_routing
    (α := α) (ρ := HeadBoundary.Record ρ η (Option Bool)) (ι := ι) bits key
  have attached := attachment_stored markerId fields.attachmentId fields.attachmentFields terminal blocks boundary child childStored
  have attachedRouting := HeadPacketLayout.attachment_routing markerId terminal boundary
  have joinStored (fields : JoinFields ι) := Representation.realJoin (κ := Fin 8) (α := α) (β := β)
    (ρ := HeadBoundary.Record ρ η (Option Bool)) markerId fields.vertexId fields.packetId fields.fields
  cases direction
  · exact Representation.primaryJoin _ blocks _ _ _ _
      (Representation.primaryJoin _ blocks _ _ _ _
        (joinStored fields.lowerLeft _ blocks _ _ _ _ (blockStored l)
          (logical_stored blocks _ _ _ (blockStored tl) (blockRouting tl))
          (blockRouting l) (HeadPacketLayout.push_routing _ _ (blockRouting tl)))
        (rawBlock_stored blocks b header (sources b) (erases b)))
      (joinStored fields.lowerRight _ blocks _ _ _ _
        (joinStored fields.upperRight _ blocks _ _ _ _ (blockStored tr) attached (blockRouting tr) attachedRouting)
        (blockStored r) (HeadPacketLayout.join_routing _ _ _ _ (blockRouting tr) attachedRouting) (blockRouting r))
  · exact Representation.primaryJoin _ blocks _ _ _ _
      (Representation.primaryJoin _ blocks _ _ _ _
        (joinStored fields.lowerLeft _ blocks _ _ _ _ (blockStored l)
          (joinStored fields.upperLeft _ blocks _ _ _ _ attached (blockStored tl) attachedRouting (blockRouting tl))
          (blockRouting l) (HeadPacketLayout.join_routing _ _ _ _ attachedRouting (blockRouting tl)))
        (rawBlock_stored blocks b header (sources b) (erases b)))
      (joinStored fields.lowerRight _ blocks _ _ _ _
        (logical_stored blocks _ _ _ (blockStored tr) (blockRouting tr)) (blockStored r)
        (HeadPacketLayout.push_routing _ _ (blockRouting tr)) (blockRouting r))

def before (bits : Fin 8 → Bool)
    (sources : Fin 8 → Source β (Context.Cell α (HeadBoundary.Record ρ η (Option Bool)) ι))
    (activeFields : ActiveFields ι) (incomingFields : PrimaryFields ι) (direction : Bool)
    (records : Records ρ η (Option Bool))
    (oldHeader incomingHeader : Packet α (HeadBoundary.Record ρ η (Option Bool)) ι) :=
  active bits sources 0 7 1 2 3
    (dormant bits sources 4 5 6 incomingFields records.incomingHigh incomingHeader)
    activeFields direction records.low records.oldHigh records.oldTerminal oldHeader

theorem before_stored (markerId : ι) (bits : Fin 8 → Bool)
    (sources : Fin 8 → Source β (Context.Cell α (HeadBoundary.Record ρ η (Option Bool)) ι))
    (blocks : Fin 8 → Source β (Packet α (HeadBoundary.Record ρ η (Option Bool)) ι))
    (erases : ∀ key, (sources key).mapRecords Prod.snd = blocks key)
    (activeFields : ActiveFields ι) (incomingFields : PrimaryFields ι) (direction : Bool)
    (records : Records ρ η (Option Bool))
    (oldHeader incomingHeader : Packet α (HeadBoundary.Record ρ η (Option Bool)) ι) :
    Holds blocks (HeadPacketLayout.before markerId bits direction records oldHeader incomingHeader)
      (before bits sources activeFields incomingFields direction records oldHeader incomingHeader) :=
  active_stored markerId bits sources blocks erases 0 7 1 2 3 _ _
    (dormant_stored markerId bits sources blocks erases 4 5 6 incomingFields records.incomingHigh incomingHeader)
    activeFields direction records.low records.oldHigh records.oldTerminal oldHeader

theorem input (markerId : ι) (bits : Fin 8 → Bool)
    (sources : Fin 8 → Source β (Context.Cell α (HeadBoundary.Record ρ η (Option Bool)) ι))
    (blocks : Fin 8 → Source β (Packet α (HeadBoundary.Record ρ η (Option Bool)) ι))
    (erases : ∀ key, (sources key).mapRecords Prod.snd = blocks key)
    (activeFields : ActiveFields ι) (incomingFields : PrimaryFields ι) (direction : Bool)
    (records : Records ρ η (Option Bool))
    (oldHeader incomingHeader : Packet α (HeadBoundary.Record ρ η (Option Bool)) ι)
    (layout : Source (Fin 8) (Expression α (HeadBoundary.Record ρ η (Option Bool)) ι))
    (found : HeadPacketLayout.before markerId bits direction records oldHeader incomingHeader = some layout)
    (source : Source β (Context.Cell α (HeadBoundary.Record ρ η (Option Bool)) ι))
    (actual : before bits sources activeFields incomingFields direction records oldHeader incomingHeader = some source) :
    Reached.Stored blocks layout source := by
  have represented := before_stored markerId bits sources blocks erases activeFields incomingFields direction records oldHeader incomingHeader
  rw [found,actual] at represented
  exact represented

end ChaCha.Paper20261030.MixedHeadInputView
