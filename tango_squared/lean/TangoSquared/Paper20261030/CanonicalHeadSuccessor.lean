import TangoSquared.Paper20261030.CanonicalHeadWitnessOutput
import TangoSquared.Paper20261030.HeadPacketMarkerFree

set_option autoImplicit false

/-!
# Exact successor payloads from the retained canonical input

Every output port carries either its unchanged old-prefix payload, its
unchanged incoming-tail payload, or the newly reconstructed dormant
component at the switched boundary. This specializes the generic payload
predicate to concrete input data; no assumed output representation is
needed. The supplied port separation follows from disjoint source blocks.
-/

namespace TangoSquared.Paper20261030.CanonicalHeadSuccessor

open ColoredStorage SourcePointer Structural PhysicalPacketStaging PacketLayers
open CanonicalHeadOutput RepairedPayloadLayouts

variable {α β ρ ι η : Type*}

def Payload (activePayload incomingPayload : Option Bool → α → Source β (Packet α (Logical ρ η) ι))
    (head oldTail incomingTail : Bool → ProjectionLocal.Projected α (Logical ρ η))
    (direction : Bool) (depth : α) (records : HeadBoundary.Records ρ η (Option Bool))
    (dormantHeader : Packet α (Logical ρ η) ι) (oldBottom : Source β (Packet α (Logical ρ η) ι))
    (side : Bool) (key : α) (body : Source β (Packet α (Logical ρ η) ι)) : Prop :=
  (side = !direction ∧ key = depth ∧
    Dormant (activePayload (some true)) (activePayload (some false))
      (oldTail true) (oldTail false) records.oldHigh dormantHeader oldBottom (some body)) ∨
  (key ∈ ports (head side) ∧ body = activePayload (some side) key) ∨
  (key ∈ ports (incomingTail side) ∧ body = incomingPayload (some side) key)

def Result (activePayload incomingPayload : Option Bool → α → Source β (Packet α (Logical ρ η) ι))
    (head oldTail incomingTail : Bool → ProjectionLocal.Projected α (Logical ρ η))
    (direction : Bool) (depth : α) (records : HeadBoundary.Records ρ η (Option Bool))
    (newHeader dormantHeader : Packet α (Logical ρ η) ι)
    (oldBottom newBottom : Source β (Packet α (Logical ρ η) ι)) :=
  Active (Payload activePayload incomingPayload head oldTail incomingTail direction depth records dormantHeader oldBottom)
    (head true) (head false) (incomingTail true) (incomingTail false) direction depth records newHeader newBottom

theorem boundary_iff (activePayload incomingPayload : Option Bool → α → Source β (Packet α (Logical ρ η) ι))
    (head oldTail incomingTail : Bool → ProjectionLocal.Projected α (Logical ρ η))
    (direction : Bool) (depth : α) (records : HeadBoundary.Records ρ η (Option Bool))
    (dormantHeader : Packet α (Logical ρ η) ι) (oldBottom body : Source β (Packet α (Logical ρ η) ι))
    (headAbsent : depth ∉ ports (head (!direction))) (incomingAbsent : depth ∉ ports (incomingTail (!direction))) :
    Payload activePayload incomingPayload head oldTail incomingTail direction depth records dormantHeader oldBottom (!direction) depth body ↔
      Dormant (activePayload (some true)) (activePayload (some false))
        (oldTail true) (oldTail false) records.oldHigh dormantHeader oldBottom (some body) := by
  simp only [Payload,headAbsent,incomingAbsent,false_and,or_false,true_and]

theorem off_boundary (activePayload incomingPayload : Option Bool → α → Source β (Packet α (Logical ρ η) ι))
    (head oldTail incomingTail : Bool → ProjectionLocal.Projected α (Logical ρ η))
    (direction : Bool) (depth : α) (records : HeadBoundary.Records ρ η (Option Bool))
    (dormantHeader : Packet α (Logical ρ η) ι) (oldBottom : Source β (Packet α (Logical ρ η) ι))
    (side : Bool) (key : α) (body : Source β (Packet α (Logical ρ η) ι)) (different : key ≠ depth)
    (valid : Payload activePayload incomingPayload head oldTail incomingTail direction depth records dormantHeader oldBottom side key body) :
    (key ∈ ports (head side) ∧ body = activePayload (some side) key) ∨
      (key ∈ ports (incomingTail side) ∧ body = incomingPayload (some side) key) := by
  rcases valid with boundary | retained
  · exact False.elim (different boundary.2.1)
  · exact retained

theorem represents (markerId : ι) (direction : Bool) (depth : α)
    (old fresh : HeadBoundary.Records ρ η (Option Bool))
    (oldHeader incomingHeader newHeader dormantHeader : Packet α (Logical ρ η) ι)
    (activePayload incomingPayload : Option Bool → α → Source β (Packet α (Logical ρ η) ι))
    (headerKey : α) (head oldTail incomingTail : Bool → ProjectionLocal.Projected α (Logical ρ η))
    (blocks : Fin 8 → Source β (Packet α (Logical ρ η) ι))
    (before : Source (Fin 8) (Expression α (Logical ρ η) ι))
    (found : HeadPacketLayout.before markerId (ObservedHeadBlueprint.bits old) direction old oldHeader incomingHeader = some before)
    (source : Source β (Context.Cell α (Logical ρ η) ι)) (stored : Reached.Stored blocks before source)
    (ready : PacketConditions.wings (fun base => Ready base (.prefix [])) (ObservedHeadBlueprint.bits old) blocks)
    (clear : SourceRecordPredicate.Holds (MarkerFreePackets.Vertex markerId) source)
    (witnesses : CanonicalRetainedBlocks.HeadWitnesses (ObservedHeadBlueprint.bits old) blocks
      activePayload incomingPayload headerKey head oldTail incomingTail)
    (separate : ∀ side, Separate (head side) (incomingTail side))
    (headAbsent : ∀ side, depth ∉ ports (head side)) (incomingAbsent : ∀ side, depth ∉ ports (incomingTail side)) :
    RepairedComponentLayout.Represents markerId blocks
      (HeadPacketRepair.after (ObservedHeadBlueprint.bits old) direction newHeader.length dormantHeader.length)
      (HeadPacketLayout.after markerId (ObservedHeadBlueprint.bits old) direction fresh newHeader dormantHeader)
      (Result activePayload incomingPayload head oldTail incomingTail direction depth fresh
        newHeader dormantHeader (activePayload none headerKey) (incomingPayload none headerKey)) := by
  have ordinary := MarkerFreePackets.wing_roots markerId (ObservedHeadBlueprint.bits old) direction old oldHeader incomingHeader
    blocks before found source stored ready clear
  have output := witnesses.after markerId (ObservedHeadBlueprint.bits old) blocks activePayload incomingPayload headerKey
    head oldTail incomingTail ordinary
    (Payload activePayload incomingPayload head oldTail incomingTail direction depth fresh dormantHeader (blocks 2))
    (fun side key member => Or.inr (Or.inl ⟨member,rfl⟩))
    (fun side key member => Or.inr (Or.inr ⟨member,rfl⟩))
    direction depth fresh newHeader dormantHeader
    (fun body dormant => Or.inl ⟨rfl,rfl,dormant⟩) separate headAbsent incomingAbsent
  rw [witnesses.oldBottom,witnesses.newBottom] at output
  exact output

end TangoSquared.Paper20261030.CanonicalHeadSuccessor
