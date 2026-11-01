import TangoSquared.Paper20261030.VirtualPhysicalPackets

/-! Computing replacement physical virtual headers from the two headers
actually read and the five repaired logical records. The zero-depth case
uses four records. Physical slot identifiers are rebuilt inside each
bounded virtual piece; identifiers of original-key vertices are retained
by the surrounding physical-tree program.
-/

namespace TangoSquared.Paper20261030.VirtualHeadPacketController

open ColoredStorage SourcePointer Structural HeadBoundary PhysicalForestMetadata
open VirtualHeadPackets (Logical Header prefixes)
open ObservedHeadBlueprint (owned)

variable {α ρ ι : Type*}

local instance : LinearOrder (Option Bool) := inferInstanceAs (LinearOrder (WithBot Bool))

abbrev Physical (α ρ ι : Type*) := VirtualHeaderController.Virtual α (Record (Logical ρ ι) Nat)

def packRoot : Header α ρ ι → Physical α ρ ι
  | some ⟨source,[]⟩ => VirtualPhysicalPackets.encode source
  | _ => none

def exchange (old fresh : Records ρ ι (Option Bool)) (active incoming : Physical α ρ ι) :
    Option (Physical α ρ ι × Physical α ρ ι) :=
  (VirtualHeadPackets.exchange old fresh (VirtualPhysicalPackets.decode active) (VirtualPhysicalPackets.decode incoming)).map
    (fun pair => (packRoot pair.1,packRoot pair.2))

def exchangeRoot (old fresh : RootRecords ρ ι) (active incoming : Physical α ρ ι) :
    Option (Physical α ρ ι × Physical α ρ ι) :=
  (VirtualHeadPackets.exchangeRoot old fresh (VirtualPhysicalPackets.decode active) (VirtualPhysicalPackets.decode incoming)).map
    (fun pair => (packRoot pair.1,packRoot pair.2))

theorem computed (old fresh : Records ρ ι (Option Bool)) (depth oldBottom newBottom : α)
    (oldPacket incomingPacket : List (Logical ρ ι)) (active incoming : Physical α ρ ι)
    (activeDecoded : VirtualPhysicalPackets.decode active =
      some ⟨.leaf oldBottom (prefixes old.low old.oldHigh ++ oldPacket),[]⟩)
    (incomingDecoded : VirtualPhysicalPackets.decode incoming =
      some ⟨.fork [old.incomingHigh] (.leaf depth [old.incomingTerminal]) (.leaf newBottom incomingPacket),[]⟩) :
    exchange old fresh active incoming = some
      (VirtualPhysicalPackets.encode (.leaf newBottom (prefixes fresh.low fresh.incomingHigh ++ incomingPacket)),
        VirtualPhysicalPackets.encode (.fork [fresh.oldHigh] (.leaf depth [fresh.oldTerminal]) (.leaf oldBottom oldPacket))) := by
  rw [exchange,activeDecoded,incomingDecoded,VirtualHeadPackets.exchange_exact]
  rfl

theorem computed_root (old fresh : RootRecords ρ ι) (depth oldBottom newBottom : α)
    (oldPacket incomingPacket : List (Logical ρ ι)) (active incoming : Physical α ρ ι)
    (activeDecoded : VirtualPhysicalPackets.decode active =
      some ⟨.leaf oldBottom (owned none old.oldHigh ++ oldPacket),[]⟩)
    (incomingDecoded : VirtualPhysicalPackets.decode incoming =
      some ⟨.fork [old.incomingHigh] (.leaf depth [old.incomingTerminal]) (.leaf newBottom incomingPacket),[]⟩) :
    exchangeRoot old fresh active incoming = some
      (VirtualPhysicalPackets.encode (.leaf newBottom (owned none fresh.incomingHigh ++ incomingPacket)),
        VirtualPhysicalPackets.encode (.fork [fresh.oldHigh] (.leaf depth [fresh.oldTerminal]) (.leaf oldBottom oldPacket))) := by
  rw [exchangeRoot,activeDecoded,incomingDecoded]
  exact congrArg (fun output => output.map (fun pair => (packRoot pair.1,packRoot pair.2)))
    (VirtualHeadPackets.exchange_root_exact old fresh depth oldBottom newBottom oldPacket incomingPacket)

/-- Both replacement pieces carry distinct local physical ids and exact
canonical parent/child fields; decoding recovers their logical packets. -/
theorem output_ready (activeBottom dormantBottom depth : α)
    (activePacket dormantPacket : List (Logical ρ ι)) (high terminal : Logical ρ ι) :
    ∃ (active dormant : Source α (Payload (Logical ρ ι) Nat)),
      (active.inventory Prod.fst).Nodup ∧ (dormant.inventory Prod.fst).Nodup ∧
      VirtualPhysicalPackets.encode (.leaf activeBottom activePacket) = some (encodeCursor ⟨active,[]⟩) ∧
      VirtualPhysicalPackets.encode (.fork [high] (.leaf depth [terminal]) (.leaf dormantBottom dormantPacket)) =
        some (encodeCursor ⟨dormant,[]⟩) ∧
      active.mapRecords Prod.snd = .leaf activeBottom activePacket ∧
      dormant.mapRecords Prod.snd = .fork [high] (.leaf depth [terminal]) (.leaf dormantBottom dormantPacket) := by
  obtain ⟨active,_,activeErases,activeUnique,activeEncoded⟩ :=
    VirtualPhysicalPackets.encode_correct (.leaf activeBottom activePacket) (by change 1 ≤ 2; decide)
  obtain ⟨dormant,_,dormantErases,dormantUnique,dormantEncoded⟩ :=
    VirtualPhysicalPackets.encode_correct (.fork [high] (.leaf depth [terminal]) (.leaf dormantBottom dormantPacket))
      (by change 1+1 ≤ 2; decide)
  exact ⟨active,dormant,activeUnique,dormantUnique,activeEncoded,dormantEncoded,activeErases,dormantErases⟩

end TangoSquared.Paper20261030.VirtualHeadPacketController
