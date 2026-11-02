import ChaCha.Paper20261030.RootPackedForest
import ChaCha.Paper20261030.LocalStoredVirtualHeaderRead
import ChaCha.Paper20261030.VirtualHeadPacketController

/-!
# Reading virtual headers justified by the representation invariant

The shared-tree program reads the stored physical cursor. Its decoded
value is the actual logical packed projection at the source root, as
proved from the maintained forest invariant. The same fact supplies the
two decoded inputs required by the bounded head-header calculation.
-/

namespace ChaCha.Paper20261030.CanonicalVirtualHeaderRead

open ColoredStorage SourcePointer Structural PhysicalForestMetadata

variable {α β ρ C : Type*} [DecidableEq α] [LinearOrder C]

theorem execute (color : α → C) (source : Source α ρ)
    (forest : TaggedForest C α ρ Nat)
    (represented : ProjectionForest.Represents color ⟨source,[]⟩ (erase forest))
    (virtualColor : C) (orientation : C → Bool) (forward : orientation virtualColor = false)
    (headerKey : α) (payload : C → α → Source β (PhysicalPacketStaging.Packet α ρ Nat))
    (layout : Source C Unit) (distinct : (ForestConnector.colors layout).Nodup)
    (covers : ForestConnector.Covers layout
      (PayloadForestController.transform payload (VirtualHeaderController.encode virtualColor headerKey
        (ForestMirrorController.transform orientation (encode forest)))))
    (config : MultiSourceProgram.Configuration C β (PhysicalPacketStaging.Packet α ρ Nat))
    (assembled : ForestConnector.assemble
      (PayloadForestController.transform payload (VirtualHeaderController.encode virtualColor headerKey
        (ForestMirrorController.transform orientation (encode forest)))) layout = some config) :
    ∃ stored reads cost,
      MultiSourceProgram.Run (StoredVirtualHeaderRead.sharedProgram virtualColor) (.ready .start) config
        (.ready (.done stored)) config reads cost ∧
      VirtualPhysicalPackets.decode stored =
        (packed color virtualColor source).map (fun tree => ⟨tree,[]⟩) ∧ cost ≤ 2 := by
  obtain ⟨reads,cost,run,bounded⟩ := StoredVirtualHeaderRead.execute virtualColor headerKey
    (ForestMirrorController.transform orientation (encode forest)) payload layout distinct covers config assembled
  exact ⟨_,reads,cost,run,RootPackedForest.decode_virtual color source forest represented virtualColor orientation forward,bounded⟩

end ChaCha.Paper20261030.CanonicalVirtualHeaderRead

namespace ChaCha.Paper20261030.VirtualHeadPacketController

open ColoredStorage SourcePointer Structural HeadBoundary PhysicalForestMetadata
open VirtualHeadPackets (Logical prefixes)

variable {α ρ ι : Type*} [DecidableEq α]

local instance : LinearOrder (Option Bool) := inferInstanceAs (LinearOrder (WithBot Bool))

/-- The two header contents follow from the actual represented source
views. No separate decoded-header hypothesis is needed. -/
theorem computed_from_forests (old fresh : Records ρ ι (Option Bool))
    (activeColor incomingColor : α → Option Bool)
    (activeSource incomingSource : Source α (Logical ρ ι))
    (activeForest incomingForest : TaggedForest (Option Bool) α (Logical ρ ι) Nat)
    (activeRep : ProjectionForest.Represents activeColor ⟨activeSource,[]⟩ (erase activeForest))
    (incomingRep : ProjectionForest.Represents incomingColor ⟨incomingSource,[]⟩ (erase incomingForest))
    (orientation : Option Bool → Bool) (forward : orientation none = false)
    (depth oldBottom newBottom : α) (oldPacket incomingPacket : List (Logical ρ ι))
    (activePacked : packed activeColor none activeSource =
      some (.leaf oldBottom (prefixes old.low old.oldHigh ++ oldPacket)))
    (incomingPacked : packed incomingColor none incomingSource =
      some (.fork [old.incomingHigh] (.leaf depth [old.incomingTerminal]) (.leaf newBottom incomingPacket))) :
    exchange old fresh
      (ForestMirrorController.transform orientation (encode activeForest) none)
      (ForestMirrorController.transform orientation (encode incomingForest) none) = some
        (VirtualPhysicalPackets.encode (.leaf newBottom (prefixes fresh.low fresh.incomingHigh ++ incomingPacket)),
          VirtualPhysicalPackets.encode (.fork [fresh.oldHigh] (.leaf depth [fresh.oldTerminal]) (.leaf oldBottom oldPacket))) := by
  apply computed
  · rw [RootPackedForest.decode_virtual activeColor activeSource activeForest activeRep none orientation forward,activePacked]
    rfl
  · rw [RootPackedForest.decode_virtual incomingColor incomingSource incomingForest incomingRep none orientation forward,incomingPacked]
    rfl

theorem computed_root_from_forests (old fresh : RootRecords ρ ι)
    (activeColor incomingColor : α → Option Bool)
    (activeSource incomingSource : Source α (Logical ρ ι))
    (activeForest incomingForest : TaggedForest (Option Bool) α (Logical ρ ι) Nat)
    (activeRep : ProjectionForest.Represents activeColor ⟨activeSource,[]⟩ (erase activeForest))
    (incomingRep : ProjectionForest.Represents incomingColor ⟨incomingSource,[]⟩ (erase incomingForest))
    (orientation : Option Bool → Bool) (forward : orientation none = false)
    (depth oldBottom newBottom : α) (oldPacket incomingPacket : List (Logical ρ ι))
    (activePacked : packed activeColor none activeSource =
      some (.leaf oldBottom (ObservedHeadBlueprint.owned none old.oldHigh ++ oldPacket)))
    (incomingPacked : packed incomingColor none incomingSource =
      some (.fork [old.incomingHigh] (.leaf depth [old.incomingTerminal]) (.leaf newBottom incomingPacket))) :
    exchangeRoot old fresh
      (ForestMirrorController.transform orientation (encode activeForest) none)
      (ForestMirrorController.transform orientation (encode incomingForest) none) = some
        (VirtualPhysicalPackets.encode (.leaf newBottom (ObservedHeadBlueprint.owned none fresh.incomingHigh ++ incomingPacket)),
          VirtualPhysicalPackets.encode (.fork [fresh.oldHigh] (.leaf depth [fresh.oldTerminal]) (.leaf oldBottom oldPacket))) := by
  apply computed_root
  · rw [RootPackedForest.decode_virtual activeColor activeSource activeForest activeRep none orientation forward,activePacked]
    rfl
  · rw [RootPackedForest.decode_virtual incomingColor incomingSource incomingForest incomingRep none orientation forward,incomingPacked]
    rfl

end ChaCha.Paper20261030.VirtualHeadPacketController
