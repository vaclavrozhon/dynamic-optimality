import TangoSquared.Paper20261030.CanonicalSubtreeValidity
import TangoSquared.Paper20261030.EnclosingPacketInvariants

set_option autoImplicit false

/-! Physical validity of the bare component follows from validity of the
actual enclosed output. Removing its enclosing packet is used only for
this proof witness; it does not introduce a runtime operation. -/

namespace TangoSquared.Paper20261030.PacketPrefixTransfer

open ColoredStorage SourcePointer Structural PhysicalPacketStaging PacketLayers

variable {α β ρ ι : Type*}

theorem valid_of_output (markerId : ι) (packet : Packet α ρ ι) (source : Source β (Context.Cell α ρ ι))
    (valid : CanonicalComponentUniqueness.Valid markerId (output packet source)) :
    CanonicalComponentUniqueness.Valid markerId source := by
  have aligned := SourceRecordPredicate.root (PacketAlignment.Predicate markerId) _ valid.1
  have clear := SourceRecordPredicate.root (MarkerFreePackets.Vertex markerId) _ valid.2.1
  have outputRoot : (output packet source).rootRecord =
      (source.rootRecord.1,reidentify source.rootRecord.1 packet ++ source.rootRecord.2) := by cases source <;> rfl
  rw [outputRoot] at aligned clear
  change PacketAlignment.Aligned markerId source.rootRecord.1
    (reidentify source.rootRecord.1 packet ++ source.rootRecord.2) at aligned
  change MarkerFreePackets.Packet markerId (reidentify source.rootRecord.1 packet ++ source.rootRecord.2) at clear
  have ownAligned : PacketAlignment.Predicate markerId source.rootRecord :=
    fun item member => aligned item (List.mem_append_right _ member)
  have ownClear : MarkerFreePackets.Vertex markerId source.rootRecord :=
    fun item member => clear item (List.mem_append_right _ member)
  have reset : (output packet source).setRoot source.rootRecord = source := by cases source <;> rfl
  refine ⟨?_,?_,?_⟩
  · simpa only [reset] using SourceRecordPredicate.setRoot (PacketAlignment.Predicate markerId)
      (output packet source) source.rootRecord valid.1 ownAligned
  · simpa only [reset] using SourceRecordPredicate.setRoot (MarkerFreePackets.Vertex markerId)
      (output packet source) source.rootRecord valid.2.1 ownClear
  · rw [← identifiers packet source]
    exact valid.2.2

end TangoSquared.Paper20261030.PacketPrefixTransfer

namespace TangoSquared.Paper20261030.EnclosingPacketOperation

open ColoredStorage SourcePointer PhysicalPacketStaging PacketLayers

variable {α β ρ ι : Type*} [DecidableEq ι]

theorem output_focus_valid (markerId : ι) (packet : Packet α ρ ι) (oldId : ι)
    (current : Cursor β (Context.Cell α ρ ι))
    (valid : CanonicalComponentUniqueness.Valid markerId (output packet oldId current).tree) :
    CanonicalComponentUniqueness.Valid markerId current.focus :=
  PacketPrefixTransfer.valid_of_output markerId packet current.focus
    (CanonicalComponentUniqueness.Valid.focused markerId (output packet oldId current) valid)

end TangoSquared.Paper20261030.EnclosingPacketOperation
