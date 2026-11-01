import TangoSquared.Paper20261030.CanonicalReachedPayloadPosition
import TangoSquared.Paper20261030.GraftedPortUniqueness

set_option autoImplicit false

/-! Applying the canonical routing update at an actual reached incoming
cursor. Its physical ancestor list is split using its checked erased
context. Neutral component connectors absorb the singleton-wing case;
the same executed enclosing repair works in both cases. -/

namespace TangoSquared.Paper20261030.CanonicalRoutingPayloadUpdate

open ColoredStorage SourcePointer Structural PhysicalPacketStaging PacketLayers CanonicalPacketLayerViews CanonicalEnclosingPackets

variable {α β ρ ι : Type*} [DecidableEq α] [DecidableEq ι]

theorem reached (payload : α → Source β (Packet α ρ ι)) (reverse : Bool)
    (key : α) (records : List ρ) (outside : List (Frame α (ι × List ρ)))
    (current : Cursor β (Context.Cell α ρ ι))
    (unique : ((plug (.leaf key (current.focus.rootRecord.1,records)) outside).inventory Prod.fst).Nodup)
    (distinct : (plug (.leaf key (current.focus.rootRecord.1,records)) outside).shape.leaves.Nodup)
    (connectors enclosing : List (Frame β (Packet α ρ ι)))
    (proper : connectors ≠ []) (neutral : FrameRecords PacketParentNeutral.Neutral connectors)
    (context : current.ancestors.map (Frame.mapRecords Prod.snd) =
      (CanonicalRoutingCursor.cursor payload reverse ⟨.leaf key (current.focus.rootRecord.1,records),outside⟩).ancestors ++
        (connectors++enclosing)) (target : Source β (Context.Cell α ρ ι)) :
    (EnclosingPacketOperation.output (layer current.focus.rootRecord.1 (.leaf records (parentId Prod.fst outside)))
      current.focus.rootRecord.1 ⟨target,current.ancestors⟩).tree.mapRecords Prod.snd =
      plug (routing (Function.update payload key (target.mapRecords Prod.snd)) reverse none
        (plug (.leaf key (target.rootRecord.1,records)) outside)) (connectors++enclosing) := by
  obtain ⟨inner,outer,split,innerView,outerView⟩ := List.map_eq_append_iff.mp context
  have fixed := PacketParentNeutral.fixed_actual_prefix current.focus.rootRecord.1 target.rootRecord.1 outer
    connectors enclosing proper outerView neutral
  rw [split]
  have actual := update_enclosed payload reverse key current.focus.rootRecord.1 records outside unique distinct target inner outer
    innerView (Or.inr fixed)
  rw [outerView] at actual
  exact actual

end TangoSquared.Paper20261030.CanonicalRoutingPayloadUpdate
