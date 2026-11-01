import TangoSquared.Paper20261030.RoutingPayloadCongruence

set_option autoImplicit false

/-! Canonical routing after a nested payload operation. The actual
prefix transfer and parent repair produce the encoding with the new
payload and its new root identifier at the same logical routing leaf.
No new routing operation or uncharged ancestor edit is introduced. -/

namespace TangoSquared.Paper20261030.CanonicalRoutingPayloadUpdate

open ColoredStorage SourcePointer Structural PhysicalPacketStaging PacketLayers
open CanonicalPacketLayerViews CanonicalEnclosingPackets

variable {α β ρ ι : Type*} [DecidableEq α] [DecidableEq ι]

theorem update (payload : α → Source β (Packet α ρ ι)) (reverse : Bool)
    (key : α) (old : ι) (records : List ρ) (outside : List (Frame α (ι × List ρ)))
    (unique : ((plug (.leaf key (old,records)) outside).inventory Prod.fst).Nodup)
    (target : Source β (Context.Cell α ρ ι)) (physicalOutside : List (Frame β (Context.Cell α ρ ι)))
    (context : physicalOutside.map (Frame.mapRecords Prod.snd) =
      (CanonicalRoutingCursor.cursor payload reverse ⟨.leaf key (old,records),outside⟩).ancestors)
    (agree : CanonicalRoutingCursor.AgreeOutside payload
      (Function.update payload key (target.mapRecords Prod.snd)) outside) :
    (EnclosingPacketOperation.output (layer old (.leaf records (parentId Prod.fst outside))) old
      ⟨target,physicalOutside⟩).tree.mapRecords Prod.snd =
      routing (Function.update payload key (target.mapRecords Prod.snd)) reverse none
        (plug (.leaf key (target.rootRecord.1,records)) outside) := by
  let freshPayload := Function.update payload key (target.mapRecords Prod.snd)
  let oldCursor : Cursor α (ι × List ρ) := ⟨.leaf key (old,records),outside⟩
  let newCursor : Cursor α (ι × List ρ) := ⟨.leaf key (target.rootRecord.1,records),outside⟩
  let finished := EnclosingPacketOperation.output (layer old (.leaf records (parentId Prod.fst outside))) old
    ⟨target,physicalOutside⟩
  have newAncestors : (CanonicalRoutingCursor.cursor freshPayload reverse newCursor).ancestors =
      match (CanonicalRoutingCursor.cursor payload reverse oldCursor).ancestors with
      | [] => []
      | first::rest => CanonicalRoutingCursor.repairFrame old target.rootRecord.1 first :: rest := by
    rw [← CanonicalRoutingCursor.ancestors_payload_congr payload freshPayload reverse newCursor agree]
    exact CanonicalRoutingCursor.parent_repair payload reverse (.leaf key (old,records))
      (.leaf key (target.rootRecord.1,records)) outside rfl unique
  have outsideEq : finished.ancestors.map (Frame.mapRecords Prod.snd) =
      (CanonicalRoutingCursor.cursor freshPayload reverse newCursor).ancestors := by
    rw [newAncestors,← context]
    cases physicalOutside with
    | nil => rfl
    | cons first rest =>
      change (PacketParentRepair.frame old target.rootRecord.1 first).mapRecords Prod.snd :: _ = _
      rw [CanonicalRoutingCursor.erase_repair]
      rfl
  have focusEq : finished.focus.mapRecords Prod.snd =
      (CanonicalRoutingCursor.cursor freshPayload reverse newCursor).focus := by
    rw [CanonicalRoutingCursor.leaf]
    simp only [finished,EnclosingPacketOperation.output,PacketPrefixTransfer.output,PacketPrefixTransfer.attach,
      Source.mapRecords_setRoot,layer,PacketPrefixTransfer.reidentify,List.map_cons,List.map_nil,
      PacketPrefixTransfer.reidentifyEntry,freshPayload,Function.update_self,Source.mapRecords_root,
      List.cons_append,List.nil_append,fields,Source.support,MixedPacketRepair.neighbors,Option.map_none]
  change (plug finished.focus finished.ancestors).mapRecords Prod.snd = _
  rw [← plug_mapRecords,focusEq,outsideEq]
  exact CanonicalRoutingCursor.tree freshPayload reverse newCursor

end TangoSquared.Paper20261030.CanonicalRoutingPayloadUpdate
