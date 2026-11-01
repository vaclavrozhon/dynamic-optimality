import TangoSquared.Paper20261030.RoutingUniquePort

set_option autoImplicit false

/-! Extending a canonical nested repair through an outer context. A
nonempty inner routing context absorbs the parent edit. For a singleton
routing piece the outer connector must be fixed by that edit; ordinary
empty connector packets satisfy this condition. -/

namespace TangoSquared.Paper20261030.EnclosingPacketOperation

open ColoredStorage SourcePointer PhysicalPacketStaging PacketLayers

variable {α β ρ ι : Type*} [DecidableEq ι]

def FixedParent (old fresh : ι) : List (Frame β (Context.Cell α ρ ι)) → Prop
  | [] => True
  | first::_ => PacketParentRepair.frame old fresh first = first

theorem extend (packet : Packet α ρ ι) (old : ι) (target : Source β (Context.Cell α ρ ι))
    (inside outside : List (Frame β (Context.Cell α ρ ι)))
    (safe : inside ≠ [] ∨ FixedParent old target.rootRecord.1 outside) :
    output packet old ⟨target,inside++outside⟩ =
      ⟨(output packet old ⟨target,inside⟩).focus,(output packet old ⟨target,inside⟩).ancestors++outside⟩ := by
  cases inside with
  | cons first rest => rfl
  | nil =>
    have fixed : FixedParent old target.rootRecord.1 outside := safe.resolve_left (by simp)
    cases outside with
    | nil => rfl
    | cons first rest =>
      change PacketParentRepair.frame old target.rootRecord.1 first = first at fixed
      simp only [output,List.nil_append,fixed]

theorem erase_extend (packet : Packet α ρ ι) (old : ι) (target : Source β (Context.Cell α ρ ι))
    (inside outside : List (Frame β (Context.Cell α ρ ι)))
    (safe : inside ≠ [] ∨ FixedParent old target.rootRecord.1 outside) :
    (output packet old ⟨target,inside++outside⟩).tree.mapRecords Prod.snd =
      plug ((output packet old ⟨target,inside⟩).tree.mapRecords Prod.snd) (outside.map (Frame.mapRecords Prod.snd)) := by
  rw [extend packet old target inside outside safe]
  change (plug _ (_++outside)).mapRecords Prod.snd = _
  rw [plug_append,plug_mapRecords]
  rfl

end TangoSquared.Paper20261030.EnclosingPacketOperation

namespace TangoSquared.Paper20261030.CanonicalRoutingPayloadUpdate

open ColoredStorage SourcePointer Structural PhysicalPacketStaging PacketLayers CanonicalPacketLayerViews CanonicalEnclosingPackets

variable {α β ρ ι : Type*} [DecidableEq α] [DecidableEq ι]

theorem update_enclosed (payload : α → Source β (Packet α ρ ι)) (reverse : Bool)
    (key : α) (old : ι) (records : List ρ) (outside : List (Frame α (ι × List ρ)))
    (unique : ((plug (.leaf key (old,records)) outside).inventory Prod.fst).Nodup)
    (distinct : (plug (.leaf key (old,records)) outside).shape.leaves.Nodup)
    (target : Source β (Context.Cell α ρ ι)) (physicalOutside enclosing : List (Frame β (Context.Cell α ρ ι)))
    (context : physicalOutside.map (Frame.mapRecords Prod.snd) =
      (CanonicalRoutingCursor.cursor payload reverse ⟨.leaf key (old,records),outside⟩).ancestors)
    (safe : physicalOutside ≠ [] ∨ EnclosingPacketOperation.FixedParent old target.rootRecord.1 enclosing) :
    (EnclosingPacketOperation.output (layer old (.leaf records (parentId Prod.fst outside))) old
      ⟨target,physicalOutside++enclosing⟩).tree.mapRecords Prod.snd =
      plug (routing (Function.update payload key (target.mapRecords Prod.snd)) reverse none
        (plug (.leaf key (target.rootRecord.1,records)) outside)) (enclosing.map (Frame.mapRecords Prod.snd)) := by
  rw [EnclosingPacketOperation.erase_extend _ old target physicalOutside enclosing safe,
    update_unique payload reverse key old records outside unique distinct target physicalOutside context]

end TangoSquared.Paper20261030.CanonicalRoutingPayloadUpdate
