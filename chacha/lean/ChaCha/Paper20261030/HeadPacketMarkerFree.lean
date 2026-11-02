import ChaCha.Paper20261030.PacketLayerMarkerFree

set_option autoImplicit false

/-! Marker-free raw headers suffice for the computed after-layout.
Before and after contain exactly the same retained block labels, including
all suppressed absent wings. These facts transport marker-free opaque
blocks from the actual input to the repacked output. -/

namespace ChaCha.Paper20261030.MarkerFreePackets

open ColoredStorage SourcePointer Structural PhysicalPacketStaging PacketLayers

variable {κ α β ρ ι η : Type*}

theorem RawTree.root (markerId : ι) (context : Source κ (Expression α ρ ι)) (clear : RawTree markerId context) :
    RawClear markerId context.rootRecord := by cases context <;> first | exact clear | exact clear.1

theorem RawTree.setRoot (markerId : ι) (context : Source κ (Expression α ρ ι)) (clear : RawTree markerId context)
    (expression : Expression α ρ ι) (fresh : RawClear markerId expression) : RawTree markerId (context.setRoot expression) := by
  cases context with
  | leaf => exact fresh
  | fork => exact ⟨fresh,clear.2⟩

def RawLayout (markerId : ι) : HeadPacketLayout.Layout κ α ρ ι → Prop
  | none => True
  | some context => RawTree markerId context

theorem logical_raw (markerId : ι) (records : List ρ) (expression : Expression α ρ ι)
    (clear : RawClear markerId expression) : RawClear markerId (HeadPacketLayout.addLogical records expression) := by
  cases expression <;> exact clear

theorem logical_layout (markerId : ι) (records : List ρ) (layout : HeadPacketLayout.Layout κ α ρ ι)
    (clear : RawLayout markerId layout) : RawLayout markerId (HeadPacketLayout.push (HeadPacketLayout.addLogical records) layout) := by
  cases layout with
  | none => trivial
  | some context => exact RawTree.setRoot markerId context clear _ (logical_raw markerId records _ (RawTree.root markerId context clear))

theorem realJoin_layout (markerId : ι) (records : List ρ) (left right : HeadPacketLayout.Layout κ α ρ ι)
    (hl : RawLayout markerId left) (hr : RawLayout markerId right) : RawLayout markerId (HeadPacketLayout.realJoin markerId records left right) := by
  cases left <;> cases right
  · trivial
  · exact logical_layout markerId records _ hr
  · exact logical_layout markerId records _ hl
  · exact ⟨trivial,hl,hr⟩

theorem primaryJoin_layout (markerId : ι) (left right : HeadPacketLayout.Layout κ α ρ ι)
    (hl : RawLayout markerId left) (hr : RawLayout markerId right) : RawLayout markerId (HeadPacketLayout.primaryJoin left right) := by
  cases left <;> cases right
  · trivial
  · exact hr
  · exact hl
  · exact ⟨trivial,hl,hr⟩

theorem block_layout (markerId : ι) (bits : κ → Bool) (key : κ) :
    RawLayout markerId (HeadPacketLayout.block (α := α) (ρ := ρ) bits key) := by
  cases present : bits key <;> simp only [HeadPacketLayout.block,present,Bool.false_eq_true,if_false,if_true] <;> trivial

theorem bottom_layout (markerId : ι) (key : κ) (header : PhysicalPacketStaging.Packet α ρ ι) (clear : Packet markerId header) :
    RawLayout markerId (HeadPacketLayout.bottom key header) := ⟨clear,trivial⟩

theorem attachment_layout (markerId : ι) (record : ρ) (child : HeadPacketLayout.Layout κ α ρ ι)
    (clear : RawLayout markerId child) : RawLayout markerId (HeadPacketLayout.attachment markerId record child) := by
  cases child with
  | none => trivial
  | some context =>
    apply RawTree.setRoot markerId context clear
    refine ⟨?_,RawTree.root markerId context clear⟩
    intro entry member
    have same : entry = none := by simpa only [List.mem_singleton] using member
    subst entry
    trivial

theorem dormant_layout (markerId : ι) (bits : Fin 8 → Bool) (l b r : Fin 8)
    (high : HeadBoundary.Record ρ η (Option Bool)) (header : PhysicalPacketStaging.Packet α (HeadBoundary.Record ρ η (Option Bool)) ι)
    (clear : Packet markerId header) : RawLayout markerId (HeadPacketLayout.dormant markerId bits l b r high header) :=
  primaryJoin_layout markerId _ _
    (primaryJoin_layout markerId _ _ (logical_layout markerId _ _ (block_layout markerId bits l)) (bottom_layout markerId b header clear))
    (logical_layout markerId _ _ (block_layout markerId bits r))

theorem active_layout (markerId : ι) (bits : Fin 8 → Bool) (l r tl b tr : Fin 8)
    (child : HeadPacketLayout.Layout (Fin 8) α (HeadBoundary.Record ρ η (Option Bool)) ι)
    (childClear : RawLayout markerId child) (direction : Bool) (low high terminal : HeadBoundary.Record ρ η (Option Bool))
    (header : PhysicalPacketStaging.Packet α (HeadBoundary.Record ρ η (Option Bool)) ι) (headerClear : Packet markerId header) :
    RawLayout markerId (HeadPacketLayout.active markerId bits l r tl b tr child direction low high terminal header) := by
  have attached := attachment_layout markerId terminal child childClear
  cases direction
  · exact primaryJoin_layout markerId _ _
      (primaryJoin_layout markerId _ _
        (realJoin_layout markerId _ _ _ (block_layout markerId bits l) (logical_layout markerId _ _ (block_layout markerId bits tl)))
        (bottom_layout markerId b header headerClear))
      (realJoin_layout markerId _ _ _ (realJoin_layout markerId _ _ _ (block_layout markerId bits tr) attached) (block_layout markerId bits r))
  · exact primaryJoin_layout markerId _ _
      (primaryJoin_layout markerId _ _
        (realJoin_layout markerId _ _ _ (block_layout markerId bits l) (realJoin_layout markerId _ _ _ attached (block_layout markerId bits tl)))
        (bottom_layout markerId b header headerClear))
      (realJoin_layout markerId _ _ _ (logical_layout markerId _ _ (block_layout markerId bits tr)) (block_layout markerId bits r))

theorem after_layout (markerId : ι) (bits : Fin 8 → Bool) (direction : Bool) (records : HeadBoundary.Records ρ η (Option Bool))
    (newHeader dormantHeader : PhysicalPacketStaging.Packet α (HeadBoundary.Record ρ η (Option Bool)) ι)
    (newClear : Packet markerId newHeader) (dormantClear : Packet markerId dormantHeader) :
    RawLayout markerId (HeadPacketLayout.after markerId bits direction records newHeader dormantHeader) :=
  active_layout markerId bits 0 7 4 5 6 _ (dormant_layout markerId bits 1 2 3 records.oldHigh dormantHeader dormantClear)
    (!direction) records.low records.incomingHigh records.incomingTerminal newHeader newClear

end ChaCha.Paper20261030.MarkerFreePackets

namespace ChaCha.Paper20261030.HeadPacketLayout

open ColoredStorage PhysicalPacketStaging PacketLayers

variable {α ρ ι η : Type*}

theorem retained_order (markerId : ι) (bits : Fin 8 → Bool) (direction : Bool)
    (old fresh : Structural.HeadBoundary.Records ρ η (Option Bool))
    (oldHeader incomingHeader newHeader dormantHeader : Packet α (Structural.HeadBoundary.Record ρ η (Option Bool)) ι)
    (oldPresent : bits 2 = true) (newPresent : bits 5 = true)
    (beforeContext afterContext : Source (Fin 8) (Expression α (Structural.HeadBoundary.Record ρ η (Option Bool)) ι))
    (beforeFound : before markerId bits direction old oldHeader incomingHeader = some beforeContext)
    (afterFound : after markerId bits direction fresh newHeader dormantHeader = some afterContext) :
    beforeContext.shape.leaves = afterContext.shape.leaves := by
  have oldLeaves := PacketContext.surviving_leaves List.append bits
    (ObservedHeadBlueprint.beforeContext (PacketAlignment.markerValue markerId) direction old oldHeader incomingHeader)
  have newLeaves := PacketContext.surviving_leaves List.append bits
    (ObservedHeadBlueprint.afterContext (PacketAlignment.markerValue markerId) direction fresh newHeader dormantHeader)
  rw [before_pruned markerId bits direction old oldHeader incomingHeader oldPresent newPresent beforeContext beforeFound] at oldLeaves
  rw [after_pruned markerId bits direction fresh newHeader dormantHeader oldPresent newPresent afterContext afterFound] at newLeaves
  simp only [PacketContext.leaves,Source.mapRecords_shape] at oldLeaves newLeaves
  rw [oldLeaves,newLeaves,ObservedHeadBlueprint.block_order]

end ChaCha.Paper20261030.HeadPacketLayout

namespace ChaCha.Paper20261030.MarkerFreePackets

open ColoredStorage SourcePointer Structural PhysicalPacketStaging PacketLayers

variable {α β ρ ι η : Type*}

theorem repaired_endpoint (markerId : ι) (direction : Bool) (old fresh : HeadBoundary.Records ρ η (Option Bool))
    (oldHeader incomingHeader newHeader dormantHeader : PhysicalPacketStaging.Packet α (HeadBoundary.Record ρ η (Option Bool)) ι)
    (newClear : Packet markerId newHeader) (dormantClear : Packet markerId dormantHeader)
    (blocks : Fin 8 → Source β (PhysicalPacketStaging.Packet α (HeadBoundary.Record ρ η (Option Bool)) ι))
    (before after : Source (Fin 8) (Expression α (HeadBoundary.Record ρ η (Option Bool)) ι))
    (beforeFound : HeadPacketLayout.before markerId (ObservedHeadBlueprint.bits old) direction old oldHeader incomingHeader = some before)
    (afterFound : HeadPacketLayout.after markerId (ObservedHeadBlueprint.bits old) direction fresh newHeader dormantHeader = some after)
    (initial final : Source β (Context.Cell α (HeadBoundary.Record ρ η (Option Bool)) ι))
    (stored : Reached.Stored blocks before initial) (clear : SourceRecordPredicate.Holds (Vertex markerId) initial)
    (repacked : Reached.Repacked blocks after final) (reserved : markerId ∉ final.inventory Prod.fst)
    (plan : Source (Fin 8) MixedPacketRepair.Layers) :
    SourceRecordPredicate.Holds (Vertex markerId) (MixedPacketRepair.output plan none final) := by
  have blocksClear := stored_blocks markerId blocks before initial stored clear
  have order := HeadPacketLayout.retained_order markerId (ObservedHeadBlueprint.bits old) direction old fresh
    oldHeader incomingHeader newHeader dormantHeader rfl rfl before after beforeFound afterFound
  have raw := after_layout markerId (ObservedHeadBlueprint.bits old) direction fresh newHeader dormantHeader newClear dormantClear
  rw [afterFound] at raw
  apply MixedPacketRepair.marker_free markerId plan none final
  exact repacked_clear markerId blocks after final repacked raw
    (fun key member => blocksClear key (by rw [order]; exact member)) reserved

end ChaCha.Paper20261030.MarkerFreePackets
