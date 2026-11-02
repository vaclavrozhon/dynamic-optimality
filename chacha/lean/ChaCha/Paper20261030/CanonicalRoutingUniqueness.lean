import ChaCha.Paper20261030.CanonicalMixedPacketRepair

set_option autoImplicit false

/-!
# Physical identifier uniqueness of canonical routing witnesses

Every routing vertex occupies a distinct actual vertex of its expanded
physical tree. Payloads may contain additional vertices, and right wings
reverse the physical child order. Alignment and absence of temporary
markers identify each stored routing id with its actual vertex id.
-/

namespace ChaCha.Paper20261030.CanonicalRoutingUniqueness

open ColoredStorage SourcePointer Structural PhysicalPacketStaging PacketLayers
open CanonicalPacketLayerViews

variable {α β ρ ι : Type*}

theorem inventory_le (markerId : ι) (payload : α → Source β (Packet α ρ ι))
    (reverse : Bool) (parent : Option ι) (tagged : Tagged α ρ ι)
    (source : Source β (Context.Cell α ρ ι))
    (erases : source.mapRecords Prod.snd = routing payload reverse parent tagged)
    (aligned : SourceRecordPredicate.Holds (PacketAlignment.Predicate markerId) source)
    (clear : SourceRecordPredicate.Holds (MarkerFreePackets.Vertex markerId) source) :
    tagged.inventory Prod.fst ≤ source.inventory Prod.fst := by
  induction tagged generalizing source parent with
  | leaf key record =>
    have rootId := CanonicalMixedPacketRepair.routing_root_id markerId payload reverse parent
      (.leaf key record) source erases
      (SourceRecordPredicate.root _ _ aligned) (SourceRecordPredicate.root _ _ clear)
    simp only [Source.inventory_leaf]
    change source.rootRecord.1 = record.1 at rootId
    rw [← rootId]
    exact Multiset.singleton_le.mpr (root_mem_inventory Prod.fst source)
  | fork record left right ihl ihr =>
    have rootId := CanonicalMixedPacketRepair.routing_root_id markerId payload reverse parent
      (.fork record left right) source erases
      (SourceRecordPredicate.root _ _ aligned) (SourceRecordPredicate.root _ _ clear)
    cases record with
    | mk ident records =>
      rw [CanonicalPacketLayerViews.fork] at erases
      cases source with
      | leaf => cases erases
      | fork cell physicalLeft physicalRight =>
        simp only [Source.mapRecords,Source.fork.injEq] at erases
        obtain ⟨_,leftEq,rightEq⟩ := erases
        obtain ⟨_,leftAligned,rightAligned⟩ := (SourceRecordPredicate.fork _ _ _ _).mp aligned
        obtain ⟨_,leftClear,rightClear⟩ := (SourceRecordPredicate.fork _ _ _ _).mp clear
        change cell.1 = ident at rootId
        simp only [Source.inventory_fork,rootId,add_assoc]
        cases reverse with
        | false =>
          exact add_le_add le_rfl (add_le_add (ihl _ _ leftEq leftAligned leftClear)
            (ihr _ _ rightEq rightAligned rightClear))
        | true =>
          have hl := ihl _ _ rightEq rightAligned rightClear
          have hr := ihr _ _ leftEq leftAligned leftClear
          rw [add_comm (left.inventory Prod.fst) (right.inventory Prod.fst)]
          exact add_le_add le_rfl (add_le_add hr hl)

theorem unique (markerId : ι) (payload : α → Source β (Packet α ρ ι))
    (reverse : Bool) (parent : Option ι) (tagged : Tagged α ρ ι)
    (source : Source β (Context.Cell α ρ ι))
    (erases : source.mapRecords Prod.snd = routing payload reverse parent tagged)
    (aligned : SourceRecordPredicate.Holds (PacketAlignment.Predicate markerId) source)
    (clear : SourceRecordPredicate.Holds (MarkerFreePackets.Vertex markerId) source)
    (ids : (source.inventory Prod.fst).Nodup) : (tagged.inventory Prod.fst).Nodup :=
  Multiset.nodup_of_le (inventory_le markerId payload reverse parent tagged source erases aligned clear) ids

end ChaCha.Paper20261030.CanonicalRoutingUniqueness
