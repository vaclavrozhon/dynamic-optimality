import TangoSquared.Paper20261030.MultiSourceNestedWriteLabels
import TangoSquared.Paper20261030.CanonicalComponentUniqueness
import TangoSquared.Paper20261030.VirtualHeaderWriteLabels

set_option autoImplicit false

/-! Packet labels characterize agreement with the actual physical
vertex and absence of temporary real-packet markers. Virtual headers
and delimiters carry no physical identifier. -/

namespace TangoSquared.Paper20261030.PacketWriteLabels

open ColoredStorage SourcePointer PhysicalPacketStaging PacketLayers

variable {α β ρ ι : Type*}

def label : Option (Datum α ρ ι) → Option (Option ι) :=
  Option.map (VirtualHeaderController.physicalLabel (fun record => record.1.1))

def Entry (markerId vertexId : ι) : Option (Option ι) → Prop
  | some (some storedId) => (storedId = markerId ∨ storedId = vertexId) ∧ storedId ≠ markerId
  | _ => True

def Relation (markerId vertexId : ι) (labels : List (Option (Option ι))) : Prop :=
  ∀ item ∈ labels, Entry markerId vertexId item

theorem entry_iff (markerId vertexId : ι) (item : Option (Datum α ρ ι)) :
    Entry markerId vertexId (label item) ↔
      PacketAlignment.Entry markerId vertexId item ∧ MarkerFreePackets.Entry markerId item := by
  cases item with
  | none => exact ⟨fun _ => ⟨trivial,trivial⟩,fun _ => trivial⟩
  | some datum => cases datum with
    | header => exact ⟨fun _ => ⟨trivial,trivial⟩,fun _ => trivial⟩
    | real record => rfl

theorem relation_iff (markerId vertexId : ι) (packet : Packet α ρ ι) :
    Relation markerId vertexId (packet.map label) ↔
      PacketAlignment.Aligned markerId vertexId packet ∧ MarkerFreePackets.Packet markerId packet := by
  constructor
  · intro valid
    constructor
    · intro item member
      exact ((entry_iff markerId vertexId item).mp (valid _ (List.mem_map.mpr ⟨item,member,rfl⟩))).1
    · intro item member
      exact ((entry_iff markerId vertexId item).mp (valid _ (List.mem_map.mpr ⟨item,member,rfl⟩))).2
  · rintro ⟨aligned,clear⟩ item member
    obtain ⟨original,originalMember,rfl⟩ := List.mem_map.mp member
    exact (entry_iff markerId vertexId original).mpr ⟨aligned original originalMember,clear original originalMember⟩

theorem holds_iff (markerId : ι) (source : Source β (Context.Cell α ρ ι)) :
    SourceRecordPredicate.Holds (fun record => Relation markerId record.1 (record.2.map label)) source ↔
      SourceRecordPredicate.Holds (PacketAlignment.Predicate markerId) source ∧
      SourceRecordPredicate.Holds (MarkerFreePackets.Vertex markerId) source := by
  constructor
  · intro valid
    exact ⟨fun record member => ((relation_iff markerId record.1 record.2).mp (valid record member)).1,
      fun record member => ((relation_iff markerId record.1 record.2).mp (valid record member)).2⟩
  · rintro ⟨aligned,clear⟩ record member
    exact (relation_iff markerId record.1 record.2).mpr ⟨aligned record member,clear record member⟩

end TangoSquared.Paper20261030.PacketWriteLabels
