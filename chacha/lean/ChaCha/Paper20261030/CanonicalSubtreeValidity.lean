import ChaCha.Paper20261030.CanonicalComponentUniqueness
import ChaCha.Paper20261030.MultiSourceRecordMap

set_option autoImplicit false

/-! Canonical packet validity descends to an actual cursor's focus.
An erased subtree witness can be lifted to such a cursor without any
runtime search or additional identifier-uniqueness assumption. -/

namespace ChaCha.Paper20261030.CanonicalComponentUniqueness

open ColoredStorage SourcePointer Structural PhysicalPacketStaging PacketLayers

variable {α β ρ ι : Type*}

theorem Valid.focused (markerId : ι) (current : Cursor β (Context.Cell α ρ ι))
    (valid : Valid markerId current.tree) : Valid markerId current.focus :=
  ⟨fun record member => valid.1 record (Multiset.mem_of_le (inventory_le_plug id current.focus current.ancestors) member),
    fun record member => valid.2.1 record (Multiset.mem_of_le (inventory_le_plug id current.focus current.ancestors) member),
    Multiset.nodup_of_le (inventory_le_plug Prod.fst current.focus current.ancestors) valid.2.2⟩

theorem realized_focus (markerId : ι) (source : Source β (Context.Cell α ρ ι))
    (valid : Valid markerId source) (view : Cursor β (Packet α ρ ι))
    (erases : source.mapRecords Prod.snd = view.tree) : Realized markerId (some view.focus) := by
  have reached : SourcePositions.locate (source.mapRecords Prod.snd) (SourcePositions.address view) = some view := by
    rw [erases]
    exact SourcePositions.locate_cursor view
  obtain ⟨current,located,same⟩ := SourcePositions.lift_locate Prod.snd source (SourcePositions.address view) view reached
  have tree := SourcePositions.locate_tree located
  intro focus equal
  refine ⟨current.focus,?_,Valid.focused markerId current ?_⟩
  · exact (congrArg Cursor.focus same).trans (Option.some.inj equal)
  · rw [tree]
    exact valid

end ChaCha.Paper20261030.CanonicalComponentUniqueness
