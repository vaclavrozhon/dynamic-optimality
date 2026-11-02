import ChaCha.Paper20261030.LocalEnclosingPacketOperation
import ChaCha.Paper20261030.CanonicalComponentUniqueness

set_option autoImplicit false

/-!
# Physical invariants after transferring an enclosing prefix

Restoring a prefix changes no immutable id. Its real packets are aligned
to the reached new root, and the parent edit changes only child-reference
fields. Thus the whole-tree invariants survive both actual wrapper phases.
Canonical correspondence of the enclosing logical layout is an additional
obligation beyond these pointwise physical invariants.
-/

namespace ChaCha.Paper20261030.EnclosingPacketOperation

open ColoredStorage SourcePointer SourceLocalProgram Structural PhysicalPacketStaging PacketLayers

variable {α β ρ ι : Type*} [DecidableEq ι]

def output (packet : Packet α ρ ι) (oldId : ι) (current : Cursor β (Context.Cell α ρ ι)) :
    Cursor β (Context.Cell α ρ ι) :=
  ⟨PacketPrefixTransfer.output packet current.focus,match current.ancestors with
    | [] => []
    | first::rest => PacketParentRepair.frame oldId current.focus.rootRecord.1 first::rest⟩

theorem inventory (packet : Packet α ρ ι) (oldId : ι) (current : Cursor β (Context.Cell α ρ ι)) :
    (output packet oldId current).tree.inventory Prod.fst = current.tree.inventory Prod.fst := by
  obtain ⟨source,outside⟩ := current
  cases outside with
  | nil => exact PacketPrefixTransfer.identifiers packet source
  | cons first rest =>
    exact (PacketParentRepair.inventory oldId source.rootRecord.1 (PacketPrefixTransfer.output packet source) first rest).trans
      (plug_inventory_congr Prod.fst (PacketPrefixTransfer.identifiers packet source) (first::rest))

theorem preserves (predicate : Context.Cell α ρ ι → Prop) (packet : Packet α ρ ι) (oldId : ι)
    (current : Cursor β (Context.Cell α ρ ι))
    (atRoot : SourceRecordPredicate.Holds predicate current.focus →
      SourceRecordPredicate.Holds predicate (PacketPrefixTransfer.output packet current.focus))
    (atParent : ∀ record, predicate record → predicate (PacketParentRepair.edit oldId current.focus.rootRecord.1 record))
    (valid : SourceRecordPredicate.Holds predicate current.tree) :
    SourceRecordPredicate.Holds predicate (output packet oldId current).tree := by
  have restored := SourceRecordPredicate.context predicate current.focus (PacketPrefixTransfer.output packet current.focus)
    current.ancestors atRoot valid
  cases outside : current.ancestors with
  | nil => simpa only [output,Cursor.tree,outside,plug] using restored
  | cons first rest =>
    rw [outside] at restored
    simp only [output,Cursor.tree,outside]
    exact PacketParentRepair.preserves predicate oldId current.focus.rootRecord.1 atParent
      (PacketPrefixTransfer.output packet current.focus) first rest restored

theorem alignment (markerId : ι) (packet : Packet α ρ ι) (oldId : ι)
    (current : Cursor β (Context.Cell α ρ ι))
    (valid : SourceRecordPredicate.Holds (PacketAlignment.Predicate markerId) current.tree) :
    SourceRecordPredicate.Holds (PacketAlignment.Predicate markerId) (output packet oldId current).tree :=
  preserves _ packet oldId current (PacketPrefixTransfer.output_alignment markerId packet current.focus)
    (PacketParentRepair.alignment markerId oldId current.focus.rootRecord.1) valid

theorem clear (markerId : ι) (packet : Packet α ρ ι) (oldId : ι)
    (current : Cursor β (Context.Cell α ρ ι)) (reserved : markerId ∉ current.tree.inventory Prod.fst)
    (valid : SourceRecordPredicate.Holds (MarkerFreePackets.Vertex markerId) current.tree) :
    SourceRecordPredicate.Holds (MarkerFreePackets.Vertex markerId) (output packet oldId current).tree := by
  have ordinary : current.focus.rootRecord.1 ≠ markerId := by
    intro equal
    apply reserved
    rw [← equal]
    exact Multiset.mem_of_le (inventory_le_plug Prod.fst current.focus current.ancestors) (root_mem_inventory Prod.fst current.focus)
  exact preserves _ packet oldId current (PacketPrefixTransfer.output_clear markerId packet current.focus ordinary)
    (PacketParentRepair.clear markerId oldId current.focus.rootRecord.1) valid

theorem valid (markerId : ι) (packet : Packet α ρ ι) (oldId : ι)
    (current : Cursor β (Context.Cell α ρ ι)) (reserved : markerId ∉ current.tree.inventory Prod.fst)
    (valid : CanonicalComponentUniqueness.Valid markerId current.tree) :
    CanonicalComponentUniqueness.Valid markerId (output packet oldId current).tree ∧
      markerId ∉ (output packet oldId current).tree.inventory Prod.fst := by
  refine ⟨⟨alignment markerId packet oldId current valid.1,clear markerId packet oldId current reserved valid.2.1,?_⟩,?_⟩
  · rw [inventory]
    exact valid.2.2
  · rw [inventory]
    exact reserved

theorem run {σ : Type*} (packet : Packet α ρ ι) (kernel : Program σ (Context.Cell α ρ ι)) (initial last : σ)
    (before after : Cursor β (Context.Cell α ρ ι)) {reads cost}
    (execution : Run kernel initial before last after reads cost) (halted : kernel last = .halt)
    (sameEmpty : after.ancestors.isEmpty = before.ancestors.isEmpty)
    (unique : (after.tree.inventory Prod.fst).Nodup) :
    ∃ observed total, Run (program packet.length (!before.ancestors.isEmpty) kernel initial) (.transferring .start)
      ⟨PacketPrefixTransfer.attach packet before.focus,before.ancestors⟩ (.done last)
      (output packet before.focus.rootRecord.1 after) observed total ∧ total ≤ cost+11 := by
  obtain ⟨before,outside⟩ := before
  obtain ⟨after,finalOutside⟩ := after
  cases outside with
  | nil => cases finalOutside with
    | nil =>
      obtain ⟨observed,actual⟩ := root packet kernel initial last before after execution halted
      exact ⟨observed,cost+4,actual,by omega⟩
    | cons => cases sameEmpty
  | cons first rest => cases finalOutside with
    | nil => cases sameEmpty
    | cons finalFirst finalRest =>
      exact nested packet kernel initial last before after (first::rest) finalFirst finalRest execution halted unique

theorem execute {σ F : Type*} [DecidableEq F] (finger : F) (markerId : ι)
    (packet : Packet α ρ ι) (kernel : Program σ (Context.Cell α ρ ι)) (initial last : σ)
    (before after : Cursor β (Context.Cell α ρ ι)) {reads cost}
    (execution : Run kernel initial before last after reads cost) (halted : kernel last = .halt)
    (sameEmpty : after.ancestors.isEmpty = before.ancestors.isEmpty)
    (reserved : markerId ∉ after.tree.inventory Prod.fst)
    (physical : CanonicalComponentUniqueness.Valid markerId after.tree)
    (config : MultiSourceProgram.Configuration F β (Context.Cell α ρ ι))
    (located : MultiSourceSingleCursor.Represents finger
      ⟨PacketPrefixTransfer.attach packet before.focus,before.ancestors⟩ config)
    (wellFormed : MultiSourceProgram.WellFormed config) :
    ∃ finalConfig observed total,
      MultiSourceProgram.Run (MultiSourceSingleCursor.program
        (program packet.length (!before.ancestors.isEmpty) kernel initial) finger)
        (some (.transferring .start)) config (some (.done last)) finalConfig observed total ∧
      MultiSourceSingleCursor.Represents finger (output packet before.focus.rootRecord.1 after) finalConfig ∧
      finalConfig.tree.inventory Prod.fst = after.tree.inventory Prod.fst ∧
      CanonicalComponentUniqueness.Valid markerId finalConfig.tree ∧
      markerId ∉ finalConfig.tree.inventory Prod.fst ∧
      MultiSourceProgram.WellFormed finalConfig ∧ total ≤ cost+11 := by
  obtain ⟨observed,total,actual,bound⟩ := run packet kernel initial last before after execution halted sameEmpty physical.2.2
  obtain ⟨finalConfig,compiled,positioned⟩ := MultiSourceSingleCursor.compile_run _ finger actual config located
  obtain ⟨finalPhysical,finalReserved⟩ := valid markerId packet before.focus.rootRecord.1 after reserved physical
  refine ⟨finalConfig,_,total,compiled,positioned,?_,?_,?_,compiled.wellFormed wellFormed,bound⟩
  · rw [positioned.1,inventory]
  · rw [positioned.1]
    exact finalPhysical
  · rw [positioned.1]
    exact finalReserved

end ChaCha.Paper20261030.EnclosingPacketOperation
