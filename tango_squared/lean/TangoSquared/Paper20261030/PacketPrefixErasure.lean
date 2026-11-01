import TangoSquared.Paper20261030.AttachedPacketIdentifiers
import TangoSquared.Paper20261030.CanonicalComponentUniqueness
import TangoSquared.Paper20261030.RetainedSubtreeHandoff

set_option autoImplicit false

/-! A ghost entry witness obtained by removing a reached enclosing packet.
The actual next controller still starts in the unchanged attached tree
and pays for its prefix read and write. These lemmas do not add a free
runtime edit: `reattach` identifies that controller's input exactly. -/

namespace TangoSquared.Paper20261030.PacketPrefixErasure

open ColoredStorage SourcePointer SourcePositions Structural MultiSourceProgram PhysicalPacketStaging PacketLayers

variable {α β ρ ι F : Type*} [DecidableEq F]

def stripped (current : Cursor β (Context.Cell α ρ ι)) (packet : Packet α ρ ι)
    (config : Configuration F β (Context.Cell α ρ ι)) : Configuration F β (Context.Cell α ρ ι) :=
  ⟨(SubtreeMetadata.replacePayload current packet).tree,config.fingers⟩

private theorem set_twice {δ : Type*} (tree : Source β δ) (first last : δ) :
    (tree.setRoot first).setRoot last = tree.setRoot last := by cases tree <;> rfl

private theorem root_set {δ : Type*} (tree : Source β δ) (record : δ) :
    (tree.setRoot record).rootRecord = record := by cases tree <;> rfl

private theorem set_own {δ : Type*} (tree : Source β δ) : tree.setRoot tree.rootRecord = tree := by cases tree <;> rfl

theorem reattach_cursor (current : Cursor β (Context.Cell α ρ ι)) (saved packet : Packet α ρ ι)
    (split : current.focus.rootRecord.2 = saved ++ packet) :
    (⟨PacketPrefixTransfer.attach saved (SubtreeMetadata.replacePayload current packet).focus,
      current.ancestors⟩ : Cursor β (Context.Cell α ρ ι)) = current := by
  have joined : (current.focus.rootRecord.1,saved++packet) = current.focus.rootRecord := by rw [← split]
  simp only [PacketPrefixTransfer.attach,SubtreeMetadata.replacePayload,root_set,set_twice,joined,set_own]

theorem reattach (current : Cursor β (Context.Cell α ρ ι)) (saved packet : Packet α ρ ι)
    (config : Configuration F β (Context.Cell α ρ ι)) (tree : config.tree = current.tree)
    (split : current.focus.rootRecord.2 = saved ++ packet) :
    MultiSourcePacketPrefix.attached saved (SubtreeMetadata.replacePayload current packet).focus current.ancestors
      (stripped current packet config) = config := by
  have joined : (current.focus.rootRecord.1,saved++packet) = current.focus.rootRecord := by
    rw [← split]
  cases config with
  | mk source fingers =>
    change Configuration.mk (plug (PacketPrefixTransfer.attach saved _) current.ancestors) fingers = _
    simp only [PacketPrefixTransfer.attach,SubtreeMetadata.replacePayload,root_set,set_twice,joined,set_own]
    exact congrArg (fun t => Configuration.mk t fingers) tree.symm

theorem represented (finger : F) (current : Cursor β (Context.Cell α ρ ι)) (packet : Packet α ρ ι)
    (config : Configuration F β (Context.Cell α ρ ι))
    (atRoot : MultiSourceSingleCursor.Represents finger current config) :
    MultiSourceSingleCursor.Represents finger (SubtreeMetadata.replacePayload current packet) (stripped current packet config) :=
  ⟨rfl,atRoot.2⟩

theorem identifier_tree (current : Cursor β (Context.Cell α ρ ι)) (packet : Packet α ρ ι)
    (config : Configuration F β (Context.Cell α ρ ι)) (tree : config.tree = current.tree) :
    (stripped current packet config).tree.mapRecords Prod.fst = config.tree.mapRecords Prod.fst := by
  rw [tree]
  exact write_labels_tree Prod.fst current (current.focus.rootRecord.1,packet) rfl

theorem inventory (current : Cursor β (Context.Cell α ρ ι)) (packet : Packet α ρ ι)
    (config : Configuration F β (Context.Cell α ρ ι)) (tree : config.tree = current.tree) :
    (stripped current packet config).tree.inventory Prod.fst = config.tree.inventory Prod.fst := by
  have same := congrArg (Source.inventory id) (identifier_tree current packet config tree)
  simpa only [mapRecords_inventory,Function.comp_def,id_eq] using same

theorem inorder (current : Cursor β (Context.Cell α ρ ι)) (packet : Packet α ρ ι)
    (config : Configuration F β (Context.Cell α ρ ι)) (tree : config.tree = current.tree) :
    (stripped current packet config).tree.inorderLabels Prod.fst = config.tree.inorderLabels Prod.fst := by
  have same := congrArg (Source.inorderLabels id) (identifier_tree current packet config tree)
  simpa only [Source.inorderLabels_map,Function.comp_def,id_eq] using same

theorem fingerLabel (current : Cursor β (Context.Cell α ρ ι)) (packet : Packet α ρ ι)
    (config : Configuration F β (Context.Cell α ρ ι)) (tree : config.tree = current.tree) (finger : F) :
    MultiSourceProgram.fingerLabel Prod.fst (stripped current packet config) finger =
      MultiSourceProgram.fingerLabel Prod.fst config finger :=
  fingerLabel_congr Prod.fst finger (identifier_tree current packet config tree) rfl

theorem root_id (current : Cursor β (Context.Cell α ρ ι)) (packet : Packet α ρ ι) :
    (SubtreeMetadata.replacePayload current packet).focus.rootRecord.1 = current.focus.rootRecord.1 := by
  simp only [SubtreeMetadata.replacePayload,root_set]

theorem wellFormed (current : Cursor β (Context.Cell α ρ ι)) (packet : Packet α ρ ι)
    (config : Configuration F β (Context.Cell α ρ ι)) (tree : config.tree = current.tree) (valid : WellFormed config) :
    WellFormed (stripped current packet config) :=
  write_wellFormed config valid current tree.symm (current.focus.rootRecord.1,packet)

theorem physical (markerId : ι) (current : Cursor β (Context.Cell α ρ ι)) (saved packet : Packet α ρ ι)
    (config : Configuration F β (Context.Cell α ρ ι)) (tree : config.tree = current.tree)
    (split : current.focus.rootRecord.2 = saved ++ packet)
    (valid : CanonicalComponentUniqueness.Valid markerId config.tree) :
    CanonicalComponentUniqueness.Valid markerId (stripped current packet config).tree := by
  have aligned := SourceRecordPredicate.focused (PacketAlignment.Predicate markerId) current (tree ▸ valid.1)
  have clear := SourceRecordPredicate.focused (MarkerFreePackets.Vertex markerId) current (tree ▸ valid.2.1)
  change PacketAlignment.Aligned markerId current.focus.rootRecord.1 current.focus.rootRecord.2 at aligned
  change MarkerFreePackets.Packet markerId current.focus.rootRecord.2 at clear
  rw [split] at aligned clear
  refine ⟨?_,?_,?_⟩
  · exact SourceRecordPredicate.write (PacketAlignment.Predicate markerId) current _ (tree ▸ valid.1)
      (fun item member => aligned item (List.mem_append_right saved member))
  · exact SourceRecordPredicate.write (MarkerFreePackets.Vertex markerId) current _ (tree ▸ valid.2.1)
      (fun item member => clear item (List.mem_append_right saved member))
  · rw [inventory current packet config tree]
    exact valid.2.2

theorem payload (current : Cursor β (Context.Cell α ρ ι)) (saved : Packet α ρ ι) (view : Source β (Packet α ρ ι))
    (erases : current.focus.mapRecords Prod.snd = view.setRoot (saved++view.rootRecord)) :
    (SubtreeMetadata.replacePayload current view.rootRecord).focus.mapRecords Prod.snd = view := by
  simp only [SubtreeMetadata.replacePayload,Source.mapRecords_setRoot,erases,set_twice,set_own]

theorem root_packet (current : Cursor β (Context.Cell α ρ ι)) (saved : Packet α ρ ι) (view : Source β (Packet α ρ ι))
    (erases : current.focus.mapRecords Prod.snd = view.setRoot (saved++view.rootRecord)) :
    current.focus.rootRecord.2 = saved++view.rootRecord := by
  simpa only [Source.mapRecords_root,root_set] using congrArg Source.rootRecord erases

end TangoSquared.Paper20261030.PacketPrefixErasure
