import ChaCha.Paper20261030.MultiSourcePacketPrefix
import ChaCha.Paper20261030.SourceInorderLabels

set_option autoImplicit false

/-! Attaching an enclosing packet changes no physical vertex label or
finger. These equalities relate raw component entry witnesses to the
actual configuration carrying its parent's packet prefix. -/

namespace ChaCha.Paper20261030.MultiSourcePacketPrefix

open ColoredStorage SourcePointer MultiSourceProgram PhysicalPacketStaging PacketLayers

variable {α β ρ ι F : Type*} [DecidableEq F]

theorem attached_identifier_tree (saved : Packet α ρ ι) (tree : Source β (Context.Cell α ρ ι))
    (outside : List (Frame β (Context.Cell α ρ ι))) (config : Configuration F β (Context.Cell α ρ ι))
    (represented : config.tree = plug tree outside) :
    (attached saved tree outside config).tree.mapRecords Prod.fst = config.tree.mapRecords Prod.fst := by
  rw [represented]
  exact write_labels_tree Prod.fst ⟨tree,outside⟩ (tree.rootRecord.1,saved++tree.rootRecord.2) rfl

theorem attached_inorder (saved : Packet α ρ ι) (tree : Source β (Context.Cell α ρ ι))
    (outside : List (Frame β (Context.Cell α ρ ι))) (config : Configuration F β (Context.Cell α ρ ι))
    (represented : config.tree = plug tree outside) :
    (attached saved tree outside config).tree.inorderLabels Prod.fst = config.tree.inorderLabels Prod.fst := by
  have same := congrArg (Source.inorderLabels id) (attached_identifier_tree saved tree outside config represented)
  simpa only [Source.inorderLabels_map,Function.comp_def,id_eq] using same

theorem attached_inventory (saved : Packet α ρ ι) (tree : Source β (Context.Cell α ρ ι))
    (outside : List (Frame β (Context.Cell α ρ ι))) (config : Configuration F β (Context.Cell α ρ ι))
    (represented : config.tree = plug tree outside) :
    (attached saved tree outside config).tree.inventory Prod.fst = config.tree.inventory Prod.fst := by
  have same := congrArg (Source.inventory id) (attached_identifier_tree saved tree outside config represented)
  simpa only [mapRecords_inventory,Function.comp_def,id_eq] using same

theorem attached_fingerLabel (saved : Packet α ρ ι) (tree : Source β (Context.Cell α ρ ι))
    (outside : List (Frame β (Context.Cell α ρ ι))) (config : Configuration F β (Context.Cell α ρ ι))
    (represented : config.tree = plug tree outside) (finger : F) :
    fingerLabel Prod.fst (attached saved tree outside config) finger = fingerLabel Prod.fst config finger :=
  fingerLabel_congr Prod.fst finger (attached_identifier_tree saved tree outside config represented) rfl

end ChaCha.Paper20261030.MultiSourcePacketPrefix
