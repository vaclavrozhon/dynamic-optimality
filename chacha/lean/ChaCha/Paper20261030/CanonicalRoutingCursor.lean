import ChaCha.Paper20261030.CanonicalRoutingParentRepair
import ChaCha.Paper20261030.CursorRepresentationShapes

set_option autoImplicit false

/-! The physical cursor at a tagged routing port. Its ancestor context
includes canonical structural fields, optional mirroring, singleton
packets, and opaque grafted payloads. The cursor is a proof witness; its
whole tree is exactly the existing canonical routing encoding. -/

namespace ChaCha.Paper20261030.CanonicalRoutingCursor

open ColoredStorage SourcePointer Structural PhysicalPacketStaging CanonicalPacketLayerViews

variable {α β ρ ι : Type*}

def frame (payload : α → Source β (Packet α ρ ι)) (reverse : Bool)
    (current : Frame α (PhysicalForestMetadata.Record ρ ι)) : Frame β (Packet α ρ ι) :=
  SourcePayloads.frame payload ((if reverse then current.mirror else current).mapRecords (fun record => [.real record]))

def cursor (payload : α → Source β (Packet α ρ ι)) (reverse : Bool)
    (current : Cursor α (ι × List ρ)) : Cursor β (Packet α ρ ι) :=
  let annotated := Structural.cursor Prod.fst (fun _ => (() : Unit)) current
  SourcePayloads.cursor payload ((if reverse then annotated.mirror else annotated).mapRecords (fun record => [.real record]))

theorem tree (payload : α → Source β (Packet α ρ ι)) (reverse : Bool) (current : Cursor α (ι × List ρ)) :
    (cursor payload reverse current).tree = routing payload reverse none current.tree := by
  cases reverse <;>
    simp only [cursor,Bool.false_eq_true,if_false,if_true,Cursor.payload_tree,Cursor.mapRecords_tree,
      Cursor.mirror_tree,Structural.cursor_tree,routing]

theorem ancestors (payload : α → Source β (Packet α ρ ι)) (reverse : Bool) (current : Cursor α (ι × List ρ)) :
    (cursor payload reverse current).ancestors =
      (Structural.frames Prod.fst (fun _ => (() : Unit)) current.focus current.ancestors).map (frame payload reverse) := by
  cases reverse <;> simp only [cursor,Bool.false_eq_true,if_false,if_true,SourcePayloads.cursor,
    Cursor.mapRecords,Cursor.mirror,Structural.cursor,List.map_map,Function.comp_def,frame] <;> rfl

theorem leaf (payload : α → Source β (Packet α ρ ι)) (reverse : Bool)
    (key : α) (value : ι × List ρ) (outside : List (Frame α (ι × List ρ))) :
    (cursor payload reverse ⟨.leaf key value,outside⟩).focus =
      (payload key).setRoot (some (.real (value,fields Prod.fst (fun _ => (() : Unit))
        (parentId Prod.fst outside) (.leaf key value))) :: none :: (payload key).rootRecord) := by
  cases reverse <;> rfl

def repairFrame [DecidableEq ι] (old fresh : ι) : Frame β (Packet α ρ ι) → Frame β (Packet α ρ ι)
  | .left record sibling => .left (record.map (PacketParentRepair.entry old fresh)) sibling
  | .right sibling record => .right sibling (record.map (PacketParentRepair.entry old fresh))

theorem frame_repair [DecidableEq ι] (payload : α → Source β (Packet α ρ ι)) (reverse : Bool)
    (old fresh : ι) (current : Frame α (PhysicalForestMetadata.Record ρ ι)) :
    frame payload reverse (CanonicalRoutingParentRepair.frame old fresh current) =
      repairFrame old fresh (frame payload reverse current) := by
  cases current <;> cases reverse <;> rfl

theorem erase_repair [DecidableEq ι] (old fresh : ι) (current : Frame β (PacketLayers.Context.Cell α ρ ι)) :
    (PacketParentRepair.frame old fresh current).mapRecords Prod.snd =
      repairFrame old fresh (current.mapRecords Prod.snd) := by
  cases current <;> rfl

/-- With the same opaque payload function, the full physical ancestor
context changes by exactly the executed immediate-parent packet edit. -/
theorem parent_repair [DecidableEq ι] (payload : α → Source β (Packet α ρ ι)) (reverse : Bool)
    (before after : Source α (ι × List ρ)) (outside : List (Frame α (ι × List ρ)))
    (colors : before.support (fun _ => (() : Unit)) = after.support (fun _ => (() : Unit)))
    (unique : ((plug before outside).inventory Prod.fst).Nodup) :
    (cursor payload reverse ⟨after,outside⟩).ancestors =
      match (cursor payload reverse ⟨before,outside⟩).ancestors with
      | [] => []
      | first::rest => repairFrame before.rootRecord.1 after.rootRecord.1 first :: rest := by
  rw [ancestors,CanonicalRoutingParentRepair.frames before after outside colors unique,ancestors]
  cases Structural.frames Prod.fst (fun _ => (() : Unit)) before outside with
  | nil => rfl
  | cons first rest => simp only [List.map_cons,frame_repair]

end ChaCha.Paper20261030.CanonicalRoutingCursor
