import ChaCha.Paper20261030.CanonicalEnclosingPackets
import ChaCha.Paper20261030.StructuralCursor

set_option autoImplicit false

/-! Replacing a routing port changes only its immediate parent's child
identifier. This identifies the executed packet repair with canonical
structural annotation, rather than merely proving packet/id alignment.
All routing contexts in this file are representation witnesses. -/

namespace ChaCha.Paper20261030.CanonicalRoutingParentRepair

open ColoredStorage SourcePointer Structural PhysicalPacketStaging

variable {α ρ ι : Type*} [DecidableEq ι]

abbrev Record (ρ ι : Type*) := PhysicalForestMetadata.Record ρ ι

def record (old fresh : ι) (value : Record ρ ι) : Record ρ ι :=
  (value.1,{value.2 with children := value.2.children.map (fun pair => (PacketParentRepair.child old fresh pair.1,PacketParentRepair.child old fresh pair.2))})

def frame (old fresh : ι) : Frame α (Record ρ ι) → Frame α (Record ρ ι)
  | .left value sibling => .left (record old fresh value) sibling
  | .right sibling value => .right sibling (record old fresh value)

theorem real_entry (old fresh : ι) (value : Record ρ ι) :
    PacketParentRepair.entry (α := α) old fresh (some (.real value)) = some (.real (record old fresh value)) := rfl

theorem left_record (parent : Option ι) (value : ι × List ρ)
    (before after sibling : Source α (ι × List ρ))
    (colors : before.support (fun _ => (() : Unit)) = after.support (fun _ => (() : Unit)))
    (different : sibling.rootRecord.1 ≠ before.rootRecord.1) :
    record before.rootRecord.1 after.rootRecord.1
      (value,fields Prod.fst (fun _ => (() : Unit)) parent (.fork value before sibling)) =
      (value,fields Prod.fst (fun _ => (() : Unit)) parent (.fork value after sibling)) := by
  simp only [record,fields,descriptor,Source.support,Option.map_some,PacketParentRepair.child,different,if_false,if_true,colors]

theorem right_record (parent : Option ι) (value : ι × List ρ)
    (before after sibling : Source α (ι × List ρ))
    (colors : before.support (fun _ => (() : Unit)) = after.support (fun _ => (() : Unit)))
    (different : sibling.rootRecord.1 ≠ before.rootRecord.1) :
    record before.rootRecord.1 after.rootRecord.1
      (value,fields Prod.fst (fun _ => (() : Unit)) parent (.fork value sibling before)) =
      (value,fields Prod.fst (fun _ => (() : Unit)) parent (.fork value sibling after)) := by
  simp only [record,fields,descriptor,Source.support,Option.map_some,PacketParentRepair.child,different,if_false,if_true,colors]

/-- Canonical annotations outside a changed subtree agree exactly with
repairing the first old annotated frame. Higher ancestors are unchanged. -/
theorem frames (before after : Source α (ι × List ρ)) (outside : List (Frame α (ι × List ρ)))
    (colors : before.support (fun _ => (() : Unit)) = after.support (fun _ => (() : Unit)))
    (unique : ((plug before outside).inventory Prod.fst).Nodup) :
    Structural.frames Prod.fst (fun _ => (() : Unit)) after outside =
      match Structural.frames Prod.fst (fun _ => (() : Unit)) before outside with
      | [] => []
      | first::rest => frame before.rootRecord.1 after.rootRecord.1 first :: rest := by
  cases outside with
  | nil => rfl
  | cons first rest =>
    cases first with
    | left value sibling =>
      have localUnique : ((Source.fork value before sibling).inventory Prod.fst).Nodup :=
        Multiset.nodup_of_le (inventory_le_plug Prod.fst (.fork value before sibling) rest) unique
      have different := (child_ids_distinct Prod.fst value before sibling localUnique).symm
      have above := Structural.frames_congr Prod.fst (fun _ => (() : Unit))
        (before := .fork value before sibling) (after := .fork value after sibling) rfl
        (by simp only [Source.support,colors]) rest
      simp only [Structural.frames,frame,left_record _ _ _ _ _ colors different,above]
    | right sibling value =>
      have localUnique : ((Source.fork value sibling before).inventory Prod.fst).Nodup :=
        Multiset.nodup_of_le (inventory_le_plug Prod.fst (.fork value sibling before) rest) unique
      have different := child_ids_distinct Prod.fst value sibling before localUnique
      have above := Structural.frames_congr Prod.fst (fun _ => (() : Unit))
        (before := .fork value sibling before) (after := .fork value sibling after) rfl
        (by simp only [Source.support,colors]) rest
      simp only [Structural.frames,frame,right_record _ _ _ _ _ colors different,above]

end ChaCha.Paper20261030.CanonicalRoutingParentRepair
