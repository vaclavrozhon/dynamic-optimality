import ChaCha.Paper20261030.MarkerFreePacketReadiness
import ChaCha.Paper20261030.LocalRootNeighborEdit

set_option autoImplicit false

/-!
# Scalar plans for physical-field repair inside mixed packet layers

An exposed routing fork uses the two actually read physical child ids.
Its `reverse` bit restores logical left/right order in a mirrored wing.
A routing leaf has no routing children even when its attached payload is
a physical fork. Crossing this attachment resets the inner parent to
none. An opaque prefix changes only the first real packet's parent.

The plan contains tags, offsets, and orientation bits, not stored records
or subtree contents. All logical contents, physical ids, headers, and
delimiters are preserved by the edit, even on malformed input.
-/

namespace ChaCha.Paper20261030.MixedPacketRepair

open ColoredStorage SourcePointer Structural PhysicalPacketStaging

variable {α β ρ ι : Type*}

inductive Layers where
  | base
  | raw (count : Nat) (rest : Layers)
  | leaf (rest : Layers)
  | fork (reverse : Bool)
  | prefix

def Layers.hasFork : Layers → Bool
  | .base | .prefix => false
  | .raw _ rest | .leaf rest => rest.hasFork
  | .fork _ => true

def childParent (plan : Layers) (id : ι) : Option ι := if plan.hasFork then some id else none

def neighbors (parent : Option ι) (reverse : Bool) (children : Option (ι × ι)) : Fields ι Unit :=
  ⟨parent,{()},children.map (fun pair =>
    if reverse then (⟨pair.2,{()}⟩,⟨pair.1,{()}⟩) else (⟨pair.1,{()}⟩,⟨pair.2,{()}⟩))⟩

def edit : Layers → Option ι → Option (ι × ι) → Packet α ρ ι → Packet α ρ ι
  | .base,_,_,packet => packet
  | .raw count rest,parent,children,packet => packet.take count ++ edit rest parent children (packet.drop count)
  | .leaf rest,parent,children,some (.real (payload,_)) :: tail =>
      some (.real (payload,neighbors parent false none)) :: edit rest none children tail
  | .fork reverse,parent,children,some (.real (payload,_)) :: tail =>
      some (.real (payload,neighbors parent reverse children)) :: tail
  | .prefix,parent,_,some (.real (payload,fields)) :: tail =>
      some (.real (payload,{ fields with parent := parent })) :: tail
  | _,_,_,packet => packet

def cell (plan : Layers) (parent : Option ι) (record : PacketLayers.Context.Cell α ρ ι)
    (children : Option (ι × ι)) : PacketLayers.Context.Cell α ρ ι :=
  (record.1,edit plan parent children record.2)

def eraseEntry : Option (Datum α ρ ι) → Option (Datum α ρ ι)
  | some (.real (payload,_)) => some (.real (payload,placeholder))
  | entry => entry

def erase (packet : Packet α ρ ι) : Packet α ρ ι := packet.map eraseEntry

theorem edit_erases (plan : Layers) (parent : Option ι) (children : Option (ι × ι)) (packet : Packet α ρ ι) :
    erase (edit plan parent children packet) = erase packet := by
  induction plan generalizing parent packet with
  | base => rfl
  | raw count rest ih =>
    have mapped := ih parent (packet.drop count)
    dsimp only [erase] at mapped
    simp only [edit,erase,List.map_append,mapped]
    rw [← List.map_append,List.take_append_drop]
  | leaf rest ih =>
    cases packet with
    | nil => rfl
    | cons entry tail => cases entry with
      | none => rfl
      | some datum => cases datum with
        | header => rfl
        | real record =>
          simp only [edit,erase,List.map_cons,eraseEntry]
          exact congrArg (List.cons _) (ih none tail)
  | fork reverse =>
    cases packet with
    | nil => rfl
    | cons entry tail => cases entry with
      | none => rfl
      | some datum => cases datum <;> rfl
  | «prefix» =>
    cases packet with
    | nil => rfl
    | cons entry tail => cases entry with
      | none => rfl
      | some datum => cases datum <;> rfl

theorem edit_length (plan : Layers) (parent : Option ι) (children : Option (ι × ι)) (packet : Packet α ρ ι) :
    (edit plan parent children packet).length = packet.length := by
  have equal := congrArg List.length (edit_erases plan parent children packet)
  simpa only [erase,List.length_map] using equal

theorem eraseEntry_alignment (markerId vertexId : ι) (entry : Option (Datum α ρ ι)) :
    PacketAlignment.Entry markerId vertexId (eraseEntry entry) ↔ PacketAlignment.Entry markerId vertexId entry := by
  cases entry with
  | none => rfl
  | some datum => cases datum <;> rfl

theorem erase_alignment (markerId vertexId : ι) (packet : Packet α ρ ι) :
    PacketAlignment.Aligned markerId vertexId (erase packet) ↔ PacketAlignment.Aligned markerId vertexId packet := by
  constructor
  · intro valid entry member
    exact (eraseEntry_alignment markerId vertexId entry).mp (valid _ (List.mem_map.mpr ⟨entry,member,rfl⟩))
  · intro valid entry member
    obtain ⟨old,oldMember,equal⟩ := (List.mem_map (f := eraseEntry) (l := packet)).mp member
    subst entry
    exact (eraseEntry_alignment markerId vertexId old).mpr (valid old oldMember)

theorem edit_alignment (markerId vertexId : ι) (plan : Layers) (parent : Option ι)
    (children : Option (ι × ι)) (packet : Packet α ρ ι) (valid : PacketAlignment.Aligned markerId vertexId packet) :
    PacketAlignment.Aligned markerId vertexId (edit plan parent children packet) := by
  apply (erase_alignment markerId vertexId _).mp
  rw [edit_erases]
  exact (erase_alignment markerId vertexId packet).mpr valid

theorem eraseEntry_clear (markerId : ι) (entry : Option (Datum α ρ ι)) :
    MarkerFreePackets.Entry markerId (eraseEntry entry) ↔ MarkerFreePackets.Entry markerId entry := by
  cases entry with
  | none => rfl
  | some datum => cases datum <;> rfl

theorem erase_clear (markerId : ι) (packet : Packet α ρ ι) :
    MarkerFreePackets.Packet markerId (erase packet) ↔ MarkerFreePackets.Packet markerId packet := by
  constructor
  · intro valid entry member
    exact (eraseEntry_clear markerId entry).mp (valid _ (List.mem_map.mpr ⟨entry,member,rfl⟩))
  · intro valid entry member
    obtain ⟨old,oldMember,equal⟩ := (List.mem_map (f := eraseEntry) (l := packet)).mp member
    subst entry
    exact (eraseEntry_clear markerId old).mpr (valid old oldMember)

theorem edit_clear (markerId : ι) (plan : Layers) (parent : Option ι) (children : Option (ι × ι))
    (packet : Packet α ρ ι) (valid : MarkerFreePackets.Packet markerId packet) :
    MarkerFreePackets.Packet markerId (edit plan parent children packet) := by
  apply (erase_clear markerId _).mp
  rw [edit_erases]
  exact (erase_clear markerId packet).mpr valid

theorem fork_fields (reverse : Bool) (parent : Option ι) (record : ι × List ρ)
    (left right : Source α (ι × List ρ)) :
    neighbors parent reverse (some (left.rootRecord.1,right.rootRecord.1)) =
      fields Prod.fst (fun _ => (() : Unit)) parent
        (.fork record (if reverse then right else left) (if reverse then left else right)) := by
  cases reverse <;> simp only [neighbors,Option.map_some,Bool.false_eq_true,if_false,if_true,
    fields,descriptor,Source.support,PhysicalBoundaryRepair.unit_support,Finset.union_self]

theorem leaf_fields (parent : Option ι) (key : α) (record : ι × List ρ) :
    neighbors parent false none = fields Prod.fst (fun _ => (() : Unit)) parent (.leaf key record) := rfl

end ChaCha.Paper20261030.MixedPacketRepair
