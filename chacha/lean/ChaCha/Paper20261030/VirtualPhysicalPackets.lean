import ChaCha.Paper20261030.PrimaryVirtualPackets
import ChaCha.Paper20261030.LocalPhysicalPacketStaging

/-!
# Canonical physical packets for a bounded virtual header

Virtual vertices are stored data, not vertices of the original-key tree.
Their local identifiers can therefore be the three fixed slots 0, 1, 2.
They need only be distinct within this virtual piece. The physical
vertices' immutable global identifiers are not changed.

`encode` examines only a leaf or a fork of two leaves. Larger inputs are
rejected. It installs exact physical pointer fields by the existing
canonical encoding. The final root edit replaces the reached header datum
while preserving the preceding attachment prefix and remaining payload.
-/

namespace ChaCha.Paper20261030.VirtualPhysicalPackets

open ColoredStorage SourcePointer SourceLocalProgram Structural PhysicalForestMetadata
open PhysicalPacketStaging

variable {α β ρ : Type*}

def tagSmall : Source α (List ρ) → Option (Source α (Payload ρ Nat))
  | .leaf key records => some (.leaf key (0,records))
  | .fork records (.leaf leftKey leftRecords) (.leaf rightKey rightRecords) =>
    some (.fork (0,records) (.leaf leftKey (1,leftRecords)) (.leaf rightKey (2,rightRecords)))
  | _ => none

def encode (source : Source α (List ρ)) : VirtualHeaderController.Virtual α (Record ρ Nat) :=
  (tagSmall source).map (fun tagged => encodeCursor ⟨tagged,[]⟩)

def unpack (records : List (Record ρ Nat)) : List ρ := records.flatMap (fun record => record.1.2)

def decode (header : VirtualHeaderController.Virtual α (Record ρ Nat)) : Option (Cursor α (List ρ)) :=
  header.map (Cursor.mapRecords unpack)

theorem unpack_annotation (source : Source α (Payload ρ Nat)) (parent : Option Nat) :
    ((annotate Prod.fst (fun _ => (() : Unit)) parent source).mapRecords (fun record => [record])).mapRecords unpack =
      source.mapRecords Prod.snd := by
  induction source generalizing parent <;> simp_all only [annotate,Source.mapRecords,unpack,
    List.flatMap_cons,List.flatMap_nil,List.append_nil]

/-- Reading an existing ready header works with any valid physical slot
identifiers; it does not require the new canonical slot assignment. -/
theorem decode_root (source : Source α (Payload ρ Nat)) :
    decode (some (encodeCursor ⟨source,[]⟩)) = some ⟨source.mapRecords Prod.snd,[]⟩ := by
  simp only [decode,Option.map_some,encodeCursor,SourceForestLift.packet,cursor,frames,
    Cursor.mapRecords,List.map_nil,unpack_annotation]

theorem encode_correct (source : Source α (List ρ)) (small : source.shape.leaves.length ≤ 2) :
    ∃ tagged, tagSmall source = some tagged ∧ tagged.mapRecords Prod.snd = source ∧
      (tagged.inventory Prod.fst).Nodup ∧ encode source = some (encodeCursor ⟨tagged,[]⟩) := by
  rcases source.two_leaves small with ⟨key,records,rfl⟩ | ⟨records,lk,lr,rk,rr,rfl⟩
  · refine ⟨.leaf key (0,records),rfl,rfl,?_,rfl⟩
    simp only [Source.inventory_leaf,Multiset.nodup_singleton]
  · refine ⟨.fork (0,records) (.leaf lk (1,lr)) (.leaf rk (2,rr)),rfl,rfl,?_,rfl⟩
    change ({0} + {1} + {2} : Multiset Nat).Nodup
    decide

theorem decode_encode (source : Source α (List ρ)) (small : source.shape.leaves.length ≤ 2) :
    decode (encode source) = some ⟨source,[]⟩ := by
  rcases source.two_leaves small with ⟨key,records,rfl⟩ | ⟨records,lk,lr,rk,rr,rfl⟩
  all_goals simp [decode,encode,tagSmall,encodeCursor,SourceForestLift.packet,cursor,frames,
    annotate,Cursor.mapRecords,Source.mapRecords,unpack]

def replaceHeader (fresh : VirtualHeaderController.Virtual α (Record ρ Nat)) : Packet α ρ Nat → Packet α ρ Nat
  | some (.header _) :: rest => some (.header fresh) :: rest
  | records => records

def edit (offset : Nat) (fresh : VirtualHeaderController.Virtual α (Record ρ Nat)) : Packet α ρ Nat → Packet α ρ Nat :=
  atOffset offset (replaceHeader fresh)

theorem edit_exact (before rest : Packet α ρ Nat)
    (old fresh : VirtualHeaderController.Virtual α (Record ρ Nat)) :
    edit before.length fresh (before++some (.header old)::rest) = before++some (.header fresh)::rest := by
  rw [edit,offset_exact]
  rfl

theorem install (source : Source β (Packet α ρ Nat)) (outside) (before rest : Packet α ρ Nat)
    (old : VirtualHeaderController.Virtual α (Record ρ Nat))
    (fresh : Source α (List ρ)) (small : fresh.shape.leaves.length ≤ 2)
    (atHeader : source.rootRecord = before++some (.header old)::rest) :
    Run (RootRecordTour.program (edit before.length (encode fresh)) []) .reading ⟨source,outside⟩ .done
      ⟨source.setRoot (before++some (.header (encode fresh))::rest),outside⟩ [source.rootRecord] 2 ∧
      decode (encode fresh) = some ⟨fresh,[]⟩ := by
  refine ⟨?_,decode_encode fresh small⟩
  have actual := RootRecordTour.edit_run (edit before.length (encode fresh)) source outside
  rw [atHeader,edit_exact] at actual
  simpa only [atHeader] using actual

end ChaCha.Paper20261030.VirtualPhysicalPackets
