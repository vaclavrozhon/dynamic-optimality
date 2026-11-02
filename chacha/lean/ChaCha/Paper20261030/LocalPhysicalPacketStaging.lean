import ChaCha.Paper20261030.LocalRootRecordTour
import ChaCha.Paper20261030.ComponentPhysicalRepair

/-!
# Local splitting and repacking of exposed logical prefixes

The ordinary physical datum wraps several logical records in one packet.
The constant-context reassembly kernel instead moves exposed logical
prefixes individually. Staging splits a reached packet into singleton
markers and an untouched residual packet. After reassembly, repacking
merges these markers and uses the reached vertex's retained global id.
Temporary marker identifiers are not used for navigation or uniqueness.

All edits are one actual read followed by one write. Prefix offsets are
scalar inputs; the caller must still derive the finite traversal and
offsets from the observed boundary descriptors. Virtual-header contents
and the global-id agreement invariant are separate obligations.
-/

namespace ChaCha.Paper20261030.RootRecordTour

open ColoredStorage SourcePointer SourceLocalProgram

theorem edit_run {α ρ : Type*} (edit : ρ → ρ) (source : Source α ρ) (outside) :
    Run (program edit []) .reading ⟨source,outside⟩ .done
      ⟨source.setRoot (edit source.rootRecord),outside⟩ [source.rootRecord] 2 := by
  refine .next (Step.read (program := program edit []) (next := fun record _ => State.writing (edit record)) rfl) ?_
  exact .next (Step.write (program := program edit []) rfl) (.halt rfl)

end ChaCha.Paper20261030.RootRecordTour

namespace ChaCha.Paper20261030.PhysicalPacketStaging

open ColoredStorage SourcePointer SourceLocalProgram Structural PhysicalForestMetadata

variable {α β ρ ι : Type*}

abbrev Datum (α ρ ι : Type*) := ComponentPhysicalRepair.Datum α ρ ι
abbrev Packet (α ρ ι : Type*) := List (Option (Datum α ρ ι))

def placeholder : Fields ι Unit := ⟨none,{()},none⟩

def marker (markerId : ι) (record : ρ) : Option (Datum α ρ ι) :=
  some (.real ((markerId,[record]),placeholder))

def decodeMarker : Option (Datum α ρ ι) → Option ρ
  | some (.real ((_,[record]),_)) => some record
  | _ => none

theorem decode_markers (markerId : ι) (records : List ρ) :
    ((records.map (marker (α := α) markerId)).filterMap decodeMarker) = records := by
  induction records <;> simp_all only [List.map_nil,List.map_cons,List.filterMap_nil,List.filterMap_cons,
    marker,decodeMarker,List.cons.injEq,Option.toList_some,List.singleton_append]

def stageBlock (markerId : ι) (count : Nat) : Packet α ρ ι → Packet α ρ ι
  | some (.real ((id,records),fields)) :: rest =>
    (records.take count).map (marker markerId) ++ some (.real ((id,records.drop count),fields)) :: rest
  | records => records

def stageConnector (markerId : ι) : Packet α ρ ι → Packet α ρ ι
  | some (.real ((_,records),_)) :: rest => records.map (marker markerId) ++ rest
  | records => records

def packBlock (count : Nat) (id : ι) (records : Packet α ρ ι) : Packet α ρ ι :=
  let logical := (records.take count).filterMap decodeMarker
  match records.drop count with
  | some (.real ((_,tail),fields)) :: rest => some (.real ((id,logical++tail),fields)) :: rest
  | _ => records

def packConnector (count : Nat) (id : ι) (records : Packet α ρ ι) : Packet α ρ ι :=
  some (.real ((id,(records.take count).filterMap decodeMarker),placeholder)) :: records.drop count

def atOffset (offset : Nat) (edit : Packet α ρ ι → Packet α ρ ι) (records : Packet α ρ ι) : Packet α ρ ι :=
  records.take offset ++ edit (records.drop offset)

/-- The global identifier is read at the same physical vertex as the
packet being rebuilt. It is preserved as a separate retained field. -/
def retainId (edit : ι → Packet α ρ ι → Packet α ρ ι) (record : Packet α ρ ι × ι) : Packet α ρ ι × ι :=
  (edit record.2 record.1,record.2)

theorem stage_block_exact (markerId id : ι) (prefixRecords tail : List ρ) (fields : Fields ι Unit) (rest : Packet α ρ ι) :
    stageBlock markerId prefixRecords.length (some (.real ((id,prefixRecords++tail),fields)) :: rest) =
      prefixRecords.map (marker markerId) ++ some (.real ((id,tail),fields)) :: rest := by
  simp only [stageBlock,List.take_left,List.drop_left]

theorem stage_connector_exact (markerId id : ι) (prefixRecords : List ρ) (fields : Fields ι Unit) (rest : Packet α ρ ι) :
    stageConnector markerId (some (.real ((id,prefixRecords),fields)) :: rest) = prefixRecords.map (marker markerId) ++ rest := rfl

theorem pack_block_exact (markerId oldId freshId : ι) (prefixRecords tail : List ρ)
    (fields : Fields ι Unit) (rest : Packet α ρ ι) :
    packBlock prefixRecords.length freshId
      (prefixRecords.map (marker markerId) ++ some (.real ((oldId,tail),fields)) :: rest) =
      some (.real ((freshId,prefixRecords++tail),fields)) :: rest := by
  have length : (prefixRecords.map (marker (α := α) markerId)).length = prefixRecords.length := List.length_map _
  rw [packBlock,← length,List.take_left,List.drop_left,decode_markers]

theorem pack_connector_exact (markerId freshId : ι) (prefixRecords : List ρ) (rest : Packet α ρ ι) :
    packConnector prefixRecords.length freshId (prefixRecords.map (marker markerId) ++ rest) =
      some (.real ((freshId,prefixRecords),placeholder)) :: rest := by
  have length : (prefixRecords.map (marker (α := α) markerId)).length = prefixRecords.length := List.length_map _
  rw [packConnector,← length,List.take_left,List.drop_left,decode_markers]

theorem offset_exact (edit : Packet α ρ ι → Packet α ρ ι) (before rest : Packet α ρ ι) :
    atOffset before.length edit (before++rest) = before++edit rest := by
  simp only [atOffset,List.take_left,List.drop_left]

theorem local_edit (edit : Packet α ρ ι → Packet α ρ ι) (source : Source β (Packet α ρ ι)) (outside) :
    Run (RootRecordTour.program edit []) .reading ⟨source,outside⟩ .done
      ⟨source.setRoot (edit source.rootRecord),outside⟩ [source.rootRecord] 2 := RootRecordTour.edit_run edit source outside

theorem local_repack (edit : ι → Packet α ρ ι → Packet α ρ ι)
    (source : Source β (Packet α ρ ι × ι)) (outside) :
    Run (RootRecordTour.program (retainId edit) []) .reading ⟨source,outside⟩ .done
      ⟨source.setRoot (edit source.rootRecord.2 source.rootRecord.1,source.rootRecord.2),outside⟩ [source.rootRecord] 2 :=
  RootRecordTour.edit_run (retainId edit) source outside

theorem stage_block_length (markerId id : ι) (prefixRecords tail : List ρ) (fields : Fields ι Unit) (rest : Packet α ρ ι) :
    (stageBlock markerId prefixRecords.length (some (.real ((id,prefixRecords++tail),fields)) :: rest)).length =
      prefixRecords.length+1+rest.length := by
  rw [stage_block_exact]
  simp only [List.length_append,List.length_map,List.length_cons]
  omega

end ChaCha.Paper20261030.PhysicalPacketStaging
