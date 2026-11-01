import TangoSquared.Paper20261030.HeadPacketAlignment
import TangoSquared.Paper20261030.LocalPackedContextStaging

/-!
# Mixed packet layers at one reached physical vertex

A node can contain an outer attachment packet, its delimiter, and a
nested component's root packet. Other nodes are empty primary joins or
virtual-header leaves. `Expression` describes this representation only
in proofs. The running `Blueprint` contains tags and lengths, never
record values or trees.

Whole packets are expanded completely. Only a retained opaque routing
block uses the final `prefix` case, which preserves a residual packet.
Raw headers and delimiters are copied in place. Repacking uses the
immutable id read at this vertex and preserves every raw suffix.
-/

namespace TangoSquared.Paper20261030.PacketLayers

open ColoredStorage SourcePointer SourceLocalProgram Structural PhysicalPacketStaging PacketAlignment

variable {α β ρ ι : Type*}

inductive Expression (α ρ ι : Type*) where
  | base
  | raw (records : Packet α ρ ι) (rest : Expression α ρ ι)
  | whole (id : ι) (records : List ρ) (fields : Fields ι Unit) (rest : Expression α ρ ι)
  | «prefix» (records : List ρ)

inductive Blueprint where
  | base
  | raw (count : Nat) (rest : Blueprint)
  | whole (count : Nat) (rest : Blueprint)
  | «prefix» (count : Nat)

def blueprint : Expression α ρ ι → Blueprint
  | .base => .base
  | .raw records rest => .raw records.length (blueprint rest)
  | .whole _ records _ rest => .whole records.length (blueprint rest)
  | .prefix records => .prefix records.length

def stored (base : Packet α ρ ι) : Expression α ρ ι → Packet α ρ ι
  | .base => base
  | .raw records rest => records++stored base rest
  | .whole id records fields rest => some (.real ((id,records),fields)) :: stored base rest
  | .prefix records => PhysicalPacketStaging.Context.prependLogical records base

def staged (markerId : ι) (base : Packet α ρ ι) : Expression α ρ ι → Packet α ρ ι
  | .base => base
  | .raw records rest => records++staged markerId base rest
  | .whole _ records _ rest => records.map (marker markerId) ++ staged markerId base rest
  | .prefix records => records.map (marker markerId) ++ base

def exposed (markerId : ι) : Expression α ρ ι → Packet α ρ ι
  | .base => []
  | .raw records rest => records ++ exposed markerId rest
  | .whole _ records _ rest => records.map (marker markerId) ++ exposed markerId rest
  | .prefix records => records.map (marker markerId)

theorem staged_exposed (markerId : ι) (base : Packet α ρ ι) (expression : Expression α ρ ι) :
    staged markerId base expression = exposed markerId expression ++ base := by
  induction expression <;> simp_all only [staged,exposed,List.nil_append,List.append_assoc]

def rebuilt (vertexId : ι) (base : Packet α ρ ι) : Expression α ρ ι → Packet α ρ ι
  | .base => base
  | .raw records rest => records++rebuilt vertexId base rest
  | .whole _ records _ rest => some (.real ((vertexId,records),placeholder)) :: rebuilt vertexId base rest
  | .prefix records => PhysicalPacketStaging.Context.prependLogical records base

def Ready (base : Packet α ρ ι) : Expression α ρ ι → Prop
  | .base => True
  | .raw _ rest | .whole _ _ _ rest => Ready base rest
  | .prefix _ => ∃ id records fields rest, base = some (.real ((id,records),fields)) :: rest

def ReadyAt (vertexId : ι) (base : Packet α ρ ι) : Expression α ρ ι → Prop
  | .base => True
  | .raw _ rest | .whole _ _ _ rest => ReadyAt vertexId base rest
  | .prefix _ => ∃ records fields rest, base = some (.real ((vertexId,records),fields)) :: rest

def OrdinaryBase (markerId : ι) (base : Packet α ρ ι) : Expression α ρ ι → Prop
  | .base => True
  | .raw _ rest | .whole _ _ _ rest => OrdinaryBase markerId base rest
  | .prefix _ => ∃ id records fields rest, base = some (.real ((id,records),fields)) :: rest ∧ id ≠ markerId

def stage (markerId : ι) : Blueprint → Packet α ρ ι → Packet α ρ ι
  | .base,packet => packet
  | .raw count rest,packet => packet.take count ++ stage markerId rest (packet.drop count)
  | .whole _ rest,some (.real ((_,records),_)) :: tail => records.map (marker markerId) ++ stage markerId rest tail
  | .whole _ _,packet => packet
  | .prefix count,packet => stageBlock markerId count packet

def repack (vertexId : ι) : Blueprint → Packet α ρ ι → Packet α ρ ι
  | .base,packet => packet
  | .raw count rest,packet => packet.take count ++ repack vertexId rest (packet.drop count)
  | .whole count rest,packet => some (.real ((vertexId,(packet.take count).filterMap decodeMarker),placeholder)) ::
      repack vertexId rest (packet.drop count)
  | .prefix count,packet => packBlock count vertexId packet

theorem stage_exact (markerId : ι) (base : Packet α ρ ι) (expression : Expression α ρ ι)
    (ready : Ready base expression) :
    stage markerId (blueprint expression) (stored base expression) = staged markerId base expression := by
  induction expression with
  | base => rfl
  | raw records rest ih => simp only [blueprint,stored,stage,staged,List.take_left,List.drop_left,ih ready]
  | whole id records fields rest ih => simp only [blueprint,stored,stage,staged,ih ready]
  | «prefix» records =>
    obtain ⟨id,tail,fields,rest,equal⟩ := ready
    simp only [blueprint,stored,stage,staged,equal,PhysicalPacketStaging.Context.prependLogical,stage_block_exact]

theorem repack_exact (markerId vertexId : ι) (base : Packet α ρ ι) (expression : Expression α ρ ι)
    (ready : ReadyAt vertexId base expression) :
    repack vertexId (blueprint expression) (staged markerId base expression) = rebuilt vertexId base expression := by
  induction expression with
  | base => rfl
  | raw records rest ih => simp only [blueprint,staged,repack,rebuilt,List.take_left,List.drop_left,ih ready]
  | whole id records fields rest ih =>
    have length : (records.map (marker (α := α) markerId)).length = records.length := List.length_map _
    simp only [blueprint,staged,repack,rebuilt]
    rw [← length,List.take_left,List.drop_left,decode_markers,ih ready]
  | «prefix» records =>
    obtain ⟨tail,fields,rest,equal⟩ := ready
    simp only [blueprint,staged,repack,rebuilt,equal,pack_block_exact,PhysicalPacketStaging.Context.prependLogical]

theorem ordinary_ready (markerId : ι) (base : Packet α ρ ι) (expression : Expression α ρ ι)
    (ordinary : OrdinaryBase markerId base expression) : Ready base expression := by
  induction expression with
  | base => trivial
  | raw _ _ ih | whole _ _ _ _ ih => exact ih ordinary
  | «prefix» _ =>
    obtain ⟨id,records,fields,rest,equal,_⟩ := ordinary
    exact ⟨id,records,fields,rest,equal⟩

theorem ready_from_alignment (markerId vertexId : ι) (base : Packet α ρ ι) (expression : Expression α ρ ι)
    (ordinary : OrdinaryBase markerId base expression)
    (aligned : Aligned markerId vertexId (staged markerId base expression)) : ReadyAt vertexId base expression := by
  induction expression with
  | base => trivial
  | raw records rest ih =>
    exact ih ordinary (fun entry member => aligned entry (List.mem_append_right records member))
  | whole id records fields rest ih =>
    exact ih ordinary (fun entry member => aligned entry (List.mem_append_right _ member))
  | «prefix» records =>
    obtain ⟨id,tail,fields,rest,equal,different⟩ := ordinary
    have atPacket : Aligned markerId vertexId
        (records.map (marker markerId) ++ some (.real ((id,tail),fields)) :: rest) := by
      simpa only [staged,equal] using aligned
    have same := stored_id markerId vertexId id tail fields _ rest atPacket different
    exact ⟨tail,fields,rest,same ▸ equal⟩

theorem stage_local (markerId : ι) (base : Packet α ρ ι) (expression : Expression α ρ ι)
    (ready : Ready base expression) (source : Source β (Packet α ρ ι)) (outside)
    (atRoot : source.rootRecord = stored base expression) :
    Run (RootRecordTour.program (stage markerId (blueprint expression)) []) .reading ⟨source,outside⟩ .done
      ⟨source.setRoot (staged markerId base expression),outside⟩ [source.rootRecord] 2 := by
  have actual := RootRecordTour.edit_run (stage markerId (blueprint expression)) source outside
  rw [atRoot,stage_exact markerId base expression ready] at actual
  simpa only [atRoot] using actual

theorem repack_local (markerId vertexId : ι) (base : Packet α ρ ι) (expression : Expression α ρ ι)
    (ordinary : OrdinaryBase markerId base expression)
    (aligned : Aligned markerId vertexId (staged markerId base expression))
    (source : Source β (Packet α ρ ι × ι)) (outside)
    (atRoot : source.rootRecord = (staged markerId base expression,vertexId)) :
    Run (RootRecordTour.program (retainId (fun id => repack id (blueprint expression))) []) .reading ⟨source,outside⟩ .done
      ⟨source.setRoot (rebuilt vertexId base expression,vertexId),outside⟩ [source.rootRecord] 2 := by
  have ready := ready_from_alignment markerId vertexId base expression ordinary aligned
  have actual := RootRecordTour.edit_run (retainId (fun id => repack id (blueprint expression))) source outside
  rw [atRoot] at actual
  simpa only [retainId,repack_exact markerId vertexId base expression ready,atRoot] using actual

end TangoSquared.Paper20261030.PacketLayers
