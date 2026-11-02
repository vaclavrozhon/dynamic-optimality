import ChaCha.Paper20261030.MixedHeadInputView
import ChaCha.Paper20261030.SourceStructuralFields

/-!
# Canonical physical routing packets at exposed boundaries

The routing skeleton is annotated with its actual physical ids and
neighbor fields, optionally mirrored, then supplied with opaque payloads.
Forks contribute one whole real packet; a routing leaf contributes one
whole packet followed by the attachment delimiter. Logical prefixes merge
inside the first packet without changing any physical field.

Mirroring exchanges the physical children but retains the stored logical
left/right fields. Boundary repair must respect this distinction.
-/

namespace ChaCha.Paper20261030.CanonicalPacketLayerViews

open ColoredStorage SourcePointer Structural PhysicalPacketStaging

variable {α β ρ ι : Type*}

abbrev Tagged (α ρ ι : Type*) := Source α (ι × List ρ)

def routing (payload : α → Source β (Packet α ρ ι)) (reverse : Bool) (parent : Option ι)
    (source : Tagged α ρ ι) : Source β (Packet α ρ ι) :=
  let annotated := annotate Prod.fst (fun _ => (() : Unit)) parent source
  let oriented := if reverse then annotated.mirror else annotated
  SourcePayloads.graft payload (oriented.mapRecords (fun record => [VirtualHeaderController.Datum.real record]))

def prepend (records : List ρ) (source : Tagged α ρ ι) : Tagged α ρ ι :=
  source.setRoot (source.rootRecord.1,records++source.rootRecord.2)

theorem leaf (payload : α → Source β (Packet α ρ ι)) (reverse : Bool) (parent : Option ι)
    (key : α) (id : ι) (records : List ρ) :
    routing payload reverse parent (.leaf key (id,records)) =
      (payload key).setRoot
        (some (.real ((id,records),fields Prod.fst (fun _ => (() : Unit)) parent (.leaf key (id,records)))) ::
          none :: (payload key).rootRecord) := by
  cases reverse <;> rfl

theorem fork (payload : α → Source β (Packet α ρ ι)) (reverse : Bool) (parent : Option ι)
    (id : ι) (records : List ρ) (left right : Tagged α ρ ι) :
    routing payload reverse parent (.fork (id,records) left right) =
      .fork [some (.real ((id,records),fields Prod.fst (fun _ => (() : Unit)) parent (.fork (id,records) left right)))]
        (routing payload reverse (some id) (if reverse then right else left))
        (routing payload reverse (some id) (if reverse then left else right)) := by
  cases reverse <;> rfl

theorem logical_prefix (payload : α → Source β (Packet α ρ ι)) (reverse : Bool) (parent : Option ι)
    (records : List ρ) (source : Tagged α ρ ι) :
    routing payload reverse parent (prepend records source) =
      (routing payload reverse parent source).setRoot
        (PhysicalPacketStaging.Context.prependLogical records (routing payload reverse parent source).rootRecord) := by
  cases source with
  | leaf key record =>
    cases reverse <;> cases present : payload key <;>
      simp only [prepend,Source.setRoot,Source.rootRecord,routing,annotate,Source.mirror,
        Bool.false_eq_true,if_false,if_true,Source.mapRecords,SourcePayloads.graft,List.map_cons,List.map_nil,
        List.singleton_append,present,PhysicalPacketStaging.Context.prependLogical,fields,Source.support]
  | fork record left right =>
    cases reverse <;>
      simp only [prepend,Source.setRoot,Source.rootRecord,routing,annotate,Source.mirror,
        Bool.false_eq_true,if_false,if_true,Source.mapRecords,SourcePayloads.graft,List.map_cons,List.map_nil,
        PhysicalPacketStaging.Context.prependLogical,fields,Source.support]

theorem prefix_erases (records : List ρ) (source : Tagged α ρ ι) :
    (prepend records source).mapRecords Prod.snd =
      (source.mapRecords Prod.snd).setRoot (records++(source.mapRecords Prod.snd).rootRecord) := by
  simp only [prepend,Source.mapRecords_setRoot,Source.mapRecords_root]

private theorem set_set {σ : Type*} (source : Source α σ) (first last : σ) :
    (source.setRoot first).setRoot last = source.setRoot last := by cases source <;> rfl

private theorem root_set {σ : Type*} (source : Source α σ) (record : σ) :
    (source.setRoot record).rootRecord = record := by cases source <;> rfl

private theorem set_root {σ : Type*} (source : Source α σ) : source.setRoot source.rootRecord = source := by cases source <;> rfl

/-- A collapsed logical fork merely adds a prefix at the root of the
remaining tagged physical block. Its old physical id is retained. -/
theorem unprepend (records : List ρ) (plain : Source α (List ρ)) (tagged : Tagged α ρ ι)
    (erases : tagged.mapRecords Prod.snd = plain.setRoot (records++plain.rootRecord)) :
    ∃ block : Tagged α ρ ι, block.mapRecords Prod.snd = plain ∧ tagged = prepend records block := by
  let block := tagged.setRoot (tagged.rootRecord.1,plain.rootRecord)
  have rootEq := congrArg Source.rootRecord erases
  simp only [Source.mapRecords_root,root_set] at rootEq
  refine ⟨block,?_,?_⟩
  · simp only [block,Source.mapRecords_setRoot,erases,set_set,set_root]
  · simp only [block,prepend,root_set,set_set,← rootEq,Prod.mk.eta,set_root]

theorem fork_decomposition (records : List ρ) (left right : Source α (List ρ)) (tagged : Tagged α ρ ι)
    (erases : tagged.mapRecords Prod.snd = .fork records left right) :
    ∃ id taggedLeft taggedRight, tagged = .fork (id,records) taggedLeft taggedRight ∧
      taggedLeft.mapRecords Prod.snd = left ∧ taggedRight.mapRecords Prod.snd = right := by
  cases tagged with
  | leaf => cases erases
  | fork record taggedLeft taggedRight =>
    simp only [Source.mapRecords,Source.fork.injEq] at erases
    obtain ⟨rootEq,leftEq,rightEq⟩ := erases
    refine ⟨record.1,taggedLeft,taggedRight,?_,leftEq,rightEq⟩
    cases record
    cases rootEq
    rfl

private theorem map_twice {σ τ υ : Type*} (f : σ → τ) (g : τ → υ) (source : Source α σ) :
    (source.mapRecords f).mapRecords g = source.mapRecords (g ∘ f) := by
  induction source <;> simp_all only [Source.mapRecords,Function.comp_def]

private theorem mirror_map {σ τ : Type*} (f : σ → τ) (source : Source α σ) :
    (source.mapRecords f).mirror = source.mirror.mapRecords f := by
  induction source <;> simp_all only [Source.mapRecords,Source.mirror]

/-- This is the real piece of the existing component encoding, including
physical annotation, orientation, real-datum wrapping, and payloads. -/
theorem component_real {C : Type*} [DecidableEq C] (virtualColor q : C) (different : q ≠ virtualColor)
    (orientation : C → Bool) (headerKey : α)
    (payload : C → α → Source β (Packet α ρ ι))
    (forest : PhysicalForestMetadata.TaggedForest C α ρ ι) (source : Tagged α ρ ι)
    (present : forest q = some ⟨source,[]⟩) :
    ComponentPhysicalRepair.view virtualColor orientation headerKey payload (PhysicalForestMetadata.encode forest) q =
      some ⟨routing (payload q) (orientation q) none source,[]⟩ := by
  cases reversed : orientation q <;>
    simp only [ComponentPhysicalRepair.view,PayloadForestController.transform,VirtualHeaderController.encode,different,if_false,
      ForestMirrorController.transform,PhysicalForestMetadata.encode,present,Option.map_some,
      PhysicalForestMetadata.encodeCursor,SourceForestLift.packet,Structural.cursor,Structural.parentId,Structural.frames,
      Cursor.mapRecords,List.map_nil,ForestMirrorController.turn,reversed,Bool.false_eq_true,if_true,
      Cursor.mirror,SourcePayloads.cursor,routing,mirror_map,map_twice,Function.comp_def,List.map_cons,List.map_nil]

theorem component_virtual {C : Type*} [DecidableEq C] (virtualColor : C) (orientation : C → Bool) (headerKey : α)
    (payload : C → α → Source β (Packet α ρ ι)) (forest : PhysicalForestMetadata.TaggedForest C α ρ ι) :
    ComponentPhysicalRepair.view virtualColor orientation headerKey payload (PhysicalForestMetadata.encode forest) virtualColor =
      some ⟨(payload virtualColor headerKey).setRoot
        (some (.header (ForestMirrorController.transform orientation (PhysicalForestMetadata.encode forest) virtualColor)) ::
          none :: (payload virtualColor headerKey).rootRecord),[]⟩ := by
  simp only [ComponentPhysicalRepair.view,PayloadForestController.transform,VirtualHeaderController.encode,ite_true,
    Option.map_some,SourcePayloads.cursor,SourcePayloads.graft,List.map_cons,List.map_nil,List.singleton_append]

end ChaCha.Paper20261030.CanonicalPacketLayerViews
