import TangoSquared.Paper20261030.CanonicalPayloadOccurrence
import TangoSquared.Paper20261030.CanonicalSubtreeValidity
import TangoSquared.Paper20261030.PacketPrefixErasure

set_option autoImplicit false

/-! A real port of a maintained component has a physically valid payload.
The routing packet attached to its root is removed only in the ghost
representation witness. This lemma supplies no uncharged navigation or
runtime write. -/

namespace TangoSquared.Paper20261030.CanonicalRealPayloadValidity

open ColoredStorage SourcePointer Structural PhysicalForestMetadata PhysicalPacketStaging
open LocalComponentCompiler ForestConnector.ThreeColors PacketLayers

variable {α β ρ ι : Type*} [DecidableEq α]

local instance canonicalRealPayloadValidityColorOrder : LinearOrder (Option Bool) :=
  inferInstanceAs (LinearOrder (WithBot Bool))

theorem occurs (color : α → Option Bool) (source : Source α ρ)
    (forest : TaggedForest (Option Bool) α ρ ι)
    (represented : ProjectionForest.Represents color ⟨source,[]⟩ (erase forest))
    (headerKey : α) (payload : Option Bool → α → Source β (Packet α ρ ι))
    (config : MultiSourceProgram.Configuration (Option Bool) β (Packet α ρ ι))
    (assembled : ForestConnector.assemble (ComponentPhysicalRepair.view none wingOrientation headerKey payload (encode forest))
      (layout (ComponentPhysicalRepair.view none wingOrientation headerKey payload (encode forest))) = some config)
    (key : α) (member : key ∈ source.shape.leaves) (real : color key ≠ none) :
    ∃ records : List (Datum α ρ ι), records.length = 1 ∧ ∃ outside, outside ≠ [] ∧ config.tree =
      plug ((payload (color key) key).setRoot (records.map some ++ none::(payload (color key) key).rootRecord)) outside := by
  have support := source.color_mem_support_of_leaf color key member
  cases packing : packed color (color key) source with
  | none => exact False.elim ((packed_none_iff color (color key) source).mp packing support)
  | some plain =>
    obtain ⟨tagged,present,erases⟩ := RootPackedForest.present color source forest represented (color key) plain packing
    have taggedMember : key ∈ tagged.shape.leaves := by
      have plainMember : key ∈ plain.shape.leaves := by
        rw [packed_shape _ _ _ packing,RouterProjection.Router.leaves_prune]
        simp only [List.mem_filter,keepColor,decide_eq_true_eq]
        exact ⟨member,True.intro⟩
      rw [← erases,Source.mapRecords_shape] at plainMember
      exact plainMember
    have physicalPiece := CanonicalPacketLayerViews.component_real none (color key) real wingOrientation headerKey payload forest tagged present
    have headerExists : ∃ header,
        ComponentPhysicalRepair.view none wingOrientation headerKey payload (encode forest) none = some ⟨header,[]⟩ := by
      simp only [ComponentPhysicalRepair.view,PayloadForestController.transform,VirtualHeaderController.encode,ite_true,Option.map_some]
      exact ⟨_,rfl⟩
    obtain ⟨header,headerPresent⟩ := headerExists
    have canonical : config = configuration (ComponentPhysicalRepair.view none wingOrientation headerKey payload (encode forest)) ⟨header,[]⟩ :=
      Option.some.inj (assembled.symm.trans (assemble_configuration _ _ headerPresent))
    obtain ⟨records,singleton,inside,found⟩ := CanonicalPacketLayerViews.payload_occurs
      (payload (color key)) (wingOrientation (color key)) none tagged key taggedMember
    cases colorHere : color key with
    | none => exact False.elim (real colorHere)
    | some side =>
      rw [colorHere] at physicalPiece
      obtain ⟨outside,nonempty,tree⟩ := real_piece_inside
        (ComponentPhysicalRepair.view none wingOrientation headerKey payload (encode forest)) ⟨header,[]⟩ side _ physicalPiece
      refine ⟨records,singleton,inside++outside,(fun empty => nonempty (List.append_eq_nil_iff.mp empty).2),?_⟩
      rw [canonical,tree]
      change plug (CanonicalPacketLayerViews.routing _ _ _ _) outside = _
      rw [← colorHere,found,plug_append]

theorem strip (markerId : ι) (source : Source β (Context.Cell α ρ ι))
    (valid : CanonicalComponentUniqueness.Valid markerId source)
    (saved : Packet α ρ ι) (body : Source β (Packet α ρ ι))
    (erases : source.mapRecords Prod.snd = body.setRoot (saved ++ body.rootRecord)) :
    ∃ bare : Source β (Context.Cell α ρ ι),
      bare.mapRecords Prod.snd = body ∧ CanonicalComponentUniqueness.Valid markerId bare := by
  let current : Cursor β (Context.Cell α ρ ι) := ⟨source,[]⟩
  let config : MultiSourceProgram.Configuration Unit β (Context.Cell α ρ ι) := ⟨source,fun _ => none⟩
  have split := PacketPrefixErasure.root_packet current saved body erases
  exact ⟨(SubtreeMetadata.replacePayload current body.rootRecord).focus,
    PacketPrefixErasure.payload current saved body erases,
    PacketPrefixErasure.physical markerId current saved body.rootRecord config rfl split valid⟩

theorem realized (markerId : ι) (color : α → Option Bool) (source : Source α ρ)
    (forest : TaggedForest (Option Bool) α ρ ι)
    (represented : ProjectionForest.Represents color ⟨source,[]⟩ (erase forest))
    (headerKey : α) (payload : Option Bool → α → Source β (Packet α ρ ι))
    (config : MultiSourceProgram.Configuration (Option Bool) β (Packet α ρ ι))
    (assembled : ForestConnector.assemble (ComponentPhysicalRepair.view none wingOrientation headerKey payload (encode forest))
      (layout (ComponentPhysicalRepair.view none wingOrientation headerKey payload (encode forest))) = some config)
    (actual : Source β (Context.Cell α ρ ι))
    (valid : CanonicalComponentUniqueness.Valid markerId actual) (erases : actual.mapRecords Prod.snd = config.tree)
    (key : α) (member : key ∈ source.shape.leaves) (real : color key ≠ none) :
    ∃ bare : Source β (Context.Cell α ρ ι),
      bare.mapRecords Prod.snd = payload (color key) key ∧ CanonicalComponentUniqueness.Valid markerId bare := by
  obtain ⟨records,_,outside,_,tree⟩ := occurs color source forest represented headerKey payload config assembled key member real
  have found := CanonicalComponentUniqueness.realized_focus markerId actual valid
    ⟨(payload (color key) key).setRoot (records.map some ++ none::(payload (color key) key).rootRecord),outside⟩ (erases.trans tree)
  obtain ⟨attached,attachedErases,attachedValid⟩ := found _ rfl
  exact strip markerId attached attachedValid (records.map some ++ [none]) (payload (color key) key)
    (by simpa only [List.append_assoc,List.singleton_append] using attachedErases)

end TangoSquared.Paper20261030.CanonicalRealPayloadValidity
