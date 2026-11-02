import ChaCha.Paper20261030.CanonicalPayloadOccurrence
import ChaCha.Paper20261030.CanonicalRoutingCursor
import ChaCha.Paper20261030.ThreeColorWingReplacement

set_option autoImplicit false

/-! A canonical real payload position retains its tagged routing-leaf
context and its surrounding empty connectors. This is the representation
witness needed to identify the parent's executed repair after a nested
component preparation. -/

namespace ChaCha.Paper20261030.SourcePointer

open ColoredStorage

variable {α ρ : Type*}

theorem leaf_occurs (source : Source α ρ) (key : α) (member : key ∈ source.shape.leaves) :
    ∃ record outside, source = plug (.leaf key record) outside := by
  induction source with
  | leaf other record =>
    have same : key = other := by simpa only [Source.shape,RouterProjection.Router.leaves,List.mem_singleton] using member
    subst other
    exact ⟨record,[],rfl⟩
  | fork record left right ihl ihr =>
    rcases List.mem_append.mp member with hl | hr
    · obtain ⟨value,outside,same⟩ := ihl hl
      refine ⟨value,outside++[.left record right],?_⟩
      rw [plug_append]
      change Source.fork _ _ _ = Source.fork _ _ _
      rw [← same]
    · obtain ⟨value,outside,same⟩ := ihr hr
      refine ⟨value,outside++[.right left record],?_⟩
      rw [plug_append]
      change Source.fork _ _ _ = Source.fork _ _ _
      rw [← same]

end ChaCha.Paper20261030.SourcePointer



namespace ChaCha.Paper20261030.LocalComponentCompiler

open ColoredStorage SourcePointer Structural PhysicalForestMetadata LocalComponentForestCompiler ForestConnector.ThreeColors

variable {α β ρ ι η : Type*} [DecidableEq α]

local instance payloadPositionColorOrder : LinearOrder (Option Bool) := inferInstanceAs (LinearOrder (WithBot Bool))

theorem real_payload_position (color : α → Option Bool) (decorated : Source α (η × ρ))
    (forest : TaggedForest (Option Bool) α (LocalColoredCompiler.LogicalRecord ρ η (Option Bool)) ι)
    (represented : ProjectionForest.Represents color ⟨annotate Prod.fst color none decorated,[]⟩ (erase forest))
    (headerKey : α) (payload : Option Bool → α → Source β (List (Option (PhysicalDatum α ρ ι η (Option Bool)))))
    (config : MultiSourceProgram.Configuration (Option Bool) β (List (Option (PhysicalDatum α ρ ι η (Option Bool)))))
    (assembled : ForestConnector.assemble (representation none wingOrientation headerKey payload forest)
      (layout (representation none wingOrientation headerKey payload forest)) = some config)
    (key : α) (member : key ∈ decorated.shape.leaves) (real : color key ≠ none) :
    ∃ tagged ident records inside outside,
      forest (color key) = some ⟨tagged,[]⟩ ∧ tagged = plug (.leaf key (ident,records)) inside ∧
      outside ≠ [] ∧ EmptyConnector outside ∧
      config.tree = plug (CanonicalRoutingCursor.cursor (payload (color key)) (wingOrientation (color key))
        ⟨.leaf key (ident,records),inside⟩).tree outside ∧
      (∀ fresh : Cursor β (List (Option (PhysicalDatum α ρ ι η (Option Bool)))), ∃ next,
        ForestConnector.assemble (Function.update (representation none wingOrientation headerKey payload forest) (color key) (some fresh))
          (layout (Function.update (representation none wingOrientation headerKey payload forest) (color key) (some fresh))) = some next ∧
        next.tree = plug fresh.tree outside) := by
  let logical := annotate Prod.fst color none decorated
  have support : color key ∈ logical.support color :=
    logical.color_mem_support_of_leaf color key (by simpa only [logical,annotate_shape] using member)
  cases packedHere : packed color (color key) logical with
  | none => exact False.elim ((packed_none_iff color (color key) logical).mp packedHere support)
  | some plain =>
    obtain ⟨tagged,present,erases⟩ := RootPackedForest.present color logical forest represented (color key) plain packedHere
    have taggedMember : key ∈ tagged.shape.leaves := by
      have plainMember : key ∈ plain.shape.leaves := by
        rw [packed_shape _ _ _ packedHere,RouterProjection.Router.leaves_prune]
        simp only [List.mem_filter,keepColor,decide_eq_true_eq]
        exact ⟨by simpa only [logical,annotate_shape] using member,True.intro⟩
      rw [← erases,Source.mapRecords_shape] at plainMember
      exact plainMember
    obtain ⟨⟨ident,records⟩,inside,taggedEq⟩ := leaf_occurs tagged key taggedMember
    have physicalPiece := CanonicalPacketLayerViews.component_real none (color key) real wingOrientation headerKey payload forest tagged present
    change representation none wingOrientation headerKey payload forest (color key) =
      some ⟨CanonicalPacketLayerViews.routing (payload (color key)) (wingOrientation (color key)) none tagged,[]⟩ at physicalPiece
    obtain ⟨header,headerPresent⟩ := virtual_present_root none wingOrientation headerKey payload forest
    have canonical : config = configuration (representation none wingOrientation headerKey payload forest) ⟨header,[]⟩ :=
      Option.some.inj (assembled.symm.trans (assemble_configuration _ _ headerPresent))
    cases colorHere : color key with
    | none => exact False.elim (real colorHere)
    | some side =>
      rw [colorHere] at physicalPiece
      obtain ⟨outside,nonempty,empty,tree,replacement⟩ := replace_piece
        (representation none wingOrientation headerKey payload forest) ⟨header,[]⟩ side _ physicalPiece
      refine ⟨tagged,ident,records,inside,outside,(by simpa only [colorHere] using present),taggedEq,nonempty,empty,?_,?_⟩
      · rw [canonical,tree]
        change plug (CanonicalPacketLayerViews.routing _ _ _ _) outside = _
        rw [← colorHere,CanonicalRoutingCursor.tree]
        exact congrArg (fun source => plug (CanonicalPacketLayerViews.routing (payload (color key)) (wingOrientation (color key)) none source) outside) taggedEq
      · intro fresh
        have keptHeader : (Function.update (representation none wingOrientation headerKey payload forest) (some side) (some fresh)) none = some ⟨header,[]⟩ := by
          rw [Function.update_of_ne (by simp)]
          exact headerPresent
        exact ⟨_,assemble_configuration _ ⟨header,[]⟩ keptHeader,replacement fresh⟩

end ChaCha.Paper20261030.LocalComponentCompiler
