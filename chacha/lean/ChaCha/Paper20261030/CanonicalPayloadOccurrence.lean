import ChaCha.Paper20261030.CanonicalPacketLayerViews
import ChaCha.Paper20261030.RootPackedForest
import ChaCha.Paper20261030.ThreeColorConfiguration
import ChaCha.Paper20261030.ComponentOriginalKeys
import ChaCha.Paper20261030.ComponentVirtualRoot

set_option autoImplicit false

/-! Every real logical port occurs as an actual payload subtree inside
the canonical three-color component. Its surrounding connector context
is nonempty, so changing the component root packet does not change this
payload focus. All contexts here are ghost representation witnesses. -/

namespace ChaCha.Paper20261030.SourcePayloads

open ColoredStorage SourcePointer

variable {α β ρ : Type*}

theorem payload_occurs (payload : α → Source β (List (Option ρ)))
    (source : Source α (List ρ)) (key : α) (member : key ∈ source.shape.leaves) :
    ∃ records : List ρ, ∃ outside, graft payload source =
      plug ((payload key).setRoot (records.map some ++ none::(payload key).rootRecord)) outside := by
  induction source with
  | leaf other records =>
    have same : key = other := by simpa only [Source.shape,RouterProjection.Router.leaves,List.mem_singleton] using member
    subst other
    exact ⟨records,[],rfl⟩
  | fork records left right ihl ihr =>
    rcases List.mem_append.mp member with hl | hr
    · obtain ⟨values,outside,same⟩ := ihl hl
      refine ⟨values,outside++[.left (records.map some) (graft payload right)],?_⟩
      rw [plug_append]
      change Source.fork _ _ _ = Source.fork _ _ _
      rw [← same]
    · obtain ⟨values,outside,same⟩ := ihr hr
      refine ⟨values,outside++[.right (graft payload left) (records.map some)],?_⟩
      rw [plug_append]
      change Source.fork _ _ _ = Source.fork _ _ _
      rw [← same]


/-- A singleton encoding contributes exactly one routing datum at a port. -/
theorem mapped_payload_occurs {σ : Type*} (payload : α → Source β (List (Option ρ)))
    (encode : σ → ρ) (source : Source α σ) (key : α) (member : key ∈ source.shape.leaves) :
    ∃ record : σ, ∃ outside, graft payload (source.mapRecords (fun record => [encode record])) =
      plug ((payload key).setRoot (some (encode record) :: none :: (payload key).rootRecord)) outside := by
  induction source with
  | leaf other record =>
    have same : key = other := by simpa only [Source.shape,RouterProjection.Router.leaves,List.mem_singleton] using member
    subst other
    exact ⟨record,[],rfl⟩
  | fork record left right ihl ihr =>
    rcases List.mem_append.mp member with hl | hr
    · obtain ⟨value,outside,same⟩ := ihl hl
      refine ⟨value,outside++[.left [some (encode record)] (graft payload (right.mapRecords (fun record => [encode record])))],?_⟩
      rw [plug_append]
      change Source.fork _ _ _ = Source.fork _ _ _
      rw [← same]
      rfl
    · obtain ⟨value,outside,same⟩ := ihr hr
      refine ⟨value,outside++[.right (graft payload (left.mapRecords (fun record => [encode record]))) [some (encode record)]],?_⟩
      rw [plug_append]
      change Source.fork _ _ _ = Source.fork _ _ _
      rw [← same]
      rfl

end ChaCha.Paper20261030.SourcePayloads

namespace ChaCha.Paper20261030.CanonicalPacketLayerViews

open ColoredStorage SourcePointer Structural PhysicalPacketStaging

variable {α β ρ ι : Type*}

theorem payload_occurs (payload : α → Source β (Packet α ρ ι)) (reverse : Bool) (parent : Option ι)
    (tagged : Tagged α ρ ι) (key : α) (member : key ∈ tagged.shape.leaves) :
    ∃ records : List (Datum α ρ ι), records.length = 1 ∧ ∃ outside, routing payload reverse parent tagged =
      plug ((payload key).setRoot (records.map some ++ none::(payload key).rootRecord)) outside := by
  have present : key ∈ (if reverse then (annotate Prod.fst (fun _ => (() : Unit)) parent tagged).mirror
      else annotate Prod.fst (fun _ => (() : Unit)) parent tagged).shape.leaves := by
    cases reverse <;> simpa only [Bool.false_eq_true,if_false,if_true,Source.mirror_leaves,annotate_shape,List.mem_reverse] using member
  obtain ⟨record,outside,equality⟩ := SourcePayloads.mapped_payload_occurs payload VirtualHeaderController.Datum.real _ key present
  exact ⟨[.real record],rfl,outside,equality⟩

end ChaCha.Paper20261030.CanonicalPacketLayerViews

namespace ChaCha.Paper20261030.ForestConnector.ThreeColors

open ColoredStorage SourcePointer

variable {α ρ : Type*}

theorem real_piece_inside (forest : ProjectionForest.State (Option Bool) α ρ)
    (header : Cursor α (List ρ)) (side : Bool) (current : Cursor α (List ρ))
    (present : forest (some side) = some current) :
    ∃ outside, outside ≠ [] ∧ (configuration forest header).tree = plug current.tree outside := by
  cases side with
  | false => cases left : forest (some true) with
    | none =>
      exact ⟨[.right header.tree []],by simp,by simp only [configuration,present,left,MultiSourceProgram.join,single,plug]⟩
    | some other =>
      exact ⟨[.right (.fork [] other.tree header.tree) []],by simp,
        by simp only [configuration,present,left,MultiSourceProgram.join,single,plug]⟩
  | true => cases right : forest (some false) with
    | none =>
      exact ⟨[.left [] header.tree],by simp,by simp only [configuration,present,right,MultiSourceProgram.join,single,plug]⟩
    | some other =>
      exact ⟨[.left [] header.tree,.left [] other.tree],by simp,
        by simp only [configuration,present,right,MultiSourceProgram.join,single,plug]⟩

end ChaCha.Paper20261030.ForestConnector.ThreeColors

namespace ChaCha.Paper20261030.ColoredStorage

open RouterProjection

variable {α ρ C : Type*} [LinearOrder C]

theorem Source.color_mem_support_of_leaf (color : α → C) (source : Source α ρ) (key : α)
    (member : key ∈ source.shape.leaves) : color key ∈ source.support color := by
  induction source with
  | leaf other record =>
    have same : key = other := by simpa only [Source.shape,Router.leaves,List.mem_singleton] using member
    simpa only [Source.support,Finset.mem_singleton] using congrArg color same
  | fork record left right ihl ihr =>
    rcases List.mem_append.mp member with hl | hr
    · exact Finset.mem_union_left _ (ihl hl)
    · exact Finset.mem_union_right _ (ihr hr)

end ChaCha.Paper20261030.ColoredStorage

namespace ChaCha.Paper20261030.LocalComponentCompiler

open ColoredStorage SourcePointer Structural PhysicalForestMetadata LocalComponentForestCompiler
open ForestConnector.ThreeColors

variable {α β ρ ι η : Type*} [DecidableEq α]

local instance payloadOccurrenceColorOrder : LinearOrder (Option Bool) := inferInstanceAs (LinearOrder (WithBot Bool))

theorem real_payload_occurs (color : α → Option Bool) (decorated : Source α (η × ρ))
    (forest : TaggedForest (Option Bool) α (LocalColoredCompiler.LogicalRecord ρ η (Option Bool)) ι)
    (represented : ProjectionForest.Represents color ⟨annotate Prod.fst color none decorated,[]⟩ (erase forest))
    (headerKey : α) (payload : Option Bool → α → Source β (List (Option (PhysicalDatum α ρ ι η (Option Bool)))))
    (config : MultiSourceProgram.Configuration (Option Bool) β (List (Option (PhysicalDatum α ρ ι η (Option Bool)))))
    (assembled : ForestConnector.assemble (representation none wingOrientation headerKey payload forest)
      (layout (representation none wingOrientation headerKey payload forest)) = some config)
    (key : α) (member : key ∈ decorated.shape.leaves) (real : color key ≠ none) :
    ∃ records : List (PhysicalDatum α ρ ι η (Option Bool)), records.length = 1 ∧ ∃ outside, outside ≠ [] ∧ config.tree =
      plug ((payload (color key) key).setRoot (records.map some ++ none::(payload (color key) key).rootRecord)) outside := by
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
    have physicalPiece := CanonicalPacketLayerViews.component_real none (color key) real wingOrientation headerKey payload forest tagged present
    change representation none wingOrientation headerKey payload forest (color key) =
      some ⟨CanonicalPacketLayerViews.routing (payload (color key)) (wingOrientation (color key)) none tagged,[]⟩ at physicalPiece
    obtain ⟨header,headerPresent⟩ := virtual_present_root none wingOrientation headerKey payload forest
    have canonical : config = configuration (representation none wingOrientation headerKey payload forest) ⟨header,[]⟩ :=
      Option.some.inj (assembled.symm.trans (assemble_configuration _ _ headerPresent))
    obtain ⟨records,singleton,inside,found⟩ := CanonicalPacketLayerViews.payload_occurs
      (payload (color key)) (wingOrientation (color key)) none tagged key taggedMember
    cases colorHere : color key with
    | none => exact False.elim (real colorHere)
    | some side =>
      rw [colorHere] at physicalPiece
      obtain ⟨outside,nonempty,tree⟩ := real_piece_inside
        (representation none wingOrientation headerKey payload forest) ⟨header,[]⟩ side _ physicalPiece
      refine ⟨records,singleton,inside++outside,(fun empty => nonempty (List.append_eq_nil_iff.mp empty).2),?_⟩
      rw [canonical,tree]
      change plug (CanonicalPacketLayerViews.routing _ _ _ _) outside = _
      rw [← colorHere,found,plug_append]

end ChaCha.Paper20261030.LocalComponentCompiler
