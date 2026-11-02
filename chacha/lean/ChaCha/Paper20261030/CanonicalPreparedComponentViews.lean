import ChaCha.Paper20261030.CanonicalComponentAssembly
import ChaCha.Paper20261030.AnnotatedHeadWingPacking
import ChaCha.Paper20261030.ComponentOriginalKeys

/-!
# Prepared component views from the maintained canonical forest

The opaque wing blocks and exposed old physical fields are obtained from
the canonical tagged projections. Their primary joins and virtual bottom
come from the actual shared-tree assembly. All witnesses below are proof
data; the controller uses the observed masks and bounded records.
-/

namespace ChaCha.Paper20261030.CanonicalPreparedComponentViews

open ColoredStorage SourcePointer Structural HeadBoundary PhysicalForestMetadata PhysicalPacketStaging
open PacketLayers.Representation CanonicalRoutingDecomposition CanonicalComponentAssembly
open MixedHeadInputView (Physical JoinFields PrimaryFields ActiveFields)
open LocalComponentCompiler (wingOrientation)
open ObservedHeadBlueprint (owned)

variable {α β ρ ι η : Type*} [DecidableEq α]

local instance : LinearOrder (Option Bool) := inferInstanceAs (LinearOrder (WithBot Bool))

abbrev Logical (ρ η : Type*) := HeadBoundary.Record ρ η (Option Bool)

def header (forest : TaggedForest (Option Bool) α (Logical ρ η) ι) : Packet α (Logical ρ η) ι :=
  [some (.header (ForestMirrorController.transform wingOrientation (encode forest) none)),none]

def dormantView (fields : PrimaryFields ι) (high : Logical ρ η) (header : Packet α (Logical ρ η) ι)
    (left right : Physical β α (Logical ρ η) ι) (bottom : Source β (PacketLayers.Context.Cell α (Logical ρ η) ι)) :=
  physicalPrimaryJoin fields.root
    (physicalPrimaryJoin fields.first (left.map (addRoot (owned (some true) high)))
      (some (MixedHeadInputView.rawBlock header bottom)))
    (right.map (addRoot (owned (some false) high)))

def activeView (fields : ActiveFields ι) (direction : Bool) (low high terminal : Logical ρ η)
    (header : Packet α (Logical ρ η) ι)
    (headLeft headRight tailLeft tailRight child : Physical β α (Logical ρ η) ι)
    (bottom : Source β (PacketLayers.Context.Cell α (Logical ρ η) ι)) :=
  let attached := MixedHeadInputView.attach fields.attachmentId fields.attachmentFields terminal child
  let left := if direction then MixedHeadInputView.join fields.upperLeft (owned (some true) high) attached tailLeft
    else tailLeft.map (addRoot (owned (some true) high))
  let right := if direction then tailRight.map (addRoot (owned (some false) high))
    else MixedHeadInputView.join fields.upperRight (owned (some false) high) tailRight attached
  physicalPrimaryJoin fields.primary.root
    (physicalPrimaryJoin fields.primary.first
      (MixedHeadInputView.join fields.lowerLeft (owned (some true) low) headLeft left)
      (some (MixedHeadInputView.rawBlock header bottom)))
    (MixedHeadInputView.join fields.lowerRight (owned (some false) low) right headRight)

theorem dormant (dummyId : ι) (identifier : ρ → η) (color : α → Option Bool)
    (high terminal : ρ) (depth : α) (tail : Source α ρ) (boundary : color depth = none)
    (forest : TaggedForest (Option Bool) α (Logical ρ η) ι)
    (represented : ProjectionForest.Represents color
      ⟨annotate identifier color none (.fork high (.leaf depth terminal) tail),[]⟩ (erase forest))
    (headerKey : α) (payload : Option Bool → α → Source β (Packet α (Logical ρ η) ι))
    (config : MultiSourceProgram.Configuration (Option Bool) β (Packet α (Logical ρ η) ι))
    (assembled : ForestConnector.assemble
      (ComponentPhysicalRepair.view none wingOrientation headerKey payload (encode forest))
      (ForestConnector.ThreeColors.layout (ComponentPhysicalRepair.view none wingOrientation headerKey payload (encode forest))) = some config) :
    ∃ left right : Physical β α (Logical ρ η) ι,
      left.isSome = (packed color (some true) (annotate identifier color (some (identifier high)) tail)).isSome ∧
      right.isSome = (packed color (some false) (annotate identifier color (some (identifier high)) tail)).isSome ∧
      some (config.tree.mapRecords (fun packet => (dummyId,packet))) =
        dormantView ⟨dummyId,dummyId⟩ (high,fields identifier color none (.fork high (.leaf depth terminal) tail))
          (header forest) left right ((payload none headerKey).mapRecords (fun packet => (dummyId,packet))) ∧
      CanonicalHeadWingViews.RootReady left ∧ CanonicalHeadWingViews.RootReady right ∧
      CanonicalHeadWingViews.Canonical dummyId (payload (some true)) false
        (packed color (some true) (annotate identifier color (some (identifier high)) tail)) left ∧
      CanonicalHeadWingViews.Canonical dummyId (payload (some false)) true
        (packed color (some false) (annotate identifier color (some (identifier high)) tail)) right := by
  let source := annotate identifier color none (.fork high (.leaf depth terminal) tail)
  have erases (side : Bool) := packed_focus color source forest represented (some side)
  have leftPacking := (erases true).trans (AnnotatedHeadWingPacking.dormant identifier color true high terminal depth tail boundary)
  have rightPacking := (erases false).trans (AnnotatedHeadWingPacking.dormant identifier color false high terminal depth tail boundary)
  obtain ⟨left,leftPresent,leftView,leftReady,leftCanonical⟩ := CanonicalHeadWingViews.dormant_canonical dummyId (payload (some true)) false none _ _ _ leftPacking
  obtain ⟨right,rightPresent,rightView,rightReady,rightCanonical⟩ := CanonicalHeadWingViews.dormant_canonical dummyId (payload (some false)) true none _ _ _ rightPacking
  have virtual := CanonicalPacketLayerViews.component_virtual none wingOrientation headerKey payload forest
  have assembly := CanonicalComponentAssembly.assembled dummyId _ _ virtual config assembled
  rw [real_piece dummyId color source forest represented none (some true) (by simp) wingOrientation headerKey payload,
    real_piece dummyId color source forest represented none (some false) (by simp) wingOrientation headerKey payload,
    virtual_piece dummyId none wingOrientation headerKey payload forest] at assembly
  change some (config.tree.mapRecords (fun packet => (dummyId,packet))) =
    physicalPrimaryJoin dummyId
      (physicalPrimaryJoin dummyId (render dummyId (payload (some true)) false none ((forest (some true)).map Cursor.focus))
        (some (MixedHeadInputView.rawBlock (header forest) ((payload none headerKey).mapRecords (fun packet => (dummyId,packet))))))
      (render dummyId (payload (some false)) true none ((forest (some false)).map Cursor.focus)) at assembly
  rw [leftView,rightView] at assembly
  exact ⟨left,right,leftPresent,rightPresent,assembly,leftReady,rightReady,leftCanonical,rightCanonical⟩

private theorem join_none_left (fields : JoinFields ι) (records : List (Logical ρ η)) (right : Physical β α (Logical ρ η) ι) :
    MixedHeadInputView.join fields records none right = right.map (addRoot records) := by cases right <;> rfl

private theorem join_none_right (fields : JoinFields ι) (records : List (Logical ρ η)) (left : Physical β α (Logical ρ η) ι) :
    MixedHeadInputView.join fields records left none = left.map (addRoot records) := by cases left <;> rfl

theorem active (dummyId : ι) (identifier : ρ → η) (color : α → Option Bool)
    (low high terminal : ρ) (depth : α) (headPart tail : Source α ρ) (direction : Bool)
    (boundary : color depth = some direction)
    (forest : TaggedForest (Option Bool) α (Logical ρ η) ι)
    (represented : ProjectionForest.Represents color
      ⟨annotate identifier color none (.fork low headPart (.fork high (.leaf depth terminal) tail)),[]⟩ (erase forest))
    (headerKey : α) (payload : Option Bool → α → Source β (Packet α (Logical ρ η) ι))
    (config : MultiSourceProgram.Configuration (Option Bool) β (Packet α (Logical ρ η) ι))
    (assembled : ForestConnector.assemble
      (ComponentPhysicalRepair.view none wingOrientation headerKey payload (encode forest))
      (ForestConnector.ThreeColors.layout (ComponentPhysicalRepair.view none wingOrientation headerKey payload (encode forest))) = some config) :
    ∃ (headLeft headRight tailLeft tailRight : Physical β α (Logical ρ η) ι) (actualFields : ActiveFields ι),
      headLeft.isSome = (packed color (some true) (annotate identifier color (some (identifier low)) headPart)).isSome ∧
      headRight.isSome = (packed color (some false) (annotate identifier color (some (identifier low)) headPart)).isSome ∧
      tailLeft.isSome = (packed color (some true) (annotate identifier color (some (identifier high)) tail)).isSome ∧
      tailRight.isSome = (packed color (some false) (annotate identifier color (some (identifier high)) tail)).isSome ∧
      some (config.tree.mapRecords (fun packet => (dummyId,packet))) =
        activeView actualFields direction
          (low,fields identifier color none (.fork low headPart (.fork high (.leaf depth terminal) tail)))
          (high,fields identifier color (some (identifier low)) (.fork high (.leaf depth terminal) tail))
          (terminal,fields identifier color (some (identifier high)) (.leaf depth terminal))
          (header forest) headLeft headRight tailLeft tailRight
          (some ((payload (some direction) depth).mapRecords (fun packet => (dummyId,packet))))
          ((payload none headerKey).mapRecords (fun packet => (dummyId,packet))) ∧
      CanonicalHeadWingViews.RootReady headLeft ∧ CanonicalHeadWingViews.RootReady headRight ∧
      CanonicalHeadWingViews.RootReady tailLeft ∧ CanonicalHeadWingViews.RootReady tailRight ∧
      CanonicalHeadWingViews.Canonical dummyId (payload (some true)) false
        (packed color (some true) (annotate identifier color (some (identifier low)) headPart)) headLeft ∧
      CanonicalHeadWingViews.Canonical dummyId (payload (some false)) true
        (packed color (some false) (annotate identifier color (some (identifier low)) headPart)) headRight ∧
      CanonicalHeadWingViews.Canonical dummyId (payload (some true)) false
        (packed color (some true) (annotate identifier color (some (identifier high)) tail)) tailLeft ∧
      CanonicalHeadWingViews.Canonical dummyId (payload (some false)) true
        (packed color (some false) (annotate identifier color (some (identifier high)) tail)) tailRight := by
  let source := annotate identifier color none (.fork low headPart (.fork high (.leaf depth terminal) tail))
  have erases (side : Bool) := packed_focus color source forest represented (some side)
  have leftPacking := (erases true).trans (AnnotatedHeadWingPacking.active identifier color true direction low high terminal depth headPart tail boundary)
  have rightPacking := (erases false).trans (AnnotatedHeadWingPacking.active identifier color false direction low high terminal depth headPart tail boundary)
  obtain ⟨headLeft,tailLeft,lowerLeft,upperLeft,leftId,leftFields,headLeftPresent,tailLeftPresent,leftView,headLeftReady,tailLeftReady,headLeftCanonical,tailLeftCanonical⟩ :=
    CanonicalHeadWingViews.active_canonical dummyId (payload (some true)) false none _ _ _ _ _ _ _ _ leftPacking
  obtain ⟨headRight,tailRight,lowerRight,upperRight,rightId,rightFields,headRightPresent,tailRightPresent,rightView,headRightReady,tailRightReady,headRightCanonical,tailRightCanonical⟩ :=
    CanonicalHeadWingViews.active_canonical dummyId (payload (some false)) true none _ _ _ _ _ _ _ _ rightPacking
  let actualFields : ActiveFields ι := ⟨lowerLeft,lowerRight,upperLeft,upperRight,
    if direction then leftId else rightId,if direction then leftFields else rightFields,⟨dummyId,dummyId⟩⟩
  have virtual := CanonicalPacketLayerViews.component_virtual none wingOrientation headerKey payload forest
  have assembly := CanonicalComponentAssembly.assembled dummyId _ _ virtual config assembled
  rw [real_piece dummyId color source forest represented none (some true) (by simp) wingOrientation headerKey payload,
    real_piece dummyId color source forest represented none (some false) (by simp) wingOrientation headerKey payload,
    virtual_piece dummyId none wingOrientation headerKey payload forest] at assembly
  change some (config.tree.mapRecords (fun packet => (dummyId,packet))) =
    physicalPrimaryJoin dummyId
      (physicalPrimaryJoin dummyId (render dummyId (payload (some true)) false none ((forest (some true)).map Cursor.focus))
        (some (MixedHeadInputView.rawBlock (header forest) ((payload none headerKey).mapRecords (fun packet => (dummyId,packet))))))
      (render dummyId (payload (some false)) true none ((forest (some false)).map Cursor.focus)) at assembly
  rw [leftView,rightView] at assembly
  refine ⟨headLeft,headRight,tailLeft,tailRight,actualFields,headLeftPresent,headRightPresent,tailLeftPresent,tailRightPresent,?_,
    headLeftReady,headRightReady,tailLeftReady,tailRightReady,headLeftCanonical,headRightCanonical,tailLeftCanonical,tailRightCanonical⟩
  cases direction <;>
    simp only [activeView,actualFields,CanonicalHeadWingViews.activeView,CanonicalHeadWingViews.orientedJoin,
      Bool.false_eq_true,reduceCtorEq,decide_false,decide_true,if_false,if_true,join_none_left,join_none_right] at assembly ⊢ <;>
    exact assembly

end ChaCha.Paper20261030.CanonicalPreparedComponentViews
