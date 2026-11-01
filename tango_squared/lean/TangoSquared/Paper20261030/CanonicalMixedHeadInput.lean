import TangoSquared.Paper20261030.CanonicalPreparedComponentViews
import TangoSquared.Paper20261030.PacketLayoutConditions
import TangoSquared.Paper20261030.CanonicalRetainedBlocks

/-!
# The mixed head input follows from two canonical component invariants

The active component contains the incoming component at its boundary
payload. Both forests represent the actual prepared, canonically annotated
sources and are assembled with the three-color connector. These facts
determine the eight opaque blocks and imply the `Stored` staging relation.
No finite physical input view is assumed.

The immutable-id alignment, reserved-marker exclusion, and placement of
the operational fingers remain separate execution invariants.
-/

namespace TangoSquared.Paper20261030.CanonicalMixedHeadInput

open ColoredStorage SourcePointer Structural HeadBoundary PhysicalForestMetadata PhysicalPacketStaging
open PacketLayers CanonicalPreparedComponentViews LocalComponentCompiler

variable {α β ρ ι η : Type*} [DecidableEq α]

local instance : LinearOrder (Option Bool) := inferInstanceAs (LinearOrder (WithBot Bool))

private theorem augmentation_erases (dummyId : ι) (source : Source β (Packet α (Logical ρ η) ι)) :
    (source.mapRecords (fun packet => (dummyId,packet))).mapRecords Prod.snd = source := by
  induction source <;> simp_all only [Source.mapRecords]

private theorem presence (identifier : ρ → η) (color : α → Option Bool) (side : Bool)
    (parent : Option η) (source : Source α ρ) :
    (packed color (some side) (annotate identifier color parent source)).isSome = decide (some side ∈ source.support color) := by
  rw [PackedRotationController.packed_isSome,ObservedHeadBlueprint.annotate_support]

theorem input (markerId : ι) (identifier : ρ → η) (activeColor incomingColor : α → Option Bool)
    (low oldHigh incomingHigh oldTerminal incomingTerminal : ρ) (depth : α)
    (headPart oldTail incomingTail : Source α ρ) (direction : Bool)
    (boundary : activeColor depth = some direction) (sentinel : incomingColor depth = none)
    (activeForest incomingForest : TaggedForest (Option Bool) α (Logical ρ η) ι)
    (activeRep : ProjectionForest.Represents activeColor
      ⟨annotate identifier activeColor none (.fork low headPart (.fork oldHigh (.leaf depth oldTerminal) oldTail)),[]⟩ (erase activeForest))
    (incomingRep : ProjectionForest.Represents incomingColor
      ⟨annotate identifier incomingColor none (.fork incomingHigh (.leaf depth incomingTerminal) incomingTail),[]⟩ (erase incomingForest))
    (headerKey : α) (activePayload incomingPayload : Option Bool → α → Source β (Packet α (Logical ρ η) ι))
    (activeConfig incomingConfig : MultiSourceProgram.Configuration (Option Bool) β (Packet α (Logical ρ η) ι))
    (activeAssembled : ForestConnector.assemble
      (ComponentPhysicalRepair.view none wingOrientation headerKey activePayload (encode activeForest))
      (ForestConnector.ThreeColors.layout (ComponentPhysicalRepair.view none wingOrientation headerKey activePayload (encode activeForest))) = some activeConfig)
    (incomingAssembled : ForestConnector.assemble
      (ComponentPhysicalRepair.view none wingOrientation headerKey incomingPayload (encode incomingForest))
      (ForestConnector.ThreeColors.layout (ComponentPhysicalRepair.view none wingOrientation headerKey incomingPayload (encode incomingForest))) = some incomingConfig)
    (attached : activePayload (some direction) depth = incomingConfig.tree)
    (actual : Source β (PacketLayers.Context.Cell α (Logical ρ η) ι))
    (actualErases : actual.mapRecords Prod.snd = activeConfig.tree) :
    let records := observed identifier activeColor incomingColor low oldHigh incomingHigh oldTerminal incomingTerminal
      depth headPart oldTail incomingTail
    ∃ (blocks : Fin 8 → Source β (Packet α (Logical ρ η) ι))
      (layout : Source (Fin 8) (Expression α (Logical ρ η) ι)),
      HeadPacketLayout.before markerId (ObservedHeadBlueprint.bits records) direction records
        (header activeForest) (header incomingForest) = some layout ∧
      Reached.Stored blocks layout actual ∧
      PacketConditions.wings (fun base => Ready base (.prefix [])) (ObservedHeadBlueprint.bits records) blocks ∧
      CanonicalRetainedBlocks.HeadWitnesses (ObservedHeadBlueprint.bits records) blocks activePayload incomingPayload headerKey
        (fun side => packed activeColor (some side) (annotate identifier activeColor (some (identifier low)) headPart))
        (fun side => packed activeColor (some side) (annotate identifier activeColor (some (identifier oldHigh)) oldTail))
        (fun side => packed incomingColor (some side) (annotate identifier incomingColor (some (identifier incomingHigh)) incomingTail)) := by
  dsimp only
  let records := observed identifier activeColor incomingColor low oldHigh incomingHigh oldTerminal incomingTerminal
    depth headPart oldTail incomingTail
  obtain ⟨headLeft,headRight,tailLeft,tailRight,actualFields,headLeftPresent,headRightPresent,tailLeftPresent,tailRightPresent,
    activeView,headLeftReady,headRightReady,tailLeftReady,tailRightReady,headLeftCanonical,headRightCanonical,tailLeftCanonical,tailRightCanonical⟩ :=
    CanonicalPreparedComponentViews.active markerId identifier activeColor low oldHigh oldTerminal depth headPart oldTail direction
      boundary activeForest activeRep headerKey activePayload activeConfig activeAssembled
  obtain ⟨incomingLeft,incomingRight,incomingLeftPresent,incomingRightPresent,incomingView,incomingLeftReady,incomingRightReady,incomingLeftCanonical,incomingRightCanonical⟩ :=
    CanonicalPreparedComponentViews.dormant markerId identifier incomingColor incomingHigh incomingTerminal depth incomingTail
      sentinel incomingForest incomingRep headerKey incomingPayload incomingConfig incomingAssembled
  rw [attached] at activeView
  let oldBottom := (activePayload none headerKey).mapRecords (fun packet => (markerId,packet))
  let newBottom := (incomingPayload none headerKey).mapRecords (fun packet => (markerId,packet))
  let pieces : Fin 8 → MixedHeadInputView.Physical β α (Logical ρ η) ι := fun key => match key.val with
    | 0 => headLeft
    | 1 => tailLeft
    | 2 => some oldBottom
    | 3 => tailRight
    | 4 => incomingLeft
    | 5 => some newBottom
    | 6 => incomingRight
    | _ => headRight
  have bits : ∀ key, ObservedHeadBlueprint.bits records key = (pieces key).isSome := by
    intro key
    fin_cases key
    · exact (headLeftPresent.trans (presence identifier activeColor true _ headPart)).symm
    · exact (tailLeftPresent.trans (presence identifier activeColor true _ oldTail)).symm
    · rfl
    · exact (tailRightPresent.trans (presence identifier activeColor false _ oldTail)).symm
    · exact (incomingLeftPresent.trans (presence identifier incomingColor true _ incomingTail)).symm
    · rfl
    · exact (incomingRightPresent.trans (presence identifier incomingColor false _ incomingTail)).symm
    · exact (headRightPresent.trans (presence identifier activeColor false _ headPart)).symm
  let sources : Fin 8 → Source β (PacketLayers.Context.Cell α (Logical ρ η) ι) := fun key => (pieces key).getD oldBottom
  let blocks : Fin 8 → Source β (Packet α (Logical ρ η) ι) := fun key => (sources key).mapRecords Prod.snd
  have pieceReady (key : Fin 8) (not2 : key ≠ 2) (not5 : key ≠ 5) : CanonicalHeadWingViews.RootReady (pieces key) := by
    fin_cases key
    · exact headLeftReady
    · exact tailLeftReady
    · exact False.elim (not2 rfl)
    · exact tailRightReady
    · exact incomingLeftReady
    · exact False.elim (not5 rfl)
    · exact incomingRightReady
    · exact headRightReady
  have wingReady : PacketConditions.wings (fun base => Ready base (.prefix [])) (ObservedHeadBlueprint.bits records) blocks := by
    intro key not2 not5 present
    rw [bits key] at present
    cases found : pieces key with
    | none => simp only [found,Option.isSome_none,reduceCtorEq] at present
    | some source =>
      have ready := pieceReady key not2 not5 source found
      simpa only [blocks,sources,found,Option.getD_some,Source.mapRecords_root] using ready
  have witnesses : CanonicalRetainedBlocks.HeadWitnesses (ObservedHeadBlueprint.bits records) blocks activePayload incomingPayload headerKey
      (fun side => packed activeColor (some side) (annotate identifier activeColor (some (identifier low)) headPart))
      (fun side => packed activeColor (some side) (annotate identifier activeColor (some (identifier oldHigh)) oldTail))
      (fun side => packed incomingColor (some side) (annotate identifier incomingColor (some (identifier incomingHigh)) incomingTail)) := by
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
    · exact CanonicalRetainedBlocks.of_piece markerId _ blocks 0 _ false _ (pieces 0) oldBottom headLeftCanonical (bits 0) rfl
    · exact CanonicalRetainedBlocks.of_piece markerId _ blocks 7 _ true _ (pieces 7) oldBottom headRightCanonical (bits 7) rfl
    · exact CanonicalRetainedBlocks.of_piece markerId _ blocks 1 _ false _ (pieces 1) oldBottom tailLeftCanonical (bits 1) rfl
    · exact CanonicalRetainedBlocks.of_piece markerId _ blocks 3 _ true _ (pieces 3) oldBottom tailRightCanonical (bits 3) rfl
    · exact CanonicalRetainedBlocks.of_piece markerId _ blocks 4 _ false _ (pieces 4) oldBottom incomingLeftCanonical (bits 4) rfl
    · exact CanonicalRetainedBlocks.of_piece markerId _ blocks 6 _ true _ (pieces 6) oldBottom incomingRightCanonical (bits 6) rfl
    · exact augmentation_erases markerId _
    · exact augmentation_erases markerId _
  have blockView (key : Fin 8) : MixedHeadInputView.block (ObservedHeadBlueprint.bits records) sources key = pieces key := by
    rw [MixedHeadInputView.block,bits key]
    cases found : pieces key <;> simp only [Option.isSome_none,Option.isSome_some,Bool.false_eq_true,if_false,if_true]
    simp only [sources,found,Option.getD_some]
  have incomingExact : MixedHeadInputView.dormant (ObservedHeadBlueprint.bits records) sources 4 5 6
      ⟨markerId,markerId⟩ records.incomingHigh (header incomingForest) =
        some (incomingConfig.tree.mapRecords (fun packet => (markerId,packet))) := by
    unfold MixedHeadInputView.dormant
    rw [blockView,blockView]
    exact incomingView.symm
  have beforeExact : MixedHeadInputView.before (ObservedHeadBlueprint.bits records) sources actualFields ⟨markerId,markerId⟩ direction
      records (header activeForest) (header incomingForest) = some (activeConfig.tree.mapRecords (fun packet => (markerId,packet))) := by
    unfold MixedHeadInputView.before
    rw [incomingExact]
    unfold MixedHeadInputView.active
    rw [blockView,blockView,blockView,blockView]
    exact activeView.symm
  have stored := MixedHeadInputView.before_stored markerId (ObservedHeadBlueprint.bits records) sources blocks (fun _ => rfl)
    actualFields ⟨markerId,markerId⟩ direction records (header activeForest) (header incomingForest)
  rw [beforeExact] at stored
  cases found : HeadPacketLayout.before markerId (ObservedHeadBlueprint.bits records) direction records
      (header activeForest) (header incomingForest) with
  | none =>
    rw [found] at stored
    exact False.elim stored
  | some layout =>
    rw [found] at stored
    refine ⟨blocks,layout,rfl,Reached.stored_of_erasure blocks layout _ actual stored ?_,wingReady,witnesses⟩
    exact (augmentation_erases markerId activeConfig.tree).trans actualErases.symm

end TangoSquared.Paper20261030.CanonicalMixedHeadInput
