import ChaCha.Paper20261030.ComputedComponentReconstruction
import ChaCha.Paper20261030.HeadRealOutputShapes
import ChaCha.Paper20261030.CanonicalHeadSuccessor

set_option autoImplicit false

/-! The canonical head-successor output determines an actual maintained
forest for the new active component. Its payload predicate still identifies
the dormant component at the switched boundary and every retained payload.
Both real projections are derived from the structural output views. -/

namespace ChaCha.Paper20261030.CanonicalActiveHeadForest

open ColoredStorage SourcePointer Structural HeadBoundary PhysicalForestMetadata PhysicalPacketStaging
open LocalComponentCompiler RepairedPayloadLayouts

variable {α β ρ η : Type*} [DecidableEq α]

local instance canonicalActiveHeadForestColorOrder : LinearOrder (Option Bool) :=
  inferInstanceAs (LinearOrder (WithBot Bool))

set_option backward.isDefEq.respectTransparency false in
theorem reconstruct (markerId : Nat) (identifier : ρ → η)
    (oldColor incomingColor newColor : α → Option Bool)
    (low oldHigh incomingHigh incomingTerminal : ρ) (depth : α) (direction : Bool)
    (headPart oldTail incomingTail : Source α ρ) (fresh : Records ρ η (Option Bool))
    (view : activeTree fresh depth
      (annotate identifier oldColor (some (identifier low)) headPart)
      (annotate identifier incomingColor (some (identifier incomingHigh)) incomingTail) =
      annotate identifier newColor none (.fork low headPart (.fork incomingHigh (.leaf depth incomingTerminal) incomingTail)))
    (boundary : newColor depth = some (!direction))
    (headColors : ∀ key ∈ headPart.shape.leaves, oldColor key = newColor key)
    (tailColors : ∀ key ∈ incomingTail.shape.leaves, incomingColor key = newColor key)
    (activePayload incomingPayload : Option Bool → α → Source β (Packet α (HeadBoundary.Record ρ η (Option Bool)) Nat))
    (headerKey : α)
    (stored : VirtualHeadPacketController.Physical α ρ η)
    (dormantHeader : Packet α (HeadBoundary.Record ρ η (Option Bool)) Nat)
    (ready : VirtualPhysicalPackets.Ready stored)
    (decoded : VirtualPhysicalPackets.decode stored =
      (packed newColor none (annotate identifier newColor none
        (.fork low headPart (.fork incomingHigh (.leaf depth incomingTerminal) incomingTail)))).map (fun tree => ⟨tree,[]⟩))
    (actual : Source β (PacketLayers.Context.Cell α (HeadBoundary.Record ρ η (Option Bool)) Nat))
    (valid : CanonicalComponentUniqueness.Valid markerId actual)
    (result : CanonicalHeadSuccessor.Result activePayload incomingPayload
      (fun side => packed oldColor (some side) (annotate identifier oldColor (some (identifier low)) headPart))
      (fun side => packed oldColor (some side) (annotate identifier oldColor (some (identifier oldHigh)) oldTail))
      (fun side => packed incomingColor (some side) (annotate identifier incomingColor (some (identifier incomingHigh)) incomingTail))
      direction depth fresh [some (.header stored),none] dormantHeader
      (activePayload none headerKey) (incomingPayload none headerKey) (some (actual.mapRecords Prod.snd))) :
    let source := annotate identifier newColor none (.fork low headPart (.fork incomingHigh (.leaf depth incomingTerminal) incomingTail))
    let good := CanonicalHeadSuccessor.Payload activePayload incomingPayload
      (fun side => packed oldColor (some side) (annotate identifier oldColor (some (identifier low)) headPart))
      (fun side => packed oldColor (some side) (annotate identifier oldColor (some (identifier oldHigh)) oldTail))
      (fun side => packed incomingColor (some side) (annotate identifier incomingColor (some (identifier incomingHigh)) incomingTail))
      direction depth fresh dormantHeader (activePayload none headerKey)
    ∃ leftPayload rightPayload forest config,
      ProjectionForest.Represents newColor ⟨source,[]⟩ (erase forest) ∧ Unique forest ∧
      ForestConnector.assemble
        (ComponentPhysicalRepair.view none wingOrientation headerKey
          (ComputedComponentReconstruction.payload leftPayload rightPayload (incomingPayload none headerKey)) (encode forest))
        (ForestConnector.ThreeColors.layout (ComponentPhysicalRepair.view none wingOrientation headerKey
          (ComputedComponentReconstruction.payload leftPayload rightPayload (incomingPayload none headerKey)) (encode forest))) = some config ∧
      config.tree = actual.mapRecords Prod.snd ∧
      ∀ side key, key ∈ ports (packed newColor (some side) source) →
        good side key (ComputedComponentReconstruction.payload leftPayload rightPayload (incomingPayload none headerKey) (some side) key) := by
  dsimp only
  have left := HeadRealOutputShapes.active identifier oldColor incomingColor newColor low incomingHigh incomingTerminal
    depth true (!direction) headPart incomingTail fresh view boundary headColors tailColors
  have right := HeadRealOutputShapes.active identifier oldColor incomingColor newColor low incomingHigh incomingTerminal
    depth false (!direction) headPart incomingTail fresh view boundary headColors tailColors
  have leftBit : decide (true = !direction) = !direction := by cases direction <;> rfl
  have rightBit : decide (false = !direction) = direction := by cases direction <;> rfl
  rw [leftBit] at left
  rw [rightBit] at right
  unfold CanonicalHeadSuccessor.Result CanonicalHeadOutput.Active at result
  rw [← left,← right] at result
  exact ComputedComponentReconstruction.active markerId newColor _ _ (incomingPayload none headerKey)
    stored ready decoded actual valid result headerKey

end ChaCha.Paper20261030.CanonicalActiveHeadForest
