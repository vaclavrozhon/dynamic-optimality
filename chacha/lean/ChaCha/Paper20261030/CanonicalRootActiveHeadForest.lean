import ChaCha.Paper20261030.ComputedComponentReconstruction
import ChaCha.Paper20261030.RootHeadRealOutputShapes
import ChaCha.Paper20261030.CanonicalHeadSuccessor

set_option autoImplicit false

/-! Reconstruct the active forest after a minimum-depth exchange. The
incoming high record is the new source root. The dormant component and
all unchanged payloads retain their canonical physical representations. -/

namespace ChaCha.Paper20261030.CanonicalRootActiveHeadForest

open ColoredStorage SourcePointer Structural HeadBoundary PhysicalForestMetadata PhysicalPacketStaging
open LocalComponentCompiler RepairedPayloadLayouts

variable {α β ρ η : Type*} [DecidableEq α]

local instance canonicalRootActiveHeadForestColorOrder : LinearOrder (Option Bool) :=
  inferInstanceAs (LinearOrder (WithBot Bool))

set_option backward.isDefEq.respectTransparency false in
theorem reconstruct (markerId : Nat) (identifier : ρ → η)
    (oldColor incomingColor newColor : α → Option Bool)
    (oldHigh incomingHigh incomingTerminal : ρ) (depth : α) (direction : Bool)
    (oldTail incomingTail : Source α ρ) (fresh : Records ρ η (Option Bool))
    (noPrefix : ∀ side, ObservedHeadBlueprint.owned (some side) fresh.low = [])
    (view : Source.fork fresh.incomingHigh (.leaf depth fresh.incomingTerminal)
      (annotate identifier incomingColor (some (identifier incomingHigh)) incomingTail) =
      annotate identifier newColor none (.fork incomingHigh (.leaf depth incomingTerminal) incomingTail))
    (boundary : newColor depth = some (!direction))
    (tailColors : ∀ key ∈ incomingTail.shape.leaves, incomingColor key = newColor key)
    (activePayload incomingPayload : Option Bool → α → Source β (Packet α (HeadBoundary.Record ρ η (Option Bool)) Nat))
    (headerKey : α)
    (stored : VirtualHeadPacketController.Physical α ρ η)
    (dormantHeader : Packet α (HeadBoundary.Record ρ η (Option Bool)) Nat)
    (ready : VirtualPhysicalPackets.Ready stored)
    (decoded : VirtualPhysicalPackets.decode stored =
      (packed newColor none (annotate identifier newColor none
        (.fork incomingHigh (.leaf depth incomingTerminal) incomingTail))).map (fun tree => ⟨tree,[]⟩))
    (actual : Source β (PacketLayers.Context.Cell α (HeadBoundary.Record ρ η (Option Bool)) Nat))
    (valid : CanonicalComponentUniqueness.Valid markerId actual)
    (result : CanonicalHeadSuccessor.Result activePayload incomingPayload
      (fun _ => none)
      (fun side => packed oldColor (some side) (annotate identifier oldColor (some (identifier oldHigh)) oldTail))
      (fun side => packed incomingColor (some side) (annotate identifier incomingColor (some (identifier incomingHigh)) incomingTail))
      direction depth fresh [some (.header stored),none] dormantHeader
      (activePayload none headerKey) (incomingPayload none headerKey) (some (actual.mapRecords Prod.snd))) :
    let source := annotate identifier newColor none (.fork incomingHigh (.leaf depth incomingTerminal) incomingTail)
    let good := CanonicalHeadSuccessor.Payload activePayload incomingPayload
      (fun _ => none)
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
  have left := HeadRealOutputShapes.root_active identifier incomingColor newColor incomingHigh incomingTerminal
    depth true (!direction) incomingTail fresh (noPrefix true) view boundary tailColors
  have right := HeadRealOutputShapes.root_active identifier incomingColor newColor incomingHigh incomingTerminal
    depth false (!direction) incomingTail fresh (noPrefix false) view boundary tailColors
  have leftBit : decide (true = !direction) = !direction := by cases direction <;> rfl
  have rightBit : decide (false = !direction) = direction := by cases direction <;> rfl
  rw [leftBit] at left
  rw [rightBit] at right
  unfold CanonicalHeadSuccessor.Result CanonicalHeadOutput.Active at result
  rw [← left,← right] at result
  exact ComputedComponentReconstruction.active markerId newColor _ _ (incomingPayload none headerKey)
    stored ready decoded actual valid result headerKey

end ChaCha.Paper20261030.CanonicalRootActiveHeadForest
