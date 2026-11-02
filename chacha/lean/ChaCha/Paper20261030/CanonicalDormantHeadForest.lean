import ChaCha.Paper20261030.ComputedComponentReconstruction
import ChaCha.Paper20261030.HeadRealOutputShapes
import ChaCha.Paper20261030.CanonicalHeadSuccessor

set_option autoImplicit false

/-! The dormant component produced by the head exchange has the maintained
forest representation for the old tail. The stored virtual header and
the two repaired real wings determine all three projections. -/

namespace ChaCha.Paper20261030.CanonicalDormantHeadForest

open ColoredStorage SourcePointer Structural HeadBoundary PhysicalForestMetadata PhysicalPacketStaging
open LocalComponentCompiler RepairedPayloadLayouts

variable {α β ρ η : Type*} [DecidableEq α]

local instance canonicalDormantHeadForestColorOrder : LinearOrder (Option Bool) :=
  inferInstanceAs (LinearOrder (WithBot Bool))

set_option backward.isDefEq.respectTransparency false in
theorem reconstruct (markerId : Nat) (identifier : ρ → η)
    (oldColor dormantColor : α → Option Bool)
    (oldHigh oldTerminal : ρ) (depth : α) (oldTail : Source α ρ) (fresh : Records ρ η (Option Bool))
    (view : dormantTree fresh depth (annotate identifier oldColor (some (identifier oldHigh)) oldTail) =
      annotate identifier dormantColor none (.fork oldHigh (.leaf depth oldTerminal) oldTail))
    (boundary : dormantColor depth = none)
    (tailColors : ∀ key ∈ oldTail.shape.leaves, oldColor key = dormantColor key)
    (activePayload : Option Bool → α → Source β (Packet α (HeadBoundary.Record ρ η (Option Bool)) Nat))
    (headerKey : α) (stored : VirtualHeadPacketController.Physical α ρ η)
    (ready : VirtualPhysicalPackets.Ready stored)
    (decoded : VirtualPhysicalPackets.decode stored =
      (packed dormantColor none (annotate identifier dormantColor none
        (.fork oldHigh (.leaf depth oldTerminal) oldTail))).map (fun tree => ⟨tree,[]⟩))
    (actual : Source β (PacketLayers.Context.Cell α (HeadBoundary.Record ρ η (Option Bool)) Nat))
    (valid : CanonicalComponentUniqueness.Valid markerId actual)
    (result : CanonicalHeadOutput.Dormant (activePayload (some true)) (activePayload (some false))
      (packed oldColor (some true) (annotate identifier oldColor (some (identifier oldHigh)) oldTail))
      (packed oldColor (some false) (annotate identifier oldColor (some (identifier oldHigh)) oldTail))
      fresh.oldHigh [some (.header stored),none] (activePayload none headerKey) (some (actual.mapRecords Prod.snd))) :
    let source := annotate identifier dormantColor none (.fork oldHigh (.leaf depth oldTerminal) oldTail)
    ∃ forest config,
      ProjectionForest.Represents dormantColor ⟨source,[]⟩ (erase forest) ∧ Unique forest ∧
      ForestConnector.assemble
        (ComponentPhysicalRepair.view none wingOrientation headerKey
          (ComputedComponentReconstruction.payload (activePayload (some true)) (activePayload (some false)) (activePayload none headerKey)) (encode forest))
        (ForestConnector.ThreeColors.layout (ComponentPhysicalRepair.view none wingOrientation headerKey
          (ComputedComponentReconstruction.payload (activePayload (some true)) (activePayload (some false)) (activePayload none headerKey)) (encode forest))) = some config ∧
      config.tree = actual.mapRecords Prod.snd := by
  dsimp only
  have left := HeadRealOutputShapes.dormant identifier oldColor dormantColor oldHigh oldTerminal depth true oldTail fresh view boundary tailColors
  have right := HeadRealOutputShapes.dormant identifier oldColor dormantColor oldHigh oldTerminal depth false oldTail fresh view boundary tailColors
  unfold CanonicalHeadOutput.Dormant at result
  rw [← left,← right] at result
  exact ComputedComponentReconstruction.dormant markerId dormantColor _ (activePayload (some true)) (activePayload (some false))
    (activePayload none headerKey) stored ready decoded actual valid result headerKey

end ChaCha.Paper20261030.CanonicalDormantHeadForest
