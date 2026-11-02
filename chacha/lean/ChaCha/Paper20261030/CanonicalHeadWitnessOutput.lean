import ChaCha.Paper20261030.CanonicalHeadOutput
import ChaCha.Paper20261030.CanonicalRetainedBlocks

set_option autoImplicit false

/-! The canonical block witnesses retained by the input decomposition
discharge all six repaired-routing inputs of the complete after-layout.
Ordinary ids come from the already derived `WingRoots` condition. -/

namespace ChaCha.Paper20261030.CanonicalRetainedBlocks

open ColoredStorage SourcePointer Structural PhysicalPacketStaging PacketLayers
open RepairedPayloadLayouts CanonicalHeadOutput

variable {α β ρ ι η : Type*}

theorem HeadWitnesses.after (markerId : ι) (bits : Fin 8 → Bool)
    (blocks : Fin 8 → Source β (Packet α (Logical ρ η) ι))
    (activePayload incomingPayload : Option Bool → α → Source β (Packet α (Logical ρ η) ι)) (headerKey : α)
    (head oldTail incomingTail : Bool → ProjectionLocal.Projected α (Logical ρ η))
    (witnesses : HeadWitnesses bits blocks activePayload incomingPayload headerKey head oldTail incomingTail)
    (ordinary : HeadPacketLayout.WingRoots markerId bits blocks)
    (good : Bool → α → Source β (Packet α (Logical ρ η) ι) → Prop)
    (headGood : ∀ side key, key ∈ ports (head side) → good side key (activePayload (some side) key))
    (incomingGood : ∀ side key, key ∈ ports (incomingTail side) → good side key (incomingPayload (some side) key))
    (direction : Bool) (depth : α) (records : HeadBoundary.Records ρ η (Option Bool))
    (newHeader dormantHeader : Packet α (Logical ρ η) ι)
    (childGood : ∀ body, Dormant (activePayload (some true)) (activePayload (some false))
      (oldTail true) (oldTail false) records.oldHigh dormantHeader (blocks 2) (some body) → good (!direction) depth body)
    (separate : ∀ side, Separate (head side) (incomingTail side))
    (headAbsent : ∀ side, depth ∉ ports (head side)) (incomingAbsent : ∀ side, depth ∉ ports (incomingTail side)) :
    RepairedComponentLayout.Represents markerId blocks (HeadPacketRepair.after bits direction newHeader.length dormantHeader.length)
      (HeadPacketLayout.after markerId bits direction records newHeader dormantHeader)
      (Active good (head true) (head false) (incomingTail true) (incomingTail false) direction depth records newHeader (blocks 5)) := by
  have headLeft := repaired markerId bits blocks 0 _ false _ witnesses.headLeft (ordinary 0 (by decide) (by decide))
  have headRight := repaired markerId bits blocks 7 _ true _ witnesses.headRight (ordinary 7 (by decide) (by decide))
  have oldLeft := repaired markerId bits blocks 1 _ false _ witnesses.oldLeft (ordinary 1 (by decide) (by decide))
  have oldRight := repaired markerId bits blocks 3 _ true _ witnesses.oldRight (ordinary 3 (by decide) (by decide))
  have incomingLeft := repaired markerId bits blocks 4 _ false _ witnesses.incomingLeft (ordinary 4 (by decide) (by decide))
  have incomingRight := repaired markerId bits blocks 6 _ true _ witnesses.incomingRight (ordinary 6 (by decide) (by decide))
  exact CanonicalHeadOutput.represents markerId blocks good (activePayload (some true)) (activePayload (some false)) bits direction depth records
    newHeader dormantHeader (head true) (head false) (oldTail true) (oldTail false) (incomingTail true) (incomingTail false)
    (fixed markerId blocks (good true) _ false _ _ _ headLeft (headGood true))
    (fixed markerId blocks (good false) _ true _ _ _ headRight (headGood false))
    (fixed markerId blocks (good true) _ false _ _ _ incomingLeft (incomingGood true))
    (fixed markerId blocks (good false) _ true _ _ _ incomingRight (incomingGood false))
    oldLeft oldRight childGood (separate true) (separate false)
    (headAbsent true) (headAbsent false) (incomingAbsent true) (incomingAbsent false)

end ChaCha.Paper20261030.CanonicalRetainedBlocks
