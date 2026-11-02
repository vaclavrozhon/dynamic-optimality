import ChaCha.Paper20261030.CanonicalActiveOutput

set_option autoImplicit false

/-! The complete after-layout reconstructs the old tails as a dormant
component and places it inside the new active component. This composes
the canonical output predicates for the exact eight-block exchange.
Its input witnesses describe the six retained real projections and their
port sets; deriving those witnesses from the full primary invariant is
a separate input-decomposition obligation. -/

namespace ChaCha.Paper20261030.CanonicalHeadOutput

open ColoredStorage SourcePointer Structural PhysicalPacketStaging PacketLayers
open CanonicalPacketLayerViews RepairedPayloadLayouts

variable {α β ρ ι η : Type*}

local instance : LinearOrder (Option Bool) := inferInstanceAs (LinearOrder (WithBot Bool))

abbrev Logical (ρ η : Type*) := HeadBoundary.Record ρ η (Option Bool)

def Dormant (leftPayload rightPayload : α → Source β (Packet α (Logical ρ η) ι))
    (leftPlain rightPlain : ProjectionLocal.Projected α (Logical ρ η))
    (high : Logical ρ η) (header : Packet α (Logical ρ η) ι) (bottom : Source β (Packet α (Logical ρ η) ι)) :=
  CanonicalRepairedDormant.Result leftPayload rightPayload
    (ProjectionLocal.decorate (ObservedHeadBlueprint.owned (some true) high) leftPlain)
    (ProjectionLocal.decorate (ObservedHeadBlueprint.owned (some false) high) rightPlain) header bottom

def Active (good : Bool → α → Source β (Packet α (Logical ρ η) ι) → Prop)
    (headLeft headRight tailLeft tailRight : ProjectionLocal.Projected α (Logical ρ η))
    (direction : Bool) (depth : α) (records : HeadBoundary.Records ρ η (Option Bool))
    (header : Packet α (Logical ρ η) ι) (bottom : Source β (Packet α (Logical ρ η) ι)) :=
  CanonicalRepairedActive.Result good
    (CanonicalHeadWingViews.activePacked headLeft tailLeft depth (!direction)
      (ObservedHeadBlueprint.owned (some true) records.low) (ObservedHeadBlueprint.owned (some true) records.incomingHigh) records.incomingTerminal)
    (CanonicalHeadWingViews.activePacked headRight tailRight depth direction
      (ObservedHeadBlueprint.owned (some false) records.low) (ObservedHeadBlueprint.owned (some false) records.incomingHigh) records.incomingTerminal)
    header bottom

theorem represents (markerId : ι) (blocks : Fin 8 → Source β (Packet α (Logical ρ η) ι))
    (good : Bool → α → Source β (Packet α (Logical ρ η) ι) → Prop)
    (oldLeftPayload oldRightPayload : α → Source β (Packet α (Logical ρ η) ι))
    (bits : Fin 8 → Bool) (direction : Bool) (depth : α) (records : HeadBoundary.Records ρ η (Option Bool))
    (newHeader dormantHeader : Packet α (Logical ρ η) ι)
    (headLeft headRight oldLeft oldRight incomingLeft incomingRight : ProjectionLocal.Projected α (Logical ρ η))
    (headLeftRep : Layout markerId blocks (good true) false headLeft (HeadPacketRepair.block bits 0) (HeadPacketLayout.block bits 0))
    (headRightRep : Layout markerId blocks (good false) true headRight (HeadPacketRepair.block bits 7) (HeadPacketLayout.block bits 7))
    (incomingLeftRep : Layout markerId blocks (good true) false incomingLeft (HeadPacketRepair.block bits 4) (HeadPacketLayout.block bits 4))
    (incomingRightRep : Layout markerId blocks (good false) true incomingRight (HeadPacketRepair.block bits 6) (HeadPacketLayout.block bits 6))
    (oldLeftRep : CanonicalRepairedRouting.Layout markerId blocks oldLeftPayload false oldLeft
      (HeadPacketRepair.block bits 1) (HeadPacketLayout.block bits 1))
    (oldRightRep : CanonicalRepairedRouting.Layout markerId blocks oldRightPayload true oldRight
      (HeadPacketRepair.block bits 3) (HeadPacketLayout.block bits 3))
    (childGood : ∀ body, Dormant oldLeftPayload oldRightPayload oldLeft oldRight records.oldHigh dormantHeader (blocks 2) (some body) →
      good (!direction) depth body)
    (leftSeparate : Separate headLeft incomingLeft) (rightSeparate : Separate headRight incomingRight)
    (headLeftAbsent : depth ∉ ports headLeft) (headRightAbsent : depth ∉ ports headRight)
    (incomingLeftAbsent : depth ∉ ports incomingLeft) (incomingRightAbsent : depth ∉ ports incomingRight) :
    RepairedComponentLayout.Represents markerId blocks (HeadPacketRepair.after bits direction newHeader.length dormantHeader.length)
      (HeadPacketLayout.after markerId bits direction records newHeader dormantHeader)
      (Active good headLeft headRight incomingLeft incomingRight direction depth records newHeader (blocks 5)) := by
  have dormant := CanonicalRepairedDormant.represents markerId blocks oldLeftPayload oldRightPayload bits 1 2 3 records.oldHigh
    dormantHeader oldLeft oldRight oldLeftRep oldRightRep
  have active := CanonicalRepairedActive.represents markerId blocks good bits 0 7 4 5 6 _ _ (!direction)
    records.low records.incomingHigh records.incomingTerminal newHeader depth headLeft headRight incomingLeft incomingRight
    headLeftRep headRightRep incomingLeftRep incomingRightRep _ dormant
    (CanonicalRepairedDormant.result_present _ _ _ _ _ _) childGood leftSeparate rightSeparate
    headLeftAbsent headRightAbsent incomingLeftAbsent incomingRightAbsent
  simp only [HeadPacketRepair.after,HeadPacketLayout.after,Active,Bool.not_not] at active ⊢
  exact active

end ChaCha.Paper20261030.CanonicalHeadOutput
