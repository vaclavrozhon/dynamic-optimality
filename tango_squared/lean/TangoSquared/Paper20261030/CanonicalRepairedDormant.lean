import TangoSquared.Paper20261030.RepairedComponentLayout

set_option autoImplicit false

/-!
# Canonical real wings and the exact virtual bottom of the new dormant component

The two opaque tails retain their internal tagged projections. Their
new logical root prefixes are the owned records of the repaired dormant
root. Repacking and the mixed repair yield precisely the canonical
physical annotation of these projections, joined with the supplied raw
virtual header and unchanged bottom payload.
-/

namespace TangoSquared.Paper20261030.CanonicalRepairedDormant

open ColoredStorage SourcePointer Structural PhysicalPacketStaging PacketLayers
open CanonicalPacketLayerViews MixedPacketRepair

variable {α β ρ ι η : Type*}

local instance : LinearOrder (Option Bool) := inferInstanceAs (LinearOrder (WithBot Bool))

abbrev Logical (ρ η : Type*) := HeadBoundary.Record ρ η (Option Bool)

def view (leftPayload rightPayload : α → Source β (Packet α ρ ι))
    (left right : Option (Tagged α ρ ι)) (header : Packet α ρ ι) (bottom : Source β (Packet α ρ ι)) :=
  ProjectionLocal.join
    (ProjectionLocal.join (left.map (routing leftPayload false none))
      (some (bottom.setRoot (header++bottom.rootRecord))))
    (right.map (routing rightPayload true none))

def Result (leftPayload rightPayload : α → Source β (Packet α ρ ι))
    (leftPlain rightPlain : ProjectionLocal.Projected α ρ)
    (header : Packet α ρ ι) (bottom : Source β (Packet α ρ ι))
    (result : RepairedComponentLayout.View β α ρ ι) : Prop :=
  ∃ left right : Option (Tagged α ρ ι),
    left.map (Source.mapRecords Prod.snd) = leftPlain ∧ right.map (Source.mapRecords Prod.snd) = rightPlain ∧
    result = view leftPayload rightPayload left right header bottom

theorem result_present (leftPayload rightPayload : α → Source β (Packet α ρ ι))
    (leftPlain rightPlain : ProjectionLocal.Projected α ρ)
    (header : Packet α ρ ι) (bottom : Source β (Packet α ρ ι)) :
    ¬ Result leftPayload rightPayload leftPlain rightPlain header bottom none := by
  rintro ⟨left,right,_,_,equal⟩
  cases left <;> cases right <;> cases equal

theorem represents (markerId : ι) (blocks : Fin 8 → Source β (Packet α (Logical ρ η) ι))
    (leftPayload rightPayload : α → Source β (Packet α (Logical ρ η) ι))
    (bits : Fin 8 → Bool) (l b r : Fin 8) (high : Logical ρ η) (header : Packet α (Logical ρ η) ι)
    (leftPlain rightPlain : ProjectionLocal.Projected α (Logical ρ η))
    (leftRep : CanonicalRepairedRouting.Layout markerId blocks leftPayload false leftPlain
      (HeadPacketRepair.block bits l) (HeadPacketLayout.block bits l))
    (rightRep : CanonicalRepairedRouting.Layout markerId blocks rightPayload true rightPlain
      (HeadPacketRepair.block bits r) (HeadPacketLayout.block bits r)) :
    RepairedComponentLayout.Represents markerId blocks (HeadPacketRepair.dormant bits l b r header.length)
      (HeadPacketLayout.dormant markerId bits l b r high header)
      (Result leftPayload rightPayload
        (ProjectionLocal.decorate (ObservedHeadBlueprint.owned (some true) high) leftPlain)
        (ProjectionLocal.decorate (ObservedHeadBlueprint.owned (some false) high) rightPlain) header (blocks b)) := by
  have left := RepairedComponentLayout.routing markerId blocks leftPayload false _ _ _
    (CanonicalRepairedRouting.logical_layout markerId blocks leftPayload false _ _ _ leftRep (ObservedHeadBlueprint.owned (some true) high))
  have right := RepairedComponentLayout.routing markerId blocks rightPayload true _ _ _
    (CanonicalRepairedRouting.logical_layout markerId blocks rightPayload true _ _ _ rightRep (ObservedHeadBlueprint.owned (some false) high))
  have bottom := RepairedComponentLayout.bottom markerId blocks b header
  have first := RepairedComponentLayout.primaryJoin markerId blocks _ _ _ _ _ _ left bottom
  have all := RepairedComponentLayout.primaryJoin markerId blocks _ _ _ _ _ _ first right
  apply RepairedComponentLayout.weaken markerId blocks _ _ _ _ all
  intro result property
  obtain ⟨firstView,rightView,⟨leftView,bottomView,⟨left,leftErases,leftEqual⟩,bottomEqual,firstEqual⟩,
    ⟨right,rightErases,rightEqual⟩,resultEqual⟩ := property
  exact ⟨left,right,leftErases,rightErases,by rw [resultEqual,firstEqual,leftEqual,bottomEqual,rightEqual]; rfl⟩

end TangoSquared.Paper20261030.CanonicalRepairedDormant
