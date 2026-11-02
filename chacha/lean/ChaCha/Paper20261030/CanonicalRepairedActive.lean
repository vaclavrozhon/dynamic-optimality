import ChaCha.Paper20261030.CanonicalRepairedWing
import ChaCha.Paper20261030.CanonicalRepairedDormant

set_option autoImplicit false

/-!
# Canonical pieces of the repaired active component

The boundary payload is a reconstructed component satisfying `predicate`.
The active wing containing that boundary retains this predicate at its
terminal, while all other port payloads retain their supplied invariants.
The result is a canonical three-piece component with both real routing
projections and the exact virtual bottom. No future connector identifier
or payload tree is supplied to the executing controller.
-/

namespace ChaCha.Paper20261030.CanonicalRepairedActive

open ColoredStorage SourcePointer Structural PhysicalPacketStaging PacketLayers
open CanonicalPacketLayerViews MixedPacketRepair RepairedPayloadLayouts

variable {α β ρ ι η : Type*}

local instance : LinearOrder (Option Bool) := inferInstanceAs (LinearOrder (WithBot Bool))

abbrev Logical (ρ η : Type*) := HeadBoundary.Record ρ η (Option Bool)

def Result (good : Bool → α → Source β (Packet α ρ ι) → Prop)
    (leftPlain rightPlain : ProjectionLocal.Projected α ρ)
    (header : Packet α ρ ι) (bottom : Source β (Packet α ρ ι))
    (view : RepairedComponentLayout.View β α ρ ι) : Prop :=
  ∃ (left right : Option (Tagged α ρ ι)) (leftPayload rightPayload : α → Source β (Packet α ρ ι)),
    left.map (Source.mapRecords Prod.snd) = leftPlain ∧ right.map (Source.mapRecords Prod.snd) = rightPlain ∧
    (∀ key ∈ ports leftPlain, good true key (leftPayload key)) ∧
    (∀ key ∈ ports rightPlain, good false key (rightPayload key)) ∧
    view = CanonicalRepairedDormant.view leftPayload rightPayload left right header bottom

theorem result_present (good : Bool → α → Source β (Packet α ρ ι) → Prop)
    (leftPlain rightPlain : ProjectionLocal.Projected α ρ)
    (header : Packet α ρ ι) (bottom : Source β (Packet α ρ ι)) :
    ¬ Result good leftPlain rightPlain header bottom none := by
  rintro ⟨left,right,lp,rp,_,_,_,_,equal⟩
  cases left <;> cases right <;> cases equal

theorem represents (markerId : ι) (blocks : Fin 8 → Source β (Packet α (Logical ρ η) ι))
    (good : Bool → α → Source β (Packet α (Logical ρ η) ι) → Prop)
    (bits : Fin 8 → Bool) (l r tl b tr : Fin 8)
    (childPlan : HeadPacketRepair.Layout (Fin 8)) (childContext : HeadPacketLayout.Layout (Fin 8) α (Logical ρ η) ι)
    (direction : Bool) (low high terminal : Logical ρ η) (header : Packet α (Logical ρ η) ι) (depth : α)
    (headLeft headRight tailLeft tailRight : ProjectionLocal.Projected α (Logical ρ η))
    (headLeftRep : Layout markerId blocks (good true) false headLeft (HeadPacketRepair.block bits l) (HeadPacketLayout.block bits l))
    (headRightRep : Layout markerId blocks (good false) true headRight (HeadPacketRepair.block bits r) (HeadPacketLayout.block bits r))
    (tailLeftRep : Layout markerId blocks (good true) false tailLeft (HeadPacketRepair.block bits tl) (HeadPacketLayout.block bits tl))
    (tailRightRep : Layout markerId blocks (good false) true tailRight (HeadPacketRepair.block bits tr) (HeadPacketLayout.block bits tr))
    (predicate : RepairedComponentLayout.View β α (Logical ρ η) ι → Prop)
    (childRep : RepairedComponentLayout.Represents markerId blocks childPlan childContext predicate)
    (childPresent : ¬ predicate none) (childGood : ∀ body, predicate (some body) → good direction depth body)
    (leftSeparate : Separate headLeft tailLeft) (rightSeparate : Separate headRight tailRight)
    (headLeftAbsent : depth ∉ ports headLeft) (headRightAbsent : depth ∉ ports headRight)
    (tailLeftAbsent : depth ∉ ports tailLeft) (tailRightAbsent : depth ∉ ports tailRight) :
    RepairedComponentLayout.Represents markerId blocks
      (HeadPacketRepair.active bits l r tl b tr childPlan direction header.length)
      (HeadPacketLayout.active markerId bits l r tl b tr childContext direction low high terminal header)
      (Result good
        (CanonicalHeadWingViews.activePacked headLeft tailLeft depth direction
          (ObservedHeadBlueprint.owned (some true) low) (ObservedHeadBlueprint.owned (some true) high) terminal)
        (CanonicalHeadWingViews.activePacked headRight tailRight depth (!direction)
          (ObservedHeadBlueprint.owned (some false) low) (ObservedHeadBlueprint.owned (some false) high) terminal)
        header (blocks b)) := by
  have leftGood : direction = true → ∀ body, predicate (some body) → good true depth body := by
    intro present body valid
    subst direction
    exact childGood body valid
  have rightGood : (!direction) = true → ∀ body, predicate (some body) → good false depth body := by
    intro present body valid
    cases direction with
    | false => exact childGood body valid
    | true => cases present
  have leftWing := CanonicalRepairedWing.represents markerId blocks (good true) false direction
    headLeft tailLeft _ _ childPlan _ _ childContext headLeftRep tailLeftRep predicate childRep childPresent depth
    (ObservedHeadBlueprint.owned (some true) low) (ObservedHeadBlueprint.owned (some true) high) terminal
    leftGood leftSeparate headLeftAbsent tailLeftAbsent
  have rightWing := CanonicalRepairedWing.represents markerId blocks (good false) true (!direction)
    headRight tailRight _ _ childPlan _ _ childContext headRightRep tailRightRep predicate childRep childPresent depth
    (ObservedHeadBlueprint.owned (some false) low) (ObservedHeadBlueprint.owned (some false) high) terminal
    rightGood rightSeparate headRightAbsent tailRightAbsent
  have left := component_piece markerId blocks (good true) (fun _ => blocks b) false _ _ _ leftWing
  have right := component_piece markerId blocks (good false) (fun _ => blocks b) true _ _ _ rightWing
  have bottom := RepairedComponentLayout.bottom markerId blocks b header
  have first := RepairedComponentLayout.primaryJoin markerId blocks _ _ _ _ _ _ left bottom
  have all := RepairedComponentLayout.primaryJoin markerId blocks _ _ _ _ _ _ first right
  have composed := RepairedComponentLayout.weaken markerId blocks _ _ _
    (Result good
      (CanonicalHeadWingViews.activePacked headLeft tailLeft depth direction
        (ObservedHeadBlueprint.owned (some true) low) (ObservedHeadBlueprint.owned (some true) high) terminal)
      (CanonicalHeadWingViews.activePacked headRight tailRight depth (!direction)
        (ObservedHeadBlueprint.owned (some false) low) (ObservedHeadBlueprint.owned (some false) high) terminal)
      header (blocks b)) all (by
        intro view property
        obtain ⟨firstView,rightView,⟨leftView,bottomView,⟨left,lp,leftErases,leftGood,leftEqual⟩,bottomEqual,firstEqual⟩,
          ⟨right,rp,rightErases,rightGood,rightEqual⟩,resultEqual⟩ := property
        exact ⟨left,right,lp,rp,leftErases,rightErases,leftGood,rightGood,
          by rw [resultEqual,firstEqual,leftEqual,bottomEqual,rightEqual]; rfl⟩)
  cases direction <;> exact composed

end ChaCha.Paper20261030.CanonicalRepairedActive
