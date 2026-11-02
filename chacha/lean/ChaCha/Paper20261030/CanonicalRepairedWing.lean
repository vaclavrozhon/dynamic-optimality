import ChaCha.Paper20261030.RepairedPayloadLayouts
import ChaCha.Paper20261030.CanonicalHeadWingViews

set_option autoImplicit false

/-! A complete prepared real wing after repair: the opaque prefix, its
two exposed logical joins, the optional boundary attachment, and the
opaque tail. Right-wing mirroring changes only physical order. -/

namespace ChaCha.Paper20261030.CanonicalRepairedWing

open ColoredStorage SourcePointer Structural PhysicalPacketStaging PacketLayers MixedPacketRepair
open RepairedPayloadLayouts

variable {κ α β ρ ι : Type*}

def plan (reverse attached : Bool) (head tail child : HeadPacketRepair.Layout κ) : HeadPacketRepair.Layout κ :=
  let terminal := HeadPacketRepair.attachment child
  let upper := if attached then
    if reverse then HeadPacketRepair.realJoin true tail terminal else HeadPacketRepair.realJoin false terminal tail
    else tail
  if reverse then HeadPacketRepair.realJoin true upper head else HeadPacketRepair.realJoin false head upper

def context (markerId : ι) (reverse attached : Bool)
    (head tail child : HeadPacketLayout.Layout κ α ρ ι) (low high : List ρ) (terminalRecord : ρ) : HeadPacketLayout.Layout κ α ρ ι :=
  let terminal := HeadPacketLayout.attachment markerId terminalRecord child
  let upper := if attached then
    if reverse then HeadPacketLayout.realJoin markerId high tail terminal else HeadPacketLayout.realJoin markerId high terminal tail
    else HeadPacketLayout.push (HeadPacketLayout.addLogical high) tail
  if reverse then HeadPacketLayout.realJoin markerId low upper head else HeadPacketLayout.realJoin markerId low head upper

private theorem join_none_left (plain : ProjectionLocal.Projected α ρ) : ProjectionLocal.join none plain = plain := by
  cases plain <;> rfl

theorem represents (markerId : ι) (blocks : κ → Source β (Packet α ρ ι))
    (good : α → Source β (Packet α ρ ι) → Prop) (reverse attached : Bool)
    (headPlain tailPlain : ProjectionLocal.Projected α ρ)
    (headPlan tailPlan childPlan : HeadPacketRepair.Layout κ)
    (headContext tailContext childContext : HeadPacketLayout.Layout κ α ρ ι)
    (headRep : Layout markerId blocks good reverse headPlain headPlan headContext)
    (tailRep : Layout markerId blocks good reverse tailPlain tailPlan tailContext)
    (predicate : RepairedComponentLayout.View β α ρ ι → Prop)
    (childRep : RepairedComponentLayout.Represents markerId blocks childPlan childContext predicate)
    (childPresent : ¬ predicate none) (depth : α) (low high : List ρ) (terminal : ρ)
    (childGood : attached = true → ∀ body, predicate (some body) → good depth body)
    (headTail : Separate headPlain tailPlain) (headAbsent : depth ∉ ports headPlain) (tailAbsent : depth ∉ ports tailPlain) :
    Layout markerId blocks good reverse
      (CanonicalHeadWingViews.activePacked headPlain tailPlain depth attached low high terminal)
      (plan reverse attached headPlan tailPlan childPlan)
      (context markerId reverse attached headContext tailContext childContext low high terminal) := by
  have headTerminal := (singleton_separate depth [terminal] headPlain headAbsent).symm
  have terminalTail := singleton_separate depth [terminal] tailPlain tailAbsent
  cases attached with
  | false =>
    have upper := logical markerId blocks good reverse _ _ _ tailRep high
    cases reverse with
    | false =>
      have result := realJoin markerId blocks good false low _ _ _ _ _ _ (headTail.decorate_right high) headRep upper
      simpa only [plan,context,CanonicalHeadWingViews.activePacked,Bool.false_eq_true,if_false,join_none_left] using result
    | true =>
      have result := realJoin markerId blocks good true low _ _ _ _ _ _ (headTail.decorate_right high).symm upper headRep
      simpa only [plan,context,CanonicalHeadWingViews.activePacked,Bool.false_eq_true,if_false,if_true,join_none_left] using result
  | true =>
    have terminalRep := RepairedPayloadLayouts.attachment markerId blocks good reverse depth terminal _ _ predicate childRep childPresent (childGood rfl)
    cases reverse with
    | false =>
      have upper := realJoin markerId blocks good false high _ _ _ _ _ _ terminalTail terminalRep tailRep
      have result := realJoin markerId blocks good false low _ _ _ _ _ _
        ((headTerminal.join_right headTail).decorate_right high) headRep upper
      simpa only [plan,context,CanonicalHeadWingViews.activePacked,Bool.false_eq_true,if_false,if_true] using result
    | true =>
      have upper := realJoin markerId blocks good true high _ _ _ _ _ _ terminalTail.symm tailRep terminalRep
      have result := realJoin markerId blocks good true low _ _ _ _ _ _
        ((headTerminal.join_right headTail).decorate_right high).symm upper headRep
      simpa only [plan,context,CanonicalHeadWingViews.activePacked,if_true] using result

end ChaCha.Paper20261030.CanonicalRepairedWing
