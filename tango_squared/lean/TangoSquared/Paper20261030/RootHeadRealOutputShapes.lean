import TangoSquared.Paper20261030.HeadRealOutputShapes
import TangoSquared.Paper20261030.CanonicalRootComponentView

set_option autoImplicit false

/-! At the minimum depth the real projections contain the new boundary
and the incoming tail, with no prefix source or prefix packet. -/

namespace TangoSquared.Paper20261030.HeadRealOutputShapes

open ColoredStorage SourcePointer Structural HeadBoundary

variable {α ρ η : Type*} [DecidableEq α]

local instance : LinearOrder (Option Bool) := inferInstanceAs (LinearOrder (WithBot Bool))

set_option backward.isDefEq.respectTransparency false in
theorem root_active (identifier : ρ → η) (incomingColor newColor : α → Option Bool)
    (incomingHigh incomingTerminal : ρ) (depth : α) (side direction : Bool)
    (incomingTail : Source α ρ) (fresh : Records ρ η (Option Bool))
    (noPrefix : ObservedHeadBlueprint.owned (some side) fresh.low = [])
    (view : Source.fork fresh.incomingHigh (.leaf depth fresh.incomingTerminal)
      (annotate identifier incomingColor (some (identifier incomingHigh)) incomingTail) =
      annotate identifier newColor none (.fork incomingHigh (.leaf depth incomingTerminal) incomingTail))
    (boundary : newColor depth = some direction)
    (tailColors : ∀ key ∈ incomingTail.shape.leaves, incomingColor key = newColor key) :
    packed newColor (some side) (annotate identifier newColor none
      (.fork incomingHigh (.leaf depth incomingTerminal) incomingTail)) =
      CanonicalHeadWingViews.activePacked none
        (packed incomingColor (some side) (annotate identifier incomingColor (some (identifier incomingHigh)) incomingTail))
        depth (decide (side = direction)) (ObservedHeadBlueprint.owned (some side) fresh.low)
        (ObservedHeadBlueprint.owned (some side) fresh.incomingHigh) fresh.incomingTerminal := by
  have parts := view
  simp only [annotate,Source.fork.injEq] at parts
  have terminal := (Source.leaf.inj parts.2.1).2
  have tailEq := CanonicalRetainedPortFacts.annotation_color_congr identifier incomingColor newColor
    (some side) (some (identifier incomingHigh)) incomingTail tailColors
  have result := CanonicalRootComponentView.packing identifier newColor side direction
    incomingHigh incomingTerminal depth incomingTail boundary
  rw [← parts.1,← terminal,← tailEq] at result
  rw [noPrefix]
  exact result

end TangoSquared.Paper20261030.HeadRealOutputShapes
