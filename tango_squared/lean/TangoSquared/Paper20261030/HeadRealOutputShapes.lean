import TangoSquared.Paper20261030.AnnotatedHeadWingPacking
import TangoSquared.Paper20261030.HeadBoundaryObservation
import TangoSquared.Paper20261030.CanonicalRetainedPortFacts

set_option autoImplicit false

/-! The repaired real wings are precisely the projections of the new
annotated sources. Unchanged block colors identify the retained packed
pieces, and the structural output views identify all boundary records. -/

namespace TangoSquared.Paper20261030.HeadRealOutputShapes

open ColoredStorage SourcePointer Structural HeadBoundary

variable {α ρ η : Type*}

local instance headRealOutputShapesColorOrder : LinearOrder (Option Bool) :=
  inferInstanceAs (LinearOrder (WithBot Bool))

set_option backward.isDefEq.respectTransparency false in
theorem active (identifier : ρ → η) (oldColor incomingColor newColor : α → Option Bool)
    (low incomingHigh incomingTerminal : ρ) (depth : α) (side direction : Bool)
    (headPart incomingTail : Source α ρ) (fresh : Records ρ η (Option Bool))
    (view : activeTree fresh depth
      (annotate identifier oldColor (some (identifier low)) headPart)
      (annotate identifier incomingColor (some (identifier incomingHigh)) incomingTail) =
      annotate identifier newColor none (.fork low headPart (.fork incomingHigh (.leaf depth incomingTerminal) incomingTail)))
    (boundary : newColor depth = some direction)
    (headColors : ∀ key ∈ headPart.shape.leaves, oldColor key = newColor key)
    (tailColors : ∀ key ∈ incomingTail.shape.leaves, incomingColor key = newColor key) :
    packed newColor (some side) (annotate identifier newColor none
      (.fork low headPart (.fork incomingHigh (.leaf depth incomingTerminal) incomingTail))) =
      CanonicalHeadWingViews.activePacked
        (packed oldColor (some side) (annotate identifier oldColor (some (identifier low)) headPart))
        (packed incomingColor (some side) (annotate identifier incomingColor (some (identifier incomingHigh)) incomingTail))
        depth (decide (side = direction)) (ObservedHeadBlueprint.owned (some side) fresh.low)
        (ObservedHeadBlueprint.owned (some side) fresh.incomingHigh) fresh.incomingTerminal := by
  have parts := view
  simp only [activeTree,annotate,Source.fork.injEq] at parts
  have terminal := (Source.leaf.inj parts.2.2.2.1).2
  have headEq := CanonicalRetainedPortFacts.annotation_color_congr identifier oldColor newColor
    (some side) (some (identifier low)) headPart headColors
  have tailEq := CanonicalRetainedPortFacts.annotation_color_congr identifier incomingColor newColor
    (some side) (some (identifier incomingHigh)) incomingTail tailColors
  have result := AnnotatedHeadWingPacking.active identifier newColor side direction low incomingHigh incomingTerminal
    depth headPart incomingTail boundary
  rw [← parts.1,← parts.2.2.1,← terminal,← headEq,← tailEq] at result
  exact result

set_option backward.isDefEq.respectTransparency false in
theorem dormant (identifier : ρ → η) (oldColor dormantColor : α → Option Bool)
    (oldHigh oldTerminal : ρ) (depth : α) (side : Bool)
    (oldTail : Source α ρ) (fresh : Records ρ η (Option Bool))
    (view : dormantTree fresh depth (annotate identifier oldColor (some (identifier oldHigh)) oldTail) =
      annotate identifier dormantColor none (.fork oldHigh (.leaf depth oldTerminal) oldTail))
    (boundary : dormantColor depth = none)
    (tailColors : ∀ key ∈ oldTail.shape.leaves, oldColor key = dormantColor key) :
    packed dormantColor (some side) (annotate identifier dormantColor none (.fork oldHigh (.leaf depth oldTerminal) oldTail)) =
      ProjectionLocal.decorate (ObservedHeadBlueprint.owned (some side) fresh.oldHigh)
        (packed oldColor (some side) (annotate identifier oldColor (some (identifier oldHigh)) oldTail)) := by
  have parts := view
  simp only [dormantTree,annotate,Source.fork.injEq] at parts
  have tailEq := CanonicalRetainedPortFacts.annotation_color_congr identifier oldColor dormantColor
    (some side) (some (identifier oldHigh)) oldTail tailColors
  have result := AnnotatedHeadWingPacking.dormant identifier dormantColor side oldHigh oldTerminal depth oldTail boundary
  rw [← parts.1,← tailEq] at result
  exact result

end TangoSquared.Paper20261030.HeadRealOutputShapes
