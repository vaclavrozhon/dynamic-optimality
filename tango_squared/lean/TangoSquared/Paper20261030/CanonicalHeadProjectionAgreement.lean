import TangoSquared.Paper20261030.CanonicalRetainedPortFacts
import TangoSquared.Paper20261030.HeadBoundaryObservation
import TangoSquared.Paper20261030.CanonicalRootComponentView

set_option autoImplicit false

/-! The reconstructed real projections are exactly those of the repaired
logical source. The record-view equalities are supplied by the checked
boundary-observation theorems; unchanged colors on retained blocks let
the input witnesses be reused in the output. -/

namespace TangoSquared.Paper20261030.CanonicalHeadProjectionAgreement

open ColoredStorage SourcePointer Structural HeadBoundary ObservedHeadBlueprint

variable {α ρ ι : Type*}

local instance : LinearOrder (Option Bool) := inferInstanceAs (LinearOrder (WithBot Bool))

theorem active (identifier : ρ → ι) (oldColor incomingColor newColor : α → Option Bool)
    (low incomingHigh incomingTerminal : ρ) (depth : α) (headPart incomingTail : Source α ρ)
    (direction side : Bool) (boundary : newColor depth = some (!direction))
    (headColors : ∀ key ∈ headPart.shape.leaves, oldColor key = newColor key)
    (incomingColors : ∀ key ∈ incomingTail.shape.leaves, incomingColor key = newColor key)
    (records : Records ρ ι (Option Bool))
    (view : activeTree records depth (annotate identifier oldColor (some (identifier low)) headPart)
      (annotate identifier incomingColor (some (identifier incomingHigh)) incomingTail) =
      annotate identifier newColor none (.fork low headPart (.fork incomingHigh (.leaf depth incomingTerminal) incomingTail))) :
    packed newColor (some side)
      (activeTree records depth (annotate identifier oldColor (some (identifier low)) headPart)
        (annotate identifier incomingColor (some (identifier incomingHigh)) incomingTail)) =
      CanonicalHeadWingViews.activePacked
        (packed oldColor (some side) (annotate identifier oldColor (some (identifier low)) headPart))
        (packed incomingColor (some side) (annotate identifier incomingColor (some (identifier incomingHigh)) incomingTail))
        depth (decide (side = !direction)) (owned (some side) records.low) (owned (some side) records.incomingHigh) records.incomingTerminal := by
  have parts := view
  simp only [activeTree,annotate,Source.fork.injEq,Source.leaf.injEq,true_and] at parts
  obtain ⟨lowEqual,_,highEqual,terminalEqual,_⟩ := parts
  have headSame := CanonicalRetainedPortFacts.annotation_color_congr identifier oldColor newColor (some side)
    (some (identifier low)) headPart headColors
  have tailSame := CanonicalRetainedPortFacts.annotation_color_congr identifier incomingColor newColor (some side)
    (some (identifier incomingHigh)) incomingTail incomingColors
  rw [view,headSame,tailSame,lowEqual,highEqual,terminalEqual]
  exact AnnotatedHeadWingPacking.active identifier newColor side (!direction) low incomingHigh incomingTerminal depth headPart incomingTail boundary

theorem dormant (identifier : ρ → ι) (oldColor dormantColor : α → Option Bool)
    (oldHigh oldTerminal : ρ) (depth : α) (oldTail : Source α ρ) (side : Bool)
    (boundary : dormantColor depth = none) (oldColors : ∀ key ∈ oldTail.shape.leaves, oldColor key = dormantColor key)
    (records : Records ρ ι (Option Bool))
    (view : dormantTree records depth (annotate identifier oldColor (some (identifier oldHigh)) oldTail) =
      annotate identifier dormantColor none (.fork oldHigh (.leaf depth oldTerminal) oldTail)) :
    packed dormantColor (some side) (dormantTree records depth (annotate identifier oldColor (some (identifier oldHigh)) oldTail)) =
      ProjectionLocal.decorate (owned (some side) records.oldHigh)
        (packed oldColor (some side) (annotate identifier oldColor (some (identifier oldHigh)) oldTail)) := by
  have highEqual := congrArg Source.rootRecord view
  change records.oldHigh = (oldHigh,fields identifier dormantColor none (.fork oldHigh (.leaf depth oldTerminal) oldTail)) at highEqual
  have tailSame := CanonicalRetainedPortFacts.annotation_color_congr identifier oldColor dormantColor (some side)
    (some (identifier oldHigh)) oldTail oldColors
  rw [view,tailSame,highEqual]
  exact AnnotatedHeadWingPacking.dormant identifier dormantColor side oldHigh oldTerminal depth oldTail boundary

theorem root_active (identifier : ρ → ι) (incomingColor newColor : α → Option Bool)
    (incomingHigh incomingTerminal : ρ) (depth : α) (incomingTail : Source α ρ)
    (direction side : Bool) (boundary : newColor depth = some (!direction))
    (incomingColors : ∀ key ∈ incomingTail.shape.leaves, incomingColor key = newColor key)
    (records : RootRecords ρ ι)
    (view : Source.fork records.incomingHigh (.leaf depth records.incomingTerminal)
      (annotate identifier incomingColor (some (identifier incomingHigh)) incomingTail) =
      annotate identifier newColor none (.fork incomingHigh (.leaf depth incomingTerminal) incomingTail)) :
    packed newColor (some side)
      (.fork records.incomingHigh (.leaf depth records.incomingTerminal)
        (annotate identifier incomingColor (some (identifier incomingHigh)) incomingTail)) =
      CanonicalHeadWingViews.activePacked none
        (packed incomingColor (some side) (annotate identifier incomingColor (some (identifier incomingHigh)) incomingTail))
        depth (decide (side = !direction)) [] (owned (some side) records.incomingHigh) records.incomingTerminal := by
  classical
  have parts := view
  simp only [annotate,Source.fork.injEq,Source.leaf.injEq,true_and] at parts
  obtain ⟨highEqual,terminalEqual,_⟩ := parts
  have tailSame := CanonicalRetainedPortFacts.annotation_color_congr identifier incomingColor newColor (some side)
    (some (identifier incomingHigh)) incomingTail incomingColors
  rw [view,tailSame,highEqual,terminalEqual]
  exact CanonicalRootComponentView.packing identifier newColor side (!direction) incomingHigh incomingTerminal depth incomingTail boundary

end TangoSquared.Paper20261030.CanonicalHeadProjectionAgreement
