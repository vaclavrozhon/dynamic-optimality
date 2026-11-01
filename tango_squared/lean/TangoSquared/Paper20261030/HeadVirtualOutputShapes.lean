import TangoSquared.Paper20261030.AnnotatedVirtualHeadPackets
import TangoSquared.Paper20261030.HeadBoundaryObservation

set_option autoImplicit false

/-! The two replacement virtual pieces have the packed projections of the
new annotated components. Their boundary records are obtained from the
already proved structural views, including the changed parent fields. -/

namespace TangoSquared.Paper20261030.HeadVirtualOutputShapes

open ColoredStorage SourcePointer Structural HeadBoundary

variable {α ρ η : Type*} [DecidableEq α]

local instance headVirtualOutputShapesColorOrder : LinearOrder (Option Bool) :=
  inferInstanceAs (LinearOrder (WithBot Bool))

theorem active (identifier : ρ → η) (oldColor incomingColor newColor : α → Option Bool)
    (low incomingHigh incomingTerminal : ρ) (depth bottom : α) (side : Bool)
    (headPart incomingTail : Source α ρ) (fresh : Records ρ η (Option Bool))
    (view : activeTree fresh depth
      (annotate identifier oldColor (some (identifier low)) headPart)
      (annotate identifier incomingColor (some (identifier incomingHigh)) incomingTail) =
      annotate identifier newColor none (.fork low headPart (.fork incomingHigh (.leaf depth incomingTerminal) incomingTail)))
    (boundary : newColor depth = some side)
    (absent : packed newColor none (annotate identifier newColor (some (identifier low)) headPart) = none)
    (packet : List (HeadBoundary.Record ρ η (Option Bool)))
    (tailPacked : packed newColor none (annotate identifier newColor (some (identifier incomingHigh)) incomingTail) =
      some (.leaf bottom packet)) :
    packed newColor none (annotate identifier newColor none
      (.fork low headPart (.fork incomingHigh (.leaf depth incomingTerminal) incomingTail))) =
      some (.leaf bottom (VirtualHeadPackets.prefixes fresh.low fresh.incomingHigh ++ packet)) := by
  have parts := view
  simp only [activeTree,annotate,Source.fork.injEq] at parts
  have result := AnnotatedVirtualHeadPackets.active identifier newColor low incomingHigh incomingTerminal depth bottom side
    headPart incomingTail boundary absent packet tailPacked
  dsimp only [AnnotatedVirtualHeadPackets.record,Source.rootRecord] at result
  rw [← parts.1,← parts.2.2.1] at result
  exact result

theorem dormant (identifier : ρ → η) (oldColor dormantColor : α → Option Bool)
    (oldHigh oldTerminal : ρ) (depth bottom : α)
    (oldTail : Source α ρ) (fresh : Records ρ η (Option Bool))
    (view : dormantTree fresh depth (annotate identifier oldColor (some (identifier oldHigh)) oldTail) =
      annotate identifier dormantColor none (.fork oldHigh (.leaf depth oldTerminal) oldTail))
    (boundary : dormantColor depth = none)
    (packet : List (HeadBoundary.Record ρ η (Option Bool)))
    (tailPacked : packed dormantColor none (annotate identifier dormantColor (some (identifier oldHigh)) oldTail) =
      some (.leaf bottom packet)) :
    packed dormantColor none (annotate identifier dormantColor none (.fork oldHigh (.leaf depth oldTerminal) oldTail)) =
      some (.fork [fresh.oldHigh] (.leaf depth [fresh.oldTerminal]) (.leaf bottom packet)) := by
  have parts := view
  simp only [dormantTree,annotate,Source.fork.injEq] at parts
  have terminal := (Source.leaf.inj parts.2.1).2
  have result := AnnotatedVirtualHeadPackets.dormant identifier dormantColor oldHigh oldTerminal depth bottom oldTail
    boundary packet tailPacked
  dsimp only [AnnotatedVirtualHeadPackets.record,Source.rootRecord] at result
  rw [← parts.1,← terminal] at result
  exact result

end TangoSquared.Paper20261030.HeadVirtualOutputShapes
