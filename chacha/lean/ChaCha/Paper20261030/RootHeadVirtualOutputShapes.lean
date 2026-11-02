import ChaCha.Paper20261030.HeadVirtualOutputShapes

set_option autoImplicit false

/-! The replacement active virtual packet when the switched depth is the
minimum. There is no prefix source and the incoming high record becomes
the logical root. -/

namespace ChaCha.Paper20261030.HeadVirtualOutputShapes

open ColoredStorage SourcePointer Structural HeadBoundary

variable {α ρ η : Type*} [DecidableEq α]

local instance : LinearOrder (Option Bool) := inferInstanceAs (LinearOrder (WithBot Bool))

theorem root_active (identifier : ρ → η) (incomingColor newColor : α → Option Bool)
    (incomingHigh incomingTerminal : ρ) (depth bottom : α) (side : Bool)
    (incomingTail : Source α ρ) (fresh : Records ρ η (Option Bool))
    (view : Source.fork fresh.incomingHigh (.leaf depth fresh.incomingTerminal)
      (annotate identifier incomingColor (some (identifier incomingHigh)) incomingTail) =
      annotate identifier newColor none (.fork incomingHigh (.leaf depth incomingTerminal) incomingTail))
    (boundary : newColor depth = some side)
    (packet : List (HeadBoundary.Record ρ η (Option Bool)))
    (tailPacked : packed newColor none (annotate identifier newColor (some (identifier incomingHigh)) incomingTail) =
      some (.leaf bottom packet)) :
    packed newColor none (annotate identifier newColor none
      (.fork incomingHigh (.leaf depth incomingTerminal) incomingTail)) =
      some (.leaf bottom (ObservedHeadBlueprint.owned none fresh.incomingHigh ++ packet)) := by
  have parts := view
  simp only [annotate,Source.fork.injEq] at parts
  have result := AnnotatedVirtualHeadPackets.root_active identifier newColor incomingHigh incomingTerminal
    depth bottom side incomingTail boundary packet tailPacked
  dsimp only [AnnotatedVirtualHeadPackets.record,Source.rootRecord] at result
  rw [← parts.1] at result
  exact result

end ChaCha.Paper20261030.HeadVirtualOutputShapes
