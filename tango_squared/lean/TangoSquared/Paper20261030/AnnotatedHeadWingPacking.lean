import TangoSquared.Paper20261030.CanonicalHeadWingViews
import TangoSquared.Paper20261030.AnnotatedVirtualHeadPackets

/-! The real-wing decomposition applies to actual canonical logical
annotations. The exposed lists are exactly the owner lists computed from
the observed child masks, including a real terminal on just one wing. -/

namespace TangoSquared.Paper20261030.AnnotatedHeadWingPacking

open ColoredStorage SourcePointer Structural HeadBoundary ProjectionLocal
open ObservedHeadBlueprint (owned)

variable {α ρ ι C : Type*} [LinearOrder C]

theorem fork (identifier : ρ → ι) (color : α → C) (q : C) (parent : Option ι)
    (record : ρ) (left right : Source α ρ) :
    packed color q (annotate identifier color parent (.fork record left right)) =
      decorate (owned q (record,fields identifier color parent (.fork record left right)))
        (join (packed color q (annotate identifier color (some (identifier record)) left))
          (packed color q (annotate identifier color (some (identifier record)) right))) := by
  apply ObservedHeadBlueprint.fork_packing color q _ _ _
    (descriptor identifier color left) (descriptor identifier color right) rfl
  · exact (ObservedHeadBlueprint.annotate_support identifier color (some (identifier record)) left).symm
  · exact (ObservedHeadBlueprint.annotate_support identifier color (some (identifier record)) right).symm

local instance : LinearOrder (Option Bool) := inferInstanceAs (LinearOrder (WithBot Bool))

theorem active (identifier : ρ → ι) (color : α → Option Bool) (side direction : Bool)
    (low high terminal : ρ) (depth : α) (headPart tail : Source α ρ)
    (boundary : color depth = some direction) :
    packed color (some side) (annotate identifier color none (.fork low headPart (.fork high (.leaf depth terminal) tail))) =
      CanonicalHeadWingViews.activePacked
        (packed color (some side) (annotate identifier color (some (identifier low)) headPart))
        (packed color (some side) (annotate identifier color (some (identifier high)) tail))
        depth (decide (side = direction))
        (owned (some side) (low,fields identifier color none (.fork low headPart (.fork high (.leaf depth terminal) tail))))
        (owned (some side) (high,fields identifier color (some (identifier low)) (.fork high (.leaf depth terminal) tail)))
        (terminal,fields identifier color (some (identifier high)) (.leaf depth terminal)) := by
  have leaf : packed color (some side) (annotate identifier color (some (identifier high)) (.leaf depth terminal)) =
      if decide (side = direction) then
        some (.leaf depth [(terminal,fields identifier color (some (identifier high)) (.leaf depth terminal))]) else none := by
    cases side <;> cases direction <;>
      simp only [annotate,packed,pack,boundary,Option.some.injEq,reduceCtorEq,if_true,if_false,decide_true,decide_false,
        Bool.false_eq_true,Stored.toSource]
  rw [fork,fork,leaf]
  rfl

theorem dormant (identifier : ρ → ι) (color : α → Option Bool) (side : Bool)
    (high terminal : ρ) (depth : α) (tail : Source α ρ) (boundary : color depth = none) :
    packed color (some side) (annotate identifier color none (.fork high (.leaf depth terminal) tail)) =
      decorate (owned (some side) (high,fields identifier color none (.fork high (.leaf depth terminal) tail)))
        (packed color (some side) (annotate identifier color (some (identifier high)) tail)) := by
  have leaf : packed color (some side) (annotate identifier color (some (identifier high)) (.leaf depth terminal)) = none := by
    simp only [annotate,packed,pack,boundary,reduceCtorEq,if_false,Stored.toSource]
  rw [fork,leaf,join]

end TangoSquared.Paper20261030.AnnotatedHeadWingPacking
