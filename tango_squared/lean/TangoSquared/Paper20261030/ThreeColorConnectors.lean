import TangoSquared.Paper20261030.ForestConnectorCompiler

/-! The primary component's three-piece connector layout: the left
routing wing, the header/bottom leaf, and the right routing wing. Empty
wings are omitted. The layout has at most three leaves and retains the
left-to-right order used by the primary representation.
-/

namespace TangoSquared.Paper20261030.ForestConnector.ThreeColors

open ColoredStorage SourcePointer

variable {α ρ : Type*}

def layout (forest : ProjectionForest.State (Option Bool) α ρ) : Source (Option Bool) Unit :=
  let middle := Source.leaf none ()
  let first := if (forest (some true)).isSome then Source.fork () (.leaf (some true) ()) middle else middle
  if (forest (some false)).isSome then Source.fork () first (.leaf (some false) ()) else first

theorem distinct (forest : ProjectionForest.State (Option Bool) α ρ) : (colors (layout forest)).Nodup := by
  cases left : forest (some true) <;> cases right : forest (some false) <;>
    simp [layout,left,right,colors,Source.shape,RouterProjection.Router.leaves]

theorem length_bound (forest : ProjectionForest.State (Option Bool) α ρ) : (colors (layout forest)).length ≤ 3 := by
  cases left : forest (some true) <;> cases right : forest (some false) <;>
    simp [layout,left,right,colors,Source.shape,RouterProjection.Router.leaves]

theorem covers (forest : ProjectionForest.State (Option Bool) α ρ) : Covers (layout forest) forest := by
  intro q current present
  cases q with
  | none =>
    cases left : forest (some true) <;> cases right : forest (some false) <;>
      simp [layout,left,right,colors,Source.shape,RouterProjection.Router.leaves]
  | some side => cases side with
    | false =>
      cases left : forest (some true) <;>
        simp [layout,left,present,colors,Source.shape,RouterProjection.Router.leaves]
    | true =>
      cases right : forest (some false) <;>
        simp [layout,right,present,colors,Source.shape,RouterProjection.Router.leaves]

theorem assemble_exists (forest : ProjectionForest.State (Option Bool) α ρ)
    (header : Cursor α (List ρ)) (present : forest none = some header) :
    ∃ config, assemble forest (layout forest) = some config := by
  cases left : forest (some true) <;> cases right : forest (some false) <;>
    simp [layout,left,right,present,assemble]

end TangoSquared.Paper20261030.ForestConnector.ThreeColors
