import TangoSquared.Paper20261030.ThreeColorConnectors

/-! A concrete configuration for the left-wing/header/right-wing
connector. Its whole key word is the concatenation of the three pieces,
and the header finger is at depth at most two when the header cursor is
at its root. These are representation facts; entry navigation is charged
by a separate controller.
-/

namespace TangoSquared.Paper20261030.ForestConnector.ThreeColors

open ColoredStorage SourcePointer SourcePositions

variable {α ρ : Type*}

def configuration (forest : ProjectionForest.State (Option Bool) α ρ) (header : Cursor α (List ρ)) :
    MultiSourceProgram.Configuration (Option Bool) α (List ρ) :=
  let middle := single none header
  let first := match forest (some true) with
    | none => middle
    | some left => MultiSourceProgram.join [] (single (some true) left) middle
  match forest (some false) with
    | none => first
    | some right => MultiSourceProgram.join [] first (single (some false) right)

theorem assemble_configuration (forest : ProjectionForest.State (Option Bool) α ρ)
    (header : Cursor α (List ρ)) (present : forest none = some header) :
    assemble forest (layout forest) = some (configuration forest header) := by
  cases left : forest (some true) <;> cases right : forest (some false) <;>
    simp [layout,configuration,left,right,present,assemble]

def word (forest : ProjectionForest.State (Option Bool) α ρ) (q : Option Bool) : List α :=
  ((forest q).map (fun current => current.tree.shape.leaves)).getD []

theorem configuration_leaves (forest : ProjectionForest.State (Option Bool) α ρ) (header : Cursor α (List ρ)) :
    (configuration forest header).tree.shape.leaves = word forest (some true) ++ header.tree.shape.leaves ++ word forest (some false) := by
  cases left : forest (some true) <;> cases right : forest (some false) <;>
    simp [configuration,word,left,right,MultiSourceProgram.join,single,Source.shape,RouterProjection.Router.leaves]

def headerPath (forest : ProjectionForest.State (Option Bool) α ρ) : List Bool :=
  (if (forest (some false)).isSome then [false] else []) ++
  (if (forest (some true)).isSome then [true] else [])

theorem headerPath_length (forest : ProjectionForest.State (Option Bool) α ρ) : (headerPath forest).length ≤ 2 := by
  cases left : forest (some true) <;> cases right : forest (some false) <;> simp [headerPath,left,right]

theorem header_finger (forest : ProjectionForest.State (Option Bool) α ρ) (header : Cursor α (List ρ)) :
    (configuration forest header).fingers none = some (headerPath forest ++ address header) := by
  cases left : forest (some true) <;> cases right : forest (some false) <;>
    simp [configuration,headerPath,left,right,MultiSourceProgram.join,single]

theorem header_atRoot (forest : ProjectionForest.State (Option Bool) α ρ) (header : Source α (List ρ)) :
    ∃ outside, locate (configuration forest ⟨header,[]⟩).tree (headerPath forest) = some ⟨header,outside⟩ := by
  cases left : forest (some true) <;> cases right : forest (some false) <;>
    simp [configuration,headerPath,left,right,MultiSourceProgram.join,single,Cursor.tree,plug,
      locate,descend,SourceLocalProgram.navigate]

end TangoSquared.Paper20261030.ForestConnector.ThreeColors
