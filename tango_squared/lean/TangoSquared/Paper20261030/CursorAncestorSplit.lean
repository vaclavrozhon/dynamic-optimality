import TangoSquared.Paper20261030.MultiSourceRecordMap

set_option autoImplicit false

/-! Recovering an actual ancestor decomposition from an erased cursor
context. Shared-tree equality and addresses identify the ancestor; no
search by identifier or injectivity of the erased records is needed. -/

namespace TangoSquared.Paper20261030.SourcePositions

open ColoredStorage SourcePointer

variable {α ρ τ : Type*}

theorem ancestor_split (erase : ρ → τ) (child parent : Cursor α ρ)
    (sameTree : child.tree = parent.tree) (insideView : List (Frame α τ))
    (context : child.ancestors.map (Frame.mapRecords erase) =
      insideView ++ parent.ancestors.map (Frame.mapRecords erase)) :
    ∃ inside, child.ancestors = inside++parent.ancestors ∧
      inside.map (Frame.mapRecords erase) = insideView ∧ parent.focus = plug child.focus inside := by
  obtain ⟨inside,outside,split,innerView,outerView⟩ := List.map_eq_append_iff.mp context
  let actual : Cursor α ρ := ⟨plug child.focus inside,outside⟩
  have actualTree : actual.tree = parent.tree := by
    change plug (plug child.focus inside) outside = _
    rw [← plug_append,← split]
    exact sameTree
  have actualAddress : address actual = address parent := by
    rw [← address_mapRecords erase actual,← address_mapRecords erase parent]
    change (outside.map (Frame.mapRecords erase)).reverse.map direction = _
    rw [outerView]
    rfl
  have equal := eq_of_tree_address actual parent actualTree actualAddress
  have sameOutside := congrArg Cursor.ancestors equal
  change outside = parent.ancestors at sameOutside
  have sameFocus := congrArg Cursor.focus equal
  exact ⟨inside,by simpa only [sameOutside] using split,innerView,sameFocus.symm⟩

end TangoSquared.Paper20261030.SourcePositions
