import ChaCha.Paper20261030.SourceIdentifierPositions

set_option autoImplicit false

namespace ChaCha.Paper20261030.MultiSourceSingleCursor

open ColoredStorage SourcePointer SourcePositions MultiSourceProgram

variable {α ρ F : Type*}

theorem Represents.unique {finger : F} {before after : Cursor α ρ} {config : Configuration F α ρ}
    (first : Represents finger before config) (last : Represents finger after config) : before = after := by
  have position := Option.some.inj (first.2.symm.trans last.2)
  have firstLocation : locate config.tree (address before) = some before := by
    rw [first.1]
    exact locate_cursor before
  have lastLocation : locate config.tree (address after) = some after := by
    rw [last.1]
    exact locate_cursor after
  rw [position] at firstLocation
  exact Option.some.inj (firstLocation.symm.trans lastLocation)

end ChaCha.Paper20261030.MultiSourceSingleCursor
