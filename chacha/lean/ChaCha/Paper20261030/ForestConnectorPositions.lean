import ChaCha.Paper20261030.ForestConnectorCompiler

/-! Locating a named projection cursor inside the common connector
tree. The reached focus is exactly the projection's current focus, with
only the surrounding connector context added. In particular a header
leaf read is an actual read of its original-key leaf.
-/

namespace ChaCha.Paper20261030.ForestConnector

open ColoredStorage SourcePointer SourcePositions

variable {α ρ C : Type*} [DecidableEq C]

theorem assemble_cursor (forest : ProjectionForest.State C α ρ) (layout : Source C Unit)
    (config : MultiSourceProgram.Configuration C α (List ρ)) (represented : assemble forest layout = some config)
    (q : C) (member : q ∈ colors layout) (current : Cursor α (List ρ)) (present : forest q = some current) :
    ∃ position outside, config.fingers q = some position ∧
      locate config.tree position = some (current.extend outside) := by
  induction layout generalizing config with
  | leaf selected value =>
    have equal : q = selected := by simpa only [colors,Source.shape,RouterProjection.Router.leaves,List.mem_singleton] using member
    subst selected
    have same : single q current = config := by simpa only [assemble,present,Option.map_some,Option.some.injEq] using represented
    rw [← same]
    exact ⟨address current,[],by simp [single],by simpa only [single,Cursor.extend,List.append_nil] using locate_cursor current⟩
  | fork value left right ihl ihr =>
    obtain ⟨l,r,leftRep,rightRep,rfl⟩ := assemble_fork represented
    by_cases inLeft : q ∈ colors left
    · obtain ⟨position,outside,finger,reached⟩ := ihl l leftRep inLeft
      refine ⟨false::position,outside++[.left [] r.tree],by simp only [MultiSourceProgram.join,finger],?_⟩
      simpa only [MultiSourceProgram.join,Cursor.extend,List.append_assoc] using locate_left reached [] r.tree
    · have inRight : q ∈ colors right := by
        have either : q ∈ colors left ∨ q ∈ colors right := by
          simpa only [colors,Source.shape,RouterProjection.Router.leaves,List.mem_append] using member
        exact either.resolve_left inLeft
      have free := assemble_outside forest left l leftRep q inLeft
      obtain ⟨position,outside,finger,reached⟩ := ihr r rightRep inRight
      refine ⟨true::position,outside++[.right l.tree []],by simp only [MultiSourceProgram.join,free,finger,Option.map_some],?_⟩
      simpa only [MultiSourceProgram.join,Cursor.extend,List.append_assoc] using locate_right reached [] l.tree

end ChaCha.Paper20261030.ForestConnector
