import ChaCha.Paper20261030.MultiSourceComposition
import ChaCha.Paper20261030.SourceProgramRecordMap
import ChaCha.Paper20261030.CursorRepresentationShapes

/-! Erasing extra vertex metadata in the shared-tree finger model.
The ghost addresses and rotation transport depend only on tree shape,
so erasure commutes with navigation and all configuration operations.
-/

namespace ChaCha.Paper20261030.SourcePositions

open ColoredStorage SourcePointer

variable {α ρ τ : Type*}

theorem direction_mapRecords (f : ρ → τ) (frame : Frame α ρ) :
    direction (frame.mapRecords f) = direction frame := by cases frame <;> rfl

theorem address_mapRecords (f : ρ → τ) (current : Cursor α ρ) :
    address (current.mapRecords f) = address current := by
  simp only [address,Cursor.mapRecords,← List.map_reverse,List.map_map]
  congr 1
  funext frame
  exact direction_mapRecords f frame

theorem descend_mapRecords (f : ρ → τ) (current : Cursor α ρ) (position : List Bool) :
    descend (current.mapRecords f) position = (descend current position).map (Cursor.mapRecords f) := by
  induction position generalizing current with
  | nil => rfl
  | cons right rest ih =>
    simp only [descend,← navigate_mapRecords]
    cases moved : SourceLocalProgram.navigate (if right then .right else .left) current with
    | none => rfl
    | some child => exact ih child

theorem locate_mapRecords (f : ρ → τ) (tree : Source α ρ) (position : List Bool) :
    locate (tree.mapRecords f) position = (locate tree position).map (Cursor.mapRecords f) :=
  descend_mapRecords f ⟨tree,[]⟩ position

theorem lift_locate (f : ρ → τ) (tree : Source α ρ) (position : List Bool) (current : Cursor α τ)
    (reached : locate (tree.mapRecords f) position = some current) :
    ∃ target, locate tree position = some target ∧ target.mapRecords f = current := by
  rw [locate_mapRecords] at reached
  cases found : locate tree position with
  | none => simp only [found,Option.map_none,reduceCtorEq] at reached
  | some target =>
    exact ⟨target,rfl,by simpa only [found,Option.map_some,Option.some.injEq] using reached⟩

theorem underContext_mapRecords (f : ρ → τ) (outside : List (Frame α ρ))
    (change : List Bool → List Bool) :
    underContext (outside.map (Frame.mapRecords f)) change = underContext outside change := by
  induction outside generalizing change with
  | nil => rfl
  | cons frame rest ih => simpa only [List.map_cons,underContext,direction_mapRecords] using ih (underChild (direction frame) change)

end ChaCha.Paper20261030.SourcePositions

namespace ChaCha.Paper20261030.MultiSourceProgram

open ColoredStorage SourcePointer SourcePositions
open DynamicOptimality.LocalProgram (Move)

variable {α ρ τ F : Type*} [DecidableEq F]

def Configuration.mapRecords (f : ρ → τ) (config : Configuration F α ρ) : Configuration F α τ :=
  ⟨config.tree.mapRecords f,config.fingers⟩

theorem transport_mapRecords (f : ρ → τ) (action : Move) (current : Cursor α ρ) :
    transport action (current.mapRecords f) = transport action current := by
  cases action <;> try rfl
  all_goals exact underContext_mapRecords f current.ancestors _

theorem moveResult_mapRecords (f : ρ → τ) (config : Configuration F α ρ) (finger : F)
    (action : Move) (before after : Cursor α ρ) :
    (moveResult config finger action before after).mapRecords f =
      moveResult (config.mapRecords f) finger action (before.mapRecords f) (after.mapRecords f) := by
  simp only [moveResult,Configuration.mapRecords,Cursor.mapRecords_tree,transport_mapRecords,address_mapRecords]

theorem writeResult_mapRecords (f : ρ → τ) (config : Configuration F α ρ) (current : Cursor α ρ) (fresh : ρ) :
    (writeResult config current fresh).mapRecords f =
      writeResult (config.mapRecords f) (current.mapRecords f) (f fresh) := by
  simp only [writeResult,Configuration.mapRecords,← plug_mapRecords,Source.mapRecords_setRoot,Cursor.mapRecords]

theorem copyResult_mapRecords (f : ρ → τ) (config : Configuration F α ρ) (destination origin : F) :
    (copyResult config destination origin).mapRecords f = copyResult (config.mapRecords f) destination origin := rfl

theorem WellFormed.of_mapRecords (f : ρ → τ) {config : Configuration F α ρ}
    (valid : WellFormed (config.mapRecords f)) : WellFormed config := by
  intro finger position present
  obtain ⟨current,reached⟩ := valid finger position present
  obtain ⟨target,found,_⟩ := lift_locate f config.tree position current reached
  exact ⟨target,found⟩

end ChaCha.Paper20261030.MultiSourceProgram
