import TangoSquared.Paper20261030.PhysicalRecordFinder
import TangoSquared.Paper20261030.PhysicalForestCompiler
import TangoSquared.Paper20261030.LocalPackedAscent

/-! A complete local ascent in the physically annotated color forest.
The current record supplies the logical parent identifier. A charged
neighborhood search finds that parent's record; its child masks select
the upward physical moves. The physical metadata compiler maintains every
pointer field. No parent identifier is used as a free physical pointer.
-/

namespace TangoSquared.Paper20261030.PhysicalPackedParentController

open ColoredStorage SourcePointer ForestLocalProgram Structural PhysicalForestMetadata

variable {α ρ ι η C : Type*} [DecidableEq ι] [DecidableEq η] [LinearOrder C] [Fintype C]

abbrev LogicalRecord (ρ η C : Type*) := ρ × Fields η C
abbrev FinderState (ρ ι η C : Type*) := PhysicalRecordFinder.State (LogicalRecord ρ η C) ι C
abbrev MoveState (ρ ι η C : Type*) := PhysicalForestCompiler.State (List C) C (LogicalRecord ρ η C) ι

inductive State (ρ ι η C : Type*) where
  | reading (phase : FinderState ρ ι η C)
  | parent (id : η) (phase : FinderState ρ ι η C)
  | moving (id : η) (phase : MoveState ρ ι η C)
  | done (id : η)
  | error

def finishMove (parentId : η) : MoveState ρ ι η C → State ρ ι η C
  | .ready [] => .done parentId
  | phase => .moving parentId phase

def finishParent (parentId : η) : FinderState ρ ι η C → State ρ ι η C
  | .found record => match record.2.children with
    | none => .error
    | some (l,r) => finishMove parentId (.ready ((l.colors ∩ r.colors).sort (· ≤ ·)))
  | phase => .parent parentId phase

def finishRead : FinderState ρ ι η C → State ρ ι η C
  | .found record => match record.2.parent with
    | none => .error
    | some id => .parent id (.scan (Finset.univ.sort (· ≤ ·)))
  | phase => .reading phase

def initial : State ρ ι η C := .reading (.scan (Finset.univ.sort (· ≤ ·)))

def moveProgram : Program (MoveState ρ ι η C) C (Record (LogicalRecord ρ η C) ι) :=
  PhysicalForestCompiler.program (ForestNavigationController.program .up)

def program (identifier : ρ → η) (wanted : η) :
    Program (State ρ ι η C) C (Record (LogicalRecord ρ η C) ι)
  | .reading phase => (PhysicalRecordFinder.program (fun record => identifier record.1) wanted phase).mapState finishRead
  | .parent id phase => (PhysicalRecordFinder.program (fun record => identifier record.1) id phase).mapState (finishParent id)
  | .moving id phase => (moveProgram phase).mapState (finishMove id)
  | .done _ | .error => .halt

theorem reading_code (identifier : ρ → η) (wanted : η) (phase : FinderState ρ ι η C)
    (active : PhysicalRecordFinder.program (fun record => identifier record.1) wanted phase ≠ .halt) :
    program identifier wanted (finishRead phase) =
      (PhysicalRecordFinder.program (fun record => identifier record.1) wanted phase).mapState finishRead := by
  cases phase with
  | found => exact False.elim (active rfl)
  | scan | parent | current => rfl

theorem parent_code (identifier : ρ → η) (wanted parentId : η) (phase : FinderState ρ ι η C)
    (active : PhysicalRecordFinder.program (fun record => identifier record.1) parentId phase ≠ .halt) :
    program identifier wanted (finishParent parentId phase) =
      (PhysicalRecordFinder.program (fun record => identifier record.1) parentId phase).mapState (finishParent parentId) := by
  cases phase with
  | found => exact False.elim (active rfl)
  | scan | parent | current => rfl

theorem moving_code (identifier : ρ → η) (wanted parentId : η) (phase : MoveState ρ ι η C)
    (active : moveProgram phase ≠ .halt) :
    program identifier wanted (finishMove parentId phase) =
      (moveProgram phase).mapState (finishMove parentId) := by
  cases phase with
  | running | error => rfl
  | ready colors => cases colors with
    | nil => exact False.elim (active rfl)
    | cons => rfl

theorem ascend [DecidableEq α] (identifier : ρ → η) (color : α → C) (right : Bool)
    (l r : Source α (LogicalRecord ρ η C)) (record : LogicalRecord ρ η C) (outside)
    (parentField : (PackedDescentController.child right l r record outside).focus.rootRecord.2.parent = some (identifier record.1))
    {leftId rightId : η}
    (children : record.2.children = some
      (Child.mk leftId (l.support color),Child.mk rightId (r.support color)))
    (forest : TaggedForest C α (LogicalRecord ρ η C) ι)
    (represented : ProjectionForest.Represents color (PackedDescentController.child right l r record outside) (erase forest))
    (physicalUnique : Unique forest)
    (logicalUnique : Distinguishes (fun entry => identifier entry.1) (Cursor.tree ⟨.fork record l r,outside⟩)) :
    ∃ target reads cost,
      Run (program identifier (identifier (PackedDescentController.child right l r record outside).focus.rootRecord.1))
        initial (encode forest) (.done (identifier record.1)) (encode target) reads cost ∧
      ProjectionForest.Represents color ⟨.fork record l r,outside⟩ (erase target) ∧
      Unique target ∧ cost ≤ 48*Fintype.card C := by
  let current := PackedDescentController.child right l r record outside
  let wanted := identifier current.focus.rootRecord.1
  obtain ⟨readWord,readCost,readRun,readBound⟩ := PhysicalRecordFinder.find_current (fun entry => identifier entry.1)
    color current forest represented physicalUnique (by cases right <;> exact logicalUnique)
  have first := readRun.map_prefix finishRead (reading_code identifier wanted)
  change Steps (program identifier wanted) initial (encode forest)
    (finishRead (.found current.focus.rootRecord)) (encode forest) readWord readCost at first
  have readEndpoint : finishRead (ρ := ρ) (ι := ι) (.found current.focus.rootRecord) =
      State.parent (identifier record.1) (.scan (Finset.univ.sort (· ≤ ·))) := by
    simp only [finishRead,parentField,current]
  rw [readEndpoint] at first
  obtain ⟨parentWord,parentCost,parentRun,parentBound⟩ := PhysicalRecordFinder.find_parent (fun entry => identifier entry.1)
    color right l r record outside forest represented physicalUnique logicalUnique
  have second := parentRun.map_prefix (finishParent (identifier record.1)) (parent_code identifier wanted (identifier record.1))
  obtain ⟨bare,moveRun,bareRep,moveBound⟩ := PackedAscentController.ascend color right l r record outside (erase forest) represented
  obtain ⟨target,moveWord,moveCost,compiled,targetErases,targetUnique,compiledBound⟩ :=
    PhysicalForestCompiler.compile_run _ moveRun forest rfl physicalUnique
  have last := compiled.map_prefix (finishMove (identifier record.1)) (moving_code identifier wanted (identifier record.1))
  have parentEndpoint : finishParent (ρ := ρ) (ι := ι) (identifier record.1) (.found record) =
      finishMove (identifier record.1) (.ready ((l.support color ∩ r.support color).sort (· ≤ ·))) := by
    simp only [finishParent,children]
  rw [parentEndpoint] at second
  have whole := ((first.append second).append last).run rfl
  exact ⟨target,_,_,whole,by rw [targetErases]; exact bareRep,targetUnique,by omega⟩

end TangoSquared.Paper20261030.PhysicalPackedParentController
