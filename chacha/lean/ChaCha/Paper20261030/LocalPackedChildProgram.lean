import ChaCha.Paper20261030.LocalPackedDescent
import ChaCha.Paper20261030.ForestProgramComposition
import ChaCha.Paper20261030.SourceStructuralFields

/-! A complete local child move in the packed representation. The program
first reads the logical record by its immutable identifier, obtains both
child masks and the next identifier from that record, and then moves the
selected physical fingers. The correctness premise concerns exactly the
child fields used by this operation; unrelated metadata are not inspected.
-/

namespace ChaCha.Paper20261030.PackedChildController

open ColoredStorage SourcePointer ForestLocalProgram Structural

variable {α ρ ι C : Type*} [DecidableEq ι] [LinearOrder C]

inductive State (ρ ι C : Type*) where
  | reading (phase : PackedReadController.State C (ρ × Fields ι C))
  | moving (nextId : ι) (colors : List C)
  | done (nextId : ι)
  | error

def finishMove (nextId : ι) : List C → State ρ ι C
  | [] => .done nextId
  | colors => .moving nextId colors

def finishRead (right : Bool) : PackedReadController.State C (ρ × Fields ι C) → State ρ ι C
  | .found _ record => match record.2.children with
    | none => .error
    | some (l,r) => finishMove (if right then r.id else l.id) ((l.colors ∩ r.colors).sort (· ≤ ·))
  | phase => .reading phase

def initial [Fintype C] : State ρ ι C := .reading (.scan (Finset.univ.sort (· ≤ ·)))

def program (identifier : ρ → ι) (wanted : ι) (right : Bool) : Program (State ρ ι C) C (ρ × Fields ι C)
  | .reading phase => (PackedReadController.program (fun record => identifier record.1) wanted phase).mapState (finishRead right)
  | .moving nextId colors => (ForestNavigationController.program (PackedDescentController.action right) colors).mapState (finishMove nextId)
  | .done _ | .error => .halt

theorem reading_code (identifier : ρ → ι) (wanted : ι) (right : Bool)
    (phase : PackedReadController.State C (ρ × Fields ι C))
    (active : PackedReadController.program (fun record => identifier record.1) wanted phase ≠ .halt) :
    program identifier wanted right (finishRead right phase) =
      (PackedReadController.program (fun record => identifier record.1) wanted phase).mapState (finishRead right) := by
  cases phase with
  | scan => rfl
  | found => exact False.elim (active rfl)

theorem moving_code (identifier : ρ → ι) (wanted : ι) (right : Bool) (nextId : ι) (colors : List C)
    (active : ForestNavigationController.program (ρ := ρ × Fields ι C) (PackedDescentController.action right) colors ≠ .halt) :
    program identifier wanted right (finishMove nextId colors) =
      (ForestNavigationController.program (PackedDescentController.action right) colors).mapState (finishMove nextId) := by
  cases colors with
  | nil => exact False.elim (active rfl)
  | cons => rfl

theorem descend [DecidableEq α] [Fintype C] (identifier : ρ → ι) (color : α → C) (right : Bool)
    (l r : Source α (ρ × Fields ι C)) (record : ρ × Fields ι C) (outside)
    (children : record.2.children = some
      (Child.mk (identifier l.rootRecord.1) (l.support color),Child.mk (identifier r.rootRecord.1) (r.support color)))
    (forest : ProjectionForest.State C α (ρ × Fields ι C))
    (represented : ProjectionForest.Represents color ⟨.fork record l r,outside⟩ forest)
    (unique : Distinguishes (fun entry => identifier entry.1) (Cursor.tree ⟨.fork record l r,outside⟩)) :
    ∃ target reads cost,
      Run (program identifier (identifier record.1) right) initial forest
        (.done (if right then identifier r.rootRecord.1 else identifier l.rootRecord.1)) target reads cost ∧
      ProjectionForest.Represents color (PackedDescentController.child right l r record outside) target ∧
      cost ≤ 2*Fintype.card C := by
  obtain ⟨q,readWord,readCost,readRun,readBound,readCapacity⟩ :=
    PackedReadController.read (fun entry => identifier entry.1) color ⟨.fork record l r,outside⟩ forest represented unique
  have first := readRun.map_prefix (finishRead right) (reading_code identifier (identifier record.1) right)
  obtain ⟨target,moveRun,targetRep,moveBound⟩ := PackedDescentController.descend color right l r record outside forest represented
  let nextId := if right then identifier r.rootRecord.1 else identifier l.rootRecord.1
  have last := moveRun.map_prefix (finishMove nextId) (moving_code identifier (identifier record.1) right nextId)
  have readEndpoint : finishRead right (.found q record) = finishMove (ρ := ρ) nextId ((l.support color ∩ r.support color).sort (· ≤ ·)) := by
    simp only [finishRead,children,nextId]
  change Steps (program identifier (identifier record.1) right) initial forest
    (finishRead right (.found q record)) forest readWord readCost at first
  rw [readEndpoint] at first
  have complete := (first.append last).run rfl
  exact ⟨target,_,_,complete,targetRep,by omega⟩

end ChaCha.Paper20261030.PackedChildController
