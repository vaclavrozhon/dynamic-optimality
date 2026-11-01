import TangoSquared.Paper20261030.PhysicalPackedRotationBatch
import TangoSquared.Paper20261030.PhysicalPackedParentProgram
import TangoSquared.Paper20261030.PhysicalPackedChildProgram

/-! The read-driven logical rotation controller. Starting with the
current immutable identifier, it reads the root, descends to the pivot,
reads that pivot, returns to the parent, and runs the observed-mask batch.
The two pivot values and their child masks are obtained only by local reads.
-/

namespace TangoSquared.Paper20261030.PackedRotationProgram

open ColoredStorage SourcePointer ForestLocalProgram Structural PhysicalForestMetadata

variable {ρ ι η C : Type*} [DecidableEq ι] [DecidableEq η] [LinearOrder C] [Fintype C]

abbrev LogicalRecord (ρ η C : Type*) := ρ × Fields η C
abbrev FinderState (ρ ι η C : Type*) := PhysicalRecordFinder.State (LogicalRecord ρ η C) ι C

structure Inputs (ρ η C : Type*) where
  u : Finset C
  v : Finset C
  w : Finset C
  p : LogicalRecord ρ η C
  top : LogicalRecord ρ η C

def inputs (right : Bool) (first second : LogicalRecord ρ η C) : Option (Inputs ρ η C) :=
  match first.2.children,second.2.children with
  | some (l,r),some (a,b) =>
    if right then some ⟨a.colors,b.colors,r.colors,second,first⟩
    else some ⟨l.colors,a.colors,b.colors,first,second⟩
  | _,_ => none

inductive State (ρ ι η C : Type*) where
  | reading (phase : FinderState ρ ι η C)
  | descending (first : LogicalRecord ρ η C) (phase : PhysicalPackedChildController.State ρ ι η C)
  | pivot (first : LogicalRecord ρ η C) (id : η) (phase : FinderState ρ ι η C)
  | ascending (first second : LogicalRecord ρ η C) (phase : PhysicalPackedParentController.State ρ ι η C)
  | rotating (data : Inputs ρ η C) (phase : PhysicalPackedRotation.State (LogicalRecord ρ η C) ι C)
  | done (id : η)
  | error

def finishRead : FinderState ρ ι η C → State ρ ι η C
  | .found record => .descending record PhysicalPackedChildController.initial
  | phase => .reading phase

def finishDescent (first : LogicalRecord ρ η C) : PhysicalPackedChildController.State ρ ι η C → State ρ ι η C
  | .ready (.done id) => .pivot first id (.scan (Finset.univ.sort (· ≤ ·)))
  | phase => .descending first phase

def finishPivot (first : LogicalRecord ρ η C) (id : η) : FinderState ρ ι η C → State ρ ι η C
  | .found second => .ascending first second PhysicalPackedParentController.initial
  | phase => .pivot first id phase

def finishAscent (right : Bool) (first second : LogicalRecord ρ η C) :
    PhysicalPackedParentController.State ρ ι η C → State ρ ι η C
  | .done _ => match inputs right first second with
    | none => .error
    | some data => .rotating data (.scan (((data.u ∪ data.v) ∪ data.w).sort (· ≤ ·)))
  | phase => .ascending first second phase

def finishRotation (identifier : ρ → η) (right : Bool) (data : Inputs ρ η C) :
    PhysicalPackedRotation.State (LogicalRecord ρ η C) ι C → State ρ ι η C
  | .scan [] => .done (if right then identifier data.p.1 else identifier data.top.1)
  | phase => .rotating data phase

def initial : State ρ ι η C := .reading (.scan (Finset.univ.sort (· ≤ ·)))

def program (identifier : ρ → η) (wanted : η) (right : Bool) :
    Program (State ρ ι η C) C (Record (LogicalRecord ρ η C) ι)
  | .reading phase => (PhysicalRecordFinder.program (fun record => identifier record.1) wanted phase).mapState finishRead
  | .descending first phase => (PhysicalPackedChildController.program identifier (identifier first.1) (!right) phase).mapState (finishDescent first)
  | .pivot first id phase => (PhysicalRecordFinder.program (fun record => identifier record.1) id phase).mapState (finishPivot first id)
  | .ascending first second phase => (PhysicalPackedParentController.program identifier (identifier second.1) phase).mapState (finishAscent right first second)
  | .rotating data phase => (PhysicalPackedRotation.program (fun record => record.2.colors) right data.u data.v data.w data.p data.top phase).mapState
      (finishRotation identifier right data)
  | .done _ | .error => .halt

theorem read_code (identifier : ρ → η) (wanted : η) (right : Bool) (phase : FinderState ρ ι η C)
    (active : PhysicalRecordFinder.program (fun record => identifier record.1) wanted phase ≠ .halt) :
    program identifier wanted right (finishRead phase) =
      (PhysicalRecordFinder.program (fun record => identifier record.1) wanted phase).mapState finishRead := by
  cases phase with
  | found => exact False.elim (active rfl)
  | scan | parent | current => rfl

theorem descent_code (identifier : ρ → η) (wanted : η) (right : Bool) (first : LogicalRecord ρ η C)
    (phase : PhysicalPackedChildController.State ρ ι η C)
    (active : PhysicalPackedChildController.program identifier (identifier first.1) (!right) phase ≠ .halt) :
    program identifier wanted right (finishDescent first phase) =
      (PhysicalPackedChildController.program identifier (identifier first.1) (!right) phase).mapState (finishDescent first) := by
  cases phase with
  | running | error => rfl
  | ready state => cases state with
    | done => exact False.elim (active rfl)
    | reading | moving | error => rfl

theorem pivot_code (identifier : ρ → η) (wanted id : η) (right : Bool) (first : LogicalRecord ρ η C)
    (phase : FinderState ρ ι η C)
    (active : PhysicalRecordFinder.program (fun record => identifier record.1) id phase ≠ .halt) :
    program identifier wanted right (finishPivot first id phase) =
      (PhysicalRecordFinder.program (fun record => identifier record.1) id phase).mapState (finishPivot first id) := by
  cases phase with
  | found => exact False.elim (active rfl)
  | scan | parent | current => rfl

theorem ascent_code (identifier : ρ → η) (wanted : η) (right : Bool) (first second : LogicalRecord ρ η C)
    (phase : PhysicalPackedParentController.State ρ ι η C)
    (active : PhysicalPackedParentController.program identifier (identifier second.1) phase ≠ .halt) :
    program identifier wanted right (finishAscent right first second phase) =
      (PhysicalPackedParentController.program identifier (identifier second.1) phase).mapState (finishAscent right first second) := by
  cases phase with
  | done => exact False.elim (active rfl)
  | reading | parent | moving | error => rfl

theorem rotation_code (identifier : ρ → η) (wanted : η) (right : Bool) (data : Inputs ρ η C)
    (phase : PhysicalPackedRotation.State (LogicalRecord ρ η C) ι C)
    (active : PhysicalPackedRotation.program (fun record => record.2.colors) right data.u data.v data.w data.p data.top phase ≠ .halt) :
    program identifier wanted right (finishRotation identifier right data phase) =
      (PhysicalPackedRotation.program (fun record => record.2.colors) right data.u data.v data.w data.p data.top phase).mapState
        (finishRotation identifier right data) := by
  cases phase with
  | rotating => rfl
  | scan colors => cases colors with
    | nil => exact False.elim (active rfl)
    | cons => rfl

end TangoSquared.Paper20261030.PackedRotationProgram
