import ChaCha.Paper20261030.PackedOperationReadiness
import ChaCha.Paper20261030.PhysicalPackedWrite

/-! A single executable compiler from annotated source programs to the
physical color forest. Its registers contain the source control state,
the current immutable identifier, and the state of one local helper.
No source tree or prescribed execution is an input to the program.
-/

namespace ChaCha.Paper20261030.PackedSourceCompiler

open ColoredStorage SourcePointer ForestLocalProgram Structural PhysicalForestMetadata

variable {ρ ι η C σ : Type*} [DecidableEq ι] [DecidableEq η] [LinearOrder C] [Fintype C]

abbrev LogicalRecord (ρ η C : Type*) := ρ × Fields η C
abbrev FinderState (ρ ι η C : Type*) := PhysicalRecordFinder.State (LogicalRecord ρ η C) ι C

inductive State (σ ρ ι η C : Type*) where
  | ready (state : σ) (id : η)
  | reading (state : σ) (wanted : η) (phase : FinderState ρ ι η C)
  | child (next : σ) (wanted : η) (right : Bool) (phase : PhysicalPackedChildController.State ρ ι η C)
  | parent (next : σ) (wanted : η) (phase : PhysicalPackedParentController.State ρ ι η C)
  | rotation (next : σ) (wanted : η) (right : Bool) (phase : PackedRotationProgram.State ρ ι η C)
  | writing (next : σ) (wanted : η) (fresh : LogicalRecord ρ η C)
      (phase : PhysicalPackedWriteController.State (LogicalRecord ρ η C) ι C)
  | error

def finishRead (identifier : ρ → η) (source : SourceLocalProgram.Program σ (LogicalRecord ρ η C))
    (state : σ) (wanted : η) : FinderState ρ ι η C → State σ ρ ι η C
  | .found record => match source state with
    | .read next => .ready (next record record.2.children.isNone) (identifier record.1)
    | _ => .error
  | phase => .reading state wanted phase

def finishChild (next : σ) (wanted : η) (right : Bool) : PhysicalPackedChildController.State ρ ι η C → State σ ρ ι η C
  | .ready (.done id) => .ready next id
  | phase => .child next wanted right phase

def finishParent (next : σ) (wanted : η) : PhysicalPackedParentController.State ρ ι η C → State σ ρ ι η C
  | .done id => .ready next id
  | phase => .parent next wanted phase

def finishRotation (next : σ) (wanted : η) (right : Bool) : PackedRotationProgram.State ρ ι η C → State σ ρ ι η C
  | .done id => .ready next id
  | phase => .rotation next wanted right phase

def finishWrite (next : σ) (wanted : η) (fresh : LogicalRecord ρ η C) :
    PhysicalPackedWriteController.State (LogicalRecord ρ η C) ι C → State σ ρ ι η C
  | .ready .done => .ready next wanted
  | phase => .writing next wanted fresh phase

def program (identifier : ρ → η) (source : SourceLocalProgram.Program σ (LogicalRecord ρ η C)) :
    Program (State σ ρ ι η C) C (Record (LogicalRecord ρ η C) ι)
  | .ready state wanted => match source state with
    | .halt => .halt
    | .read _ => (PhysicalRecordFinder.program (fun record => identifier record.1) wanted
        (.scan (Finset.univ.sort (· ≤ ·)))).mapState (finishRead identifier source state wanted)
    | .nav .left next => (PhysicalPackedChildController.program identifier wanted false PhysicalPackedChildController.initial).mapState (finishChild next wanted false)
    | .nav .right next => (PhysicalPackedChildController.program identifier wanted true PhysicalPackedChildController.initial).mapState (finishChild next wanted true)
    | .nav .up next => (PhysicalPackedParentController.program identifier wanted PhysicalPackedParentController.initial).mapState (finishParent next wanted)
    | .nav .rotateRight next => (PackedRotationProgram.program identifier wanted true PackedRotationProgram.initial).mapState (finishRotation next wanted true)
    | .nav .rotateLeft next => (PackedRotationProgram.program identifier wanted false PackedRotationProgram.initial).mapState (finishRotation next wanted false)
    | .write fresh next => (PhysicalPackedWriteController.program (fun record => identifier record.1) wanted fresh
        (.ready (.scan (Finset.univ.sort (· ≤ ·))))).mapState (finishWrite next wanted fresh)
  | .reading state wanted phase => (PhysicalRecordFinder.program (fun record => identifier record.1) wanted phase).mapState (finishRead identifier source state wanted)
  | .child next wanted right phase => (PhysicalPackedChildController.program identifier wanted right phase).mapState (finishChild next wanted right)
  | .parent next wanted phase => (PhysicalPackedParentController.program identifier wanted phase).mapState (finishParent next wanted)
  | .rotation next wanted right phase => (PackedRotationProgram.program identifier wanted right phase).mapState (finishRotation next wanted right)
  | .writing next wanted fresh phase => (PhysicalPackedWriteController.program (fun record => identifier record.1) wanted fresh phase).mapState (finishWrite next wanted fresh)
  | .error => .halt

theorem read_code (identifier : ρ → η) (source : SourceLocalProgram.Program σ (LogicalRecord ρ η C))
    (state : σ) (wanted : η) (phase : FinderState ρ ι η C)
    (active : PhysicalRecordFinder.program (fun record => identifier record.1) wanted phase ≠ .halt) :
    program identifier source (finishRead identifier source state wanted phase) =
      (PhysicalRecordFinder.program (fun record => identifier record.1) wanted phase).mapState (finishRead identifier source state wanted) := by
  cases phase with
  | found => exact False.elim (active rfl)
  | scan | parent | current => rfl

theorem child_code (identifier : ρ → η) (source : SourceLocalProgram.Program σ (LogicalRecord ρ η C))
    (next : σ) (wanted : η) (right : Bool) (phase : PhysicalPackedChildController.State ρ ι η C)
    (active : PhysicalPackedChildController.program identifier wanted right phase ≠ .halt) :
    program identifier source (finishChild next wanted right phase) =
      (PhysicalPackedChildController.program identifier wanted right phase).mapState (finishChild next wanted right) := by
  cases phase with
  | running | error => rfl
  | ready state => cases state with
    | done => exact False.elim (active rfl)
    | reading | moving | error => rfl

theorem parent_code (identifier : ρ → η) (source : SourceLocalProgram.Program σ (LogicalRecord ρ η C))
    (next : σ) (wanted : η) (phase : PhysicalPackedParentController.State ρ ι η C)
    (active : PhysicalPackedParentController.program identifier wanted phase ≠ .halt) :
    program identifier source (finishParent next wanted phase) =
      (PhysicalPackedParentController.program identifier wanted phase).mapState (finishParent next wanted) := by
  cases phase with
  | done => exact False.elim (active rfl)
  | reading | parent | moving | error => rfl

theorem rotation_code (identifier : ρ → η) (source : SourceLocalProgram.Program σ (LogicalRecord ρ η C))
    (next : σ) (wanted : η) (right : Bool) (phase : PackedRotationProgram.State ρ ι η C)
    (active : PackedRotationProgram.program identifier wanted right phase ≠ .halt) :
    program identifier source (finishRotation next wanted right phase) =
      (PackedRotationProgram.program identifier wanted right phase).mapState (finishRotation next wanted right) := by
  cases phase with
  | done => exact False.elim (active rfl)
  | reading | descending | pivot | ascending | rotating | error => rfl

theorem write_code (identifier : ρ → η) (source : SourceLocalProgram.Program σ (LogicalRecord ρ η C))
    (next : σ) (wanted : η) (fresh : LogicalRecord ρ η C)
    (phase : PhysicalPackedWriteController.State (LogicalRecord ρ η C) ι C)
    (active : PhysicalPackedWriteController.program (fun record => identifier record.1) wanted fresh phase ≠ .halt) :
    program identifier source (finishWrite next wanted fresh phase) =
      (PhysicalPackedWriteController.program (fun record => identifier record.1) wanted fresh phase).mapState (finishWrite next wanted fresh) := by
  cases phase with
  | running | error => rfl
  | ready state => cases state with
    | done => exact False.elim (active rfl)
    | scan | writing => rfl

end ChaCha.Paper20261030.PackedSourceCompiler
