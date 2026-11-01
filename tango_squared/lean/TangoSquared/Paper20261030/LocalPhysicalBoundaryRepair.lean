import TangoSquared.Paper20261030.StructuralReadiness
import TangoSquared.Paper20261030.MultiSourceSingleCursor

/-!
# Local repair of physical pointer fields at an exposed boundary

The parent identifier is retained by the boundary controller. At a
routing fork, the program reads the current record and the two reached
child-root identifiers, then writes the exact new physical descriptors.
It does not use the old parent/child fields to navigate. At an opaque
block root it changes only the parent field, leaving the block interior
and its existing child descriptors untouched.

The two kernels cost eight and two operations, respectively. Their
placement in the nested physical-datum wrapper is in `ComponentPhysicalRepair`.
-/

namespace TangoSquared.Paper20261030.PhysicalBoundaryRepair

open ColoredStorage SourcePointer SourceLocalProgram Structural

variable {α ρ ι : Type*}

abbrev Record (ρ ι : Type*) := ρ × Fields ι Unit

def forkRecord (parent : Option ι) (old : Record ρ ι) (left right : ι) : Record ρ ι :=
  (old.1,⟨parent,{()},some (⟨left,{()}⟩,⟨right,{()}⟩)⟩)

inductive State (ρ ι : Type*) where
  | start
  | writeParent (fresh : Record ρ ι) (id : ι)
  | toLeft (old : Record ρ ι)
  | readLeft (old : Record ρ ι)
  | fromLeft (old : Record ρ ι) (left : ι)
  | toRight (old : Record ρ ι) (left : ι)
  | readRight (old : Record ρ ι) (left : ι)
  | fromRight (old : Record ρ ι) (left right : ι)
  | writeFork (old : Record ρ ι) (left right : ι)
  | done (id : ι)

def program (identifier : ρ → ι) (parent : Option ι) (branchPresent : Bool) :
    Program (State ρ ι) (Record ρ ι)
  | .start => .read (fun record _ => if branchPresent then .toLeft record
      else .writeParent (reparent parent record) (identifier record.1))
  | .writeParent fresh id => .write fresh (.done id)
  | .toLeft old => .nav .left (.readLeft old)
  | .readLeft old => .read (fun record _ => .fromLeft old (identifier record.1))
  | .fromLeft old left => .nav .up (.toRight old left)
  | .toRight old left => .nav .right (.readRight old left)
  | .readRight old left => .read (fun record _ => .fromRight old left (identifier record.1))
  | .fromRight old left right => .nav .up (.writeFork old left right)
  | .writeFork old left right => .write (forkRecord parent old left right) (.done (identifier old.1))
  | .done _ => .halt

theorem fork (identifier : ρ → ι) (parent : Option ι) (old : Record ρ ι)
    (left right : Source α (Record ρ ι)) (outside) :
    Run (program identifier parent true) .start ⟨.fork old left right,outside⟩ (.done (identifier old.1))
      ⟨.fork (forkRecord parent old (identifier left.rootRecord.1) (identifier right.rootRecord.1)) left right,outside⟩
      [old,left.rootRecord,right.rootRecord] 8 := by
  refine .next (Step.read (program := program identifier parent true)
    (next := fun record _ => State.toLeft record) rfl) ?_
  refine .next (Step.nav (program := program identifier parent true) (action := .left)
    (next := State.readLeft old) rfl rfl) ?_
  refine .next (Step.read (program := program identifier parent true)
    (next := fun record _ => State.fromLeft old (identifier record.1)) rfl) ?_
  refine .next (Step.nav (program := program identifier parent true) (action := .up)
    (next := State.toRight old (identifier left.rootRecord.1)) rfl rfl) ?_
  refine .next (Step.nav (program := program identifier parent true) (action := .right)
    (next := State.readRight old (identifier left.rootRecord.1)) rfl rfl) ?_
  refine .next (Step.read (program := program identifier parent true)
    (next := fun record _ => State.fromRight old (identifier left.rootRecord.1) (identifier record.1)) rfl) ?_
  refine .next (Step.nav (program := program identifier parent true) (action := .up)
    (next := State.writeFork old (identifier left.rootRecord.1) (identifier right.rootRecord.1)) rfl rfl) ?_
  exact .next (Step.write (program := program identifier parent true) rfl) (.halt rfl)

theorem block (identifier : ρ → ι) (parent : Option ι) (source : Source α (Record ρ ι)) (outside) :
    Run (program identifier parent false) .start ⟨source,outside⟩ (.done (identifier source.rootRecord.1))
      ⟨source.setRoot (reparent parent source.rootRecord),outside⟩ [source.rootRecord] 2 := by
  refine .next (Step.read (program := program identifier parent false)
    (next := fun record _ => State.writeParent (reparent parent record) (identifier record.1)) rfl) ?_
  exact .next (Step.write (program := program identifier parent false) rfl) (.halt rfl)

theorem unit_support (source : Source α ρ) : source.support (fun _ => (() : Unit)) = {()} := by
  induction source <;> simp_all only [Source.support,Finset.union_self]

theorem forkRecord_exact (identifier : ρ → ι) (parent : Option ι) (record : ρ) (stale : Fields ι Unit)
    (left right : Source α ρ) :
    forkRecord parent (record,stale) (identifier left.rootRecord) (identifier right.rootRecord) =
      (record,fields identifier (fun _ => (() : Unit)) parent (.fork record left right)) := by
  simp only [forkRecord,fields,descriptor,Source.support,unit_support,Finset.union_self]

theorem block_exact (identifier : ρ → ι) (oldParent parent : Option ι) (source : Source α ρ) (outside) :
    Run (program identifier parent false) .start
      ⟨annotate identifier (fun _ => (() : Unit)) oldParent source,outside⟩ (.done (identifier source.rootRecord))
      ⟨annotate identifier (fun _ => (() : Unit)) parent source,outside⟩
      [(annotate identifier (fun _ => (() : Unit)) oldParent source).rootRecord] 2 := by
  have actual := block identifier parent (annotate identifier (fun _ => (() : Unit)) oldParent source) outside
  have changed : (annotate identifier (fun _ => (() : Unit)) oldParent source).setRoot
      (reparent parent (annotate identifier (fun _ => (() : Unit)) oldParent source).rootRecord) =
      annotate identifier (fun _ => (() : Unit)) parent source := by
    rw [reparent_root,annotate_root]
    exact (annotate_parent identifier (fun _ => (() : Unit)) oldParent parent source).symm
  rw [changed] at actual
  simpa only [annotate_root] using actual

def workingRecords : State ρ ι → Nat
  | .start | .done _ => 0
  | _ => 1

theorem working_records (state : State ρ ι) : workingRecords state ≤ 1 := by
  cases state <;> simp only [workingRecords] <;> omega

end TangoSquared.Paper20261030.PhysicalBoundaryRepair
