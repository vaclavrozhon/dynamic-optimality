import ChaCha.Paper20261030.LocalPhysicalBoundaryRepair

set_option autoImplicit false

/-!
# A root edit using only actually read child identifiers

The fork tour reads one whole root record and the two child ids, returns
to the root, and writes the computed record. It costs eight operations
and saves at most one whole record. At an opaque block root the two-step
variant performs no child traversal. The edit function is fixed by the
finite boundary blueprint and scalar parent id.
-/

namespace ChaCha.Paper20261030.RootNeighborEdit

open ColoredStorage SourcePointer SourceLocalProgram

variable {α ρ ι : Type*}

inductive State (ρ ι : Type*) where
  | start
  | writeRoot (fresh : ρ) (id : ι)
  | toLeft (old : ρ)
  | readLeft (old : ρ)
  | fromLeft (old : ρ) (left : ι)
  | toRight (old : ρ) (left : ι)
  | readRight (old : ρ) (left : ι)
  | fromRight (old : ρ) (left right : ι)
  | writeFork (old : ρ) (left right : ι)
  | done (id : ι)

def program (identifier : ρ → ι) (edit : ρ → Option (ι × ι) → ρ) (branch : Bool) : Program (State ρ ι) ρ
  | .start => .read (fun record _ => if branch then .toLeft record else .writeRoot (edit record none) (identifier record))
  | .writeRoot fresh id => .write fresh (.done id)
  | .toLeft old => .nav .left (.readLeft old)
  | .readLeft old => .read (fun record _ => .fromLeft old (identifier record))
  | .fromLeft old left => .nav .up (.toRight old left)
  | .toRight old left => .nav .right (.readRight old left)
  | .readRight old left => .read (fun record _ => .fromRight old left (identifier record))
  | .fromRight old left right => .nav .up (.writeFork old left right)
  | .writeFork old left right => .write (edit old (some (left,right))) (.done (identifier old))
  | .done _ => .halt

theorem fork (identifier : ρ → ι) (edit : ρ → Option (ι × ι) → ρ) (record : ρ)
    (left right : Source α ρ) (outside) :
    Run (program identifier edit true) .start ⟨.fork record left right,outside⟩ (.done (identifier record))
      ⟨.fork (edit record (some (identifier left.rootRecord,identifier right.rootRecord))) left right,outside⟩
      [record,left.rootRecord,right.rootRecord] 8 := by
  refine .next (Step.read (program := program identifier edit true) (next := fun record _ => State.toLeft record) rfl) ?_
  refine .next (Step.nav (program := program identifier edit true) (action := .left) (next := State.readLeft record) rfl rfl) ?_
  refine .next (Step.read (program := program identifier edit true) (next := fun current _ => State.fromLeft record (identifier current)) rfl) ?_
  refine .next (Step.nav (program := program identifier edit true) (action := .up) (next := State.toRight record (identifier left.rootRecord)) rfl rfl) ?_
  refine .next (Step.nav (program := program identifier edit true) (action := .right) (next := State.readRight record (identifier left.rootRecord)) rfl rfl) ?_
  refine .next (Step.read (program := program identifier edit true)
    (next := fun current _ => State.fromRight record (identifier left.rootRecord) (identifier current)) rfl) ?_
  refine .next (Step.nav (program := program identifier edit true) (action := .up)
    (next := State.writeFork record (identifier left.rootRecord) (identifier right.rootRecord)) rfl rfl) ?_
  exact .next (Step.write (program := program identifier edit true) rfl) (.halt rfl)

theorem block (identifier : ρ → ι) (edit : ρ → Option (ι × ι) → ρ) (source : Source α ρ) (outside) :
    Run (program identifier edit false) .start ⟨source,outside⟩ (.done (identifier source.rootRecord))
      ⟨source.setRoot (edit source.rootRecord none),outside⟩ [source.rootRecord] 2 := by
  refine .next (Step.read (program := program identifier edit false)
    (next := fun record _ => State.writeRoot (edit record none) (identifier record)) rfl) ?_
  exact .next (Step.write (program := program identifier edit false) rfl) (.halt rfl)

def workingRecords : State ρ ι → Nat
  | .start | .done _ => 0
  | _ => 1

theorem working_records (state : State ρ ι) : workingRecords state ≤ 1 := by cases state <;> simp [workingRecords]

end ChaCha.Paper20261030.RootNeighborEdit
