import ChaCha.Paper20261030.LocalPhysicalBoundaryRepair
import ChaCha.Paper20261030.SourceObserverReadiness
import ChaCha.Paper20261030.PackedContextReassembly

/-! Repairing physical fields throughout a finite exposed context.
The runtime blueprint contains only its fixed shape and block labels.
Each connector is repaired from local reads; each opaque block is visited
only at its root to update its parent. All block interiors are preserved.
An eight-block context takes exactly one hundred operations, regardless
of the sizes of the blocks. This kernel uses direct physical records;
`ComponentPhysicalRepair` executes it through the nested component datums.
-/

namespace ChaCha.Paper20261030.PhysicalContextRepair

open ColoredStorage SourcePointer SourceLocalProgram Structural OrderedContext
open PhysicalBoundaryRepair (Record)

variable {κ α ρ ι : Type*}

inductive Edge where
  | left
  | right
  | up

def Edge.move : Edge → DynamicOptimality.LocalProgram.Move
  | .left => .left
  | .right => .right
  | .up => .up

inductive Task (κ ι : Type*) where
  | visit (shape : Source κ Unit) (parent : Option ι)
  | move (action : Edge)

inductive State (κ ρ ι : Type*) where
  | ready (tasks : List (Task κ ι))
  | running (shape : Source κ Unit) (parent : Option ι) (tasks : List (Task κ ι))
      (phase : PhysicalBoundaryRepair.State ρ ι)

def branch : Source κ Unit → Bool
  | .leaf _ _ => false
  | .fork _ _ _ => true

def children (shape : Source κ Unit) (id : ι) (tasks : List (Task κ ι)) : List (Task κ ι) :=
  match shape with
  | .leaf _ _ => tasks
  | .fork _ left right =>
    .move .left :: .visit left (some id) :: .move .up ::
      .move .right :: .visit right (some id) :: .move .up :: tasks

def finish (shape : Source κ Unit) (parent : Option ι) (tasks : List (Task κ ι)) :
    PhysicalBoundaryRepair.State ρ ι → State κ ρ ι
  | .done id => .ready (children shape id tasks)
  | phase => .running shape parent tasks phase

def program (identifier : ρ → ι) : Program (State κ ρ ι) (Record ρ ι)
  | .ready [] => .halt
  | .ready (.move action :: tasks) => .nav action.move (.ready tasks)
  | .ready (.visit shape parent :: tasks) =>
    (PhysicalBoundaryRepair.program identifier parent (branch shape) .start).mapState (finish shape parent tasks)
  | .running shape parent tasks phase =>
    (PhysicalBoundaryRepair.program identifier parent (branch shape) phase).mapState (finish shape parent tasks)

theorem primitive_code (identifier : ρ → ι) (shape : Source κ Unit) (parent : Option ι)
    (tasks : List (Task κ ι)) (phase : PhysicalBoundaryRepair.State ρ ι)
    (active : PhysicalBoundaryRepair.program identifier parent (branch shape) phase ≠ .halt) :
    program identifier (finish shape parent tasks phase) =
      (PhysicalBoundaryRepair.program identifier parent (branch shape) phase).mapState (finish shape parent tasks) := by
  cases phase <;> first | rfl | exact False.elim (active rfl)

theorem primitive_prefix (identifier : ρ → ι) (shape : Source κ Unit) (parent : Option ι)
    (tasks : List (Task κ ι)) {before after : Cursor α (Record ρ ι)} {reads cost id}
    (run : Run (PhysicalBoundaryRepair.program identifier parent (branch shape)) .start before (.done id) after reads cost)
    (positive : 0 < cost) :
    Steps (program identifier) (.ready (.visit shape parent :: tasks)) before
      (.ready (children shape id tasks)) after reads cost := by
  have mapped := run.map_prefix (finish shape parent tasks) (primitive_code identifier shape parent tasks)
  exact mapped.change_start positive rfl

def input (identifier : ρ → ι) (blocks : κ → Source α ρ) (parents : κ → Option ι)
    (context : Source κ (Record ρ ι)) : Source α (Record ρ ι) :=
  substituteSource (fun key => annotate identifier (fun _ => (() : Unit)) (parents key) (blocks key)) context

def plain (blocks : κ → Source α ρ) (context : Source κ (Record ρ ι)) : Source α ρ :=
  substituteSource blocks (context.mapRecords Prod.fst)

theorem input_erases (identifier : ρ → ι) (blocks : κ → Source α ρ) (parents : κ → Option ι)
    (context : Source κ (Record ρ ι)) : (input identifier blocks parents context).mapRecords Prod.fst = plain blocks context := by
  induction context with
  | leaf key _ => exact annotate_erase identifier (fun _ => (() : Unit)) (parents key) (blocks key)
  | fork record left right ihl ihr =>
    change Source.fork record.1 ((input identifier blocks parents left).mapRecords Prod.fst)
      ((input identifier blocks parents right).mapRecords Prod.fst) =
      .fork record.1 (plain blocks left) (plain blocks right)
    rw [ihl,ihr]

theorem input_root (identifier : ρ → ι) (blocks : κ → Source α ρ) (parents : κ → Option ι)
    (context : Source κ (Record ρ ι)) : (input identifier blocks parents context).rootRecord.1 = (plain blocks context).rootRecord := by
  have equal := congrArg Source.rootRecord (input_erases identifier blocks parents context)
  simpa only [Source.mapRecords_root] using equal

def cost {τ : Type*} : Source κ τ → Nat
  | .leaf _ _ => 2
  | .fork _ left right => 12+cost left+cost right

theorem repair (identifier : ρ → ι) (blocks : κ → Source α ρ) (parents : κ → Option ι)
    (context : Source κ (Record ρ ι)) (parent : Option ι) (tasks : List (Task κ ι)) (outside) :
    ∃ reads, Steps (program identifier) (.ready (.visit (context.mapRecords (fun _ => ())) parent :: tasks))
      ⟨input identifier blocks parents context,outside⟩ (.ready tasks)
      ⟨annotate identifier (fun _ => (() : Unit)) parent (plain blocks context),outside⟩ reads (cost context) := by
  induction context generalizing parent tasks outside with
  | leaf key ignored =>
    exact ⟨_,primitive_prefix identifier (.leaf key ()) parent tasks
      (PhysicalBoundaryRepair.block_exact identifier (parents key) parent (blocks key) outside) (by change 0 < 2; decide)⟩
  | fork record left right ihl ihr =>
    let L := input identifier blocks parents left
    let R := input identifier blocks parents right
    let newL := annotate identifier (fun _ => (() : Unit)) (some (identifier record.1)) (plain blocks left)
    let newR := annotate identifier (fun _ => (() : Unit)) (some (identifier record.1)) (plain blocks right)
    let fresh : Record ρ ι := (record.1,fields identifier (fun _ => (() : Unit)) parent
      (.fork record.1 (plain blocks left) (plain blocks right)))
    let leftShape := left.mapRecords (fun _ => ())
    let rightShape := right.mapRecords (fun _ => ())
    let remaining := Task.move .up :: Task.move .right :: Task.visit rightShape (some (identifier record.1)) :: Task.move .up :: tasks
    have kernel : Run (PhysicalBoundaryRepair.program identifier parent true) .start ⟨.fork record L R,outside⟩
        (.done (identifier record.1)) ⟨.fork fresh L R,outside⟩ [record,L.rootRecord,R.rootRecord] 8 := by
      have actual := PhysicalBoundaryRepair.fork identifier parent record L R outside
      have equality : PhysicalBoundaryRepair.forkRecord parent record (identifier L.rootRecord.1) (identifier R.rootRecord.1) = fresh := by
        rw [input_root,input_root]
        exact PhysicalBoundaryRepair.forkRecord_exact identifier parent record.1 record.2 (plain blocks left) (plain blocks right)
      rw [equality] at actual
      exact actual
    have first := primitive_prefix identifier (.fork () leftShape rightShape) parent tasks kernel (by decide)
    have downLeft : Step (program identifier)
        (.ready (.move .left :: .visit leftShape (some (identifier record.1)) :: remaining))
        ⟨.fork fresh L R,outside⟩ (.ready (.visit leftShape (some (identifier record.1)) :: remaining))
        ⟨L,.left fresh R :: outside⟩ none := .nav rfl rfl
    obtain ⟨leftReads,leftRun⟩ := ihl (some (identifier record.1)) remaining (.left fresh R :: outside)
    have upLeft : Step (program identifier) (.ready remaining) ⟨newL,.left fresh R :: outside⟩
        (.ready (.move .right :: .visit rightShape (some (identifier record.1)) :: .move .up :: tasks))
        ⟨.fork fresh newL R,outside⟩ none := .nav rfl rfl
    have downRight : Step (program identifier)
        (.ready (.move .right :: .visit rightShape (some (identifier record.1)) :: .move .up :: tasks))
        ⟨.fork fresh newL R,outside⟩ (.ready (.visit rightShape (some (identifier record.1)) :: .move .up :: tasks))
        ⟨R,.right newL fresh :: outside⟩ none := .nav rfl rfl
    obtain ⟨rightReads,rightRun⟩ := ihr (some (identifier record.1)) (.move .up :: tasks) (.right newL fresh :: outside)
    have upRight : Step (program identifier) (.ready (.move .up :: tasks)) ⟨newR,.right newL fresh :: outside⟩
        (.ready tasks) ⟨.fork fresh newL newR,outside⟩ none := .nav rfl rfl
    have actual := first.append (downLeft.prefix.append (leftRun.append
      (upLeft.prefix.append (downRight.prefix.append (rightRun.append upRight.prefix)))))
    have costEqual : 8+(1+(cost left+(1+(1+(cost right+1))))) = cost (.fork record left right) := by
      simp only [cost]
      omega
    rw [costEqual] at actual
    refine ⟨[record,L.rootRecord,R.rootRecord]++leftReads++rightReads,?_⟩
    simpa only [Option.toList_none,List.nil_append,List.append_nil,List.append_assoc,
      input,plain,substituteSource,Source.mapRecords,annotate,L,R,newL,newR,fresh,leftShape,rightShape] using actual

theorem run (identifier : ρ → ι) (blocks : κ → Source α ρ) (parents : κ → Option ι)
    (context : Source κ (Record ρ ι)) (parent : Option ι) (outside) :
    ∃ reads, Run (program identifier) (.ready [.visit (context.mapRecords (fun _ => ())) parent])
      ⟨input identifier blocks parents context,outside⟩ (.ready [])
      ⟨annotate identifier (fun _ => (() : Unit)) parent (plain blocks context),outside⟩ reads (cost context) := by
  obtain ⟨reads,actual⟩ := repair identifier blocks parents context parent [] outside
  exact ⟨reads,actual.run rfl⟩

theorem cost_leaves {τ : Type*} (context : Source κ τ) : cost context+12 = 14*context.shape.leaves.length := by
  induction context with
  | leaf => rfl
  | fork record left right ihl ihr =>
    simp only [cost,Source.shape,RouterProjection.Router.leaves,List.length_append]
    omega

theorem eight_blocks {τ : Type*} (context : Source κ τ) (eight : context.shape.leaves.length = 8) : cost context = 100 := by
  have equal := cost_leaves context
  rw [eight] at equal
  omega

end ChaCha.Paper20261030.PhysicalContextRepair
