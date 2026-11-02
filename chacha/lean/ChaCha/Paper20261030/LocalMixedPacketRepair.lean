import ChaCha.Paper20261030.MixedPacketRepairPlan
import ChaCha.Paper20261030.LocalPhysicalContextSpace

set_option autoImplicit false

/-!
# One local traversal repairs all exposed mixed packet layers

At each exposed fork the program reads the two actual child-root ids.
It repairs every local packet layer in one root write, then visits its
two finite-context children. At an opaque block it changes only the root.
The scalar layer plan chooses logical child orientation and resets parent
tracking when an attachment enters another component.

The cost is `14 * leaves - 12`, hence at most 100 for eight blocks.
Packet lengths, logical data, header contents, and immutable ids are
preserved. Identifying this generic output with the canonical repaired
head representation additionally requires the head-specific plan proof.
-/

namespace ChaCha.Paper20261030.MixedPacketRepair

open ColoredStorage SourcePointer SourceLocalProgram Structural PhysicalPacketStaging
open PhysicalContextRepair (Edge)

variable {κ α β ρ ι : Type*}

abbrev Cell (α ρ ι : Type*) := PacketLayers.Context.Cell α ρ ι

def Fits : Source κ Layers → Source β (Cell α ρ ι) → Prop
  | .leaf _ _,_ => True
  | .fork _ left right,.fork _ l r => Fits left l ∧ Fits right r
  | .fork _ _ _,.leaf _ _ => False

def output : Source κ Layers → Option ι → Source β (Cell α ρ ι) → Source β (Cell α ρ ι)
  | .leaf _ plan,parent,source => source.setRoot (cell plan parent source.rootRecord none)
  | .fork plan left right,parent,.fork record l r =>
      .fork (cell plan parent record (some (l.rootRecord.1,r.rootRecord.1)))
        (output left (childParent plan record.1) l) (output right (childParent plan record.1) r)
  | .fork _ _ _,_,source => source

theorem identifiers (context : Source κ Layers) (parent : Option ι) (source : Source β (Cell α ρ ι)) :
    (output context parent source).mapRecords Prod.fst = source.mapRecords Prod.fst := by
  induction context generalizing parent source with
  | leaf key plan => cases source <;> rfl
  | fork plan left right ihl ihr => cases source with
    | leaf => rfl
    | fork record l r => simp only [output,Source.mapRecords,cell,ihl,ihr]

def eraseCell (record : Cell α ρ ι) := (record.1,erase record.2)

theorem erases (context : Source κ Layers) (parent : Option ι) (source : Source β (Cell α ρ ι)) :
    (output context parent source).mapRecords eraseCell = source.mapRecords eraseCell := by
  induction context generalizing parent source with
  | leaf key plan =>
    cases source <;> simp only [output,Source.setRoot,Source.rootRecord,Source.mapRecords,cell,eraseCell,edit_erases]
  | fork plan left right ihl ihr => cases source with
    | leaf => rfl
    | fork record l r => simp only [output,Source.mapRecords,cell,eraseCell,edit_erases,ihl,ihr]

theorem preserves (predicate : Cell α ρ ι → Prop)
    (stable : ∀ plan parent record children, predicate record → predicate (cell plan parent record children))
    (context : Source κ Layers) (parent : Option ι) (source : Source β (Cell α ρ ι))
    (valid : SourceRecordPredicate.Holds predicate source) : SourceRecordPredicate.Holds predicate (output context parent source) := by
  induction context generalizing parent source with
  | leaf key plan =>
    exact SourceRecordPredicate.setRoot predicate source _ valid (stable plan parent _ none (SourceRecordPredicate.root _ _ valid))
  | fork plan left right ihl ihr => cases source with
    | leaf => exact valid
    | fork record l r =>
      obtain ⟨rootValid,leftValid,rightValid⟩ := (SourceRecordPredicate.fork predicate record l r).mp valid
      exact (SourceRecordPredicate.fork predicate _ _ _).mpr
        ⟨stable plan parent record _ rootValid,ihl _ l leftValid,ihr _ r rightValid⟩

theorem alignment (markerId : ι) (context : Source κ Layers) (parent : Option ι) (source : Source β (Cell α ρ ι))
    (valid : SourceRecordPredicate.Holds (PacketAlignment.Predicate markerId) source) :
    SourceRecordPredicate.Holds (PacketAlignment.Predicate markerId) (output context parent source) :=
  preserves _ (fun plan parent record children valid => edit_alignment markerId record.1 plan parent children record.2 valid)
    context parent source valid

theorem marker_free (markerId : ι) (context : Source κ Layers) (parent : Option ι) (source : Source β (Cell α ρ ι))
    (valid : SourceRecordPredicate.Holds (MarkerFreePackets.Vertex markerId) source) :
    SourceRecordPredicate.Holds (MarkerFreePackets.Vertex markerId) (output context parent source) :=
  preserves _ (fun plan parent record children valid => edit_clear markerId plan parent children record.2 valid)
    context parent source valid

inductive Task (κ ι : Type*) where
  | visit (context : Source κ Layers) (parent : Option ι)
  | move (edge : Edge)

inductive State (κ α ρ ι : Type*) where
  | ready (tasks : List (Task κ ι))
  | running (context : Source κ Layers) (parent : Option ι) (tasks : List (Task κ ι))
      (phase : RootNeighborEdit.State (Cell α ρ ι) ι)

def branch : Source κ Layers → Bool
  | .leaf _ _ => false
  | .fork _ _ _ => true

def children (context : Source κ Layers) (id : ι) (tasks : List (Task κ ι)) : List (Task κ ι) :=
  match context with
  | .leaf _ _ => tasks
  | .fork plan left right =>
      .move .left :: .visit left (childParent plan id) :: .move .up ::
        .move .right :: .visit right (childParent plan id) :: .move .up :: tasks

def finish (context : Source κ Layers) (parent : Option ι) (tasks : List (Task κ ι)) :
    RootNeighborEdit.State (Cell α ρ ι) ι → State κ α ρ ι
  | .done id => .ready (children context id tasks)
  | phase => .running context parent tasks phase

def program : Program (State κ α ρ ι) (Cell α ρ ι)
  | .ready [] => .halt
  | .ready (.move edge :: tasks) => .nav edge.move (.ready tasks)
  | .ready (.visit context parent :: tasks) =>
      (RootNeighborEdit.program Prod.fst (cell context.rootRecord parent) (branch context) .start).mapState (finish context parent tasks)
  | .running context parent tasks phase =>
      (RootNeighborEdit.program Prod.fst (cell context.rootRecord parent) (branch context) phase).mapState (finish context parent tasks)

theorem primitive_code (context : Source κ Layers) (parent : Option ι) (tasks : List (Task κ ι))
    (phase : RootNeighborEdit.State (Cell α ρ ι) ι)
    (active : RootNeighborEdit.program Prod.fst (cell context.rootRecord parent) (branch context) phase ≠ .halt) :
    program (finish context parent tasks phase) =
      (RootNeighborEdit.program Prod.fst (cell context.rootRecord parent) (branch context) phase).mapState (finish context parent tasks) := by
  cases phase <;> first | rfl | exact False.elim (active rfl)

theorem primitive_prefix (context : Source κ Layers) (parent : Option ι) (tasks : List (Task κ ι))
    {before after : Cursor β (Cell α ρ ι)} {reads cost id}
    (run : Run (RootNeighborEdit.program Prod.fst (cell context.rootRecord parent) (branch context))
      .start before (.done id) after reads cost) (positive : 0 < cost) :
    Steps program (.ready (.visit context parent :: tasks)) before (.ready (children context id tasks)) after reads cost := by
  have mapped := run.map_prefix (finish context parent tasks) (primitive_code context parent tasks)
  exact mapped.change_start positive rfl

theorem repair (context : Source κ Layers) (parent : Option ι) (source : Source β (Cell α ρ ι))
    (fits : Fits context source) (tasks : List (Task κ ι)) (outside) :
    ∃ reads, Steps program (.ready (.visit context parent :: tasks)) ⟨source,outside⟩ (.ready tasks)
      ⟨output context parent source,outside⟩ reads (PhysicalContextRepair.cost context) := by
  induction context generalizing parent source tasks outside with
  | leaf key plan =>
    exact ⟨_,primitive_prefix (.leaf key plan) parent tasks
      (RootNeighborEdit.block Prod.fst (cell plan parent) source outside) (by change 0 < 2; decide)⟩
  | fork plan left right ihl ihr =>
    cases source with
    | leaf => exact False.elim fits
    | fork record l r =>
      let fresh := cell plan parent record (some (l.rootRecord.1,r.rootRecord.1))
      let nextParent := childParent plan record.1
      let newLeft := output left nextParent l
      let newRight := output right nextParent r
      let remaining := Task.move .up :: .move .right :: .visit right nextParent :: .move .up :: tasks
      have kernel := RootNeighborEdit.fork Prod.fst (cell plan parent) record l r outside
      have first := primitive_prefix (.fork plan left right) parent tasks kernel (by decide)
      have downLeft : Step program
          (.ready (.move .left :: .visit left nextParent :: remaining)) ⟨.fork fresh l r,outside⟩
          (.ready (.visit left nextParent :: remaining)) ⟨l,.left fresh r :: outside⟩ none := .nav rfl rfl
      obtain ⟨leftReads,leftRun⟩ := ihl nextParent l fits.1 remaining (.left fresh r :: outside)
      have upLeft : Step program (.ready remaining) ⟨newLeft,.left fresh r :: outside⟩
          (.ready (.move .right :: .visit right nextParent :: .move .up :: tasks)) ⟨.fork fresh newLeft r,outside⟩ none := .nav rfl rfl
      have downRight : Step program (.ready (.move .right :: .visit right nextParent :: .move .up :: tasks))
          ⟨.fork fresh newLeft r,outside⟩ (.ready (.visit right nextParent :: .move .up :: tasks))
          ⟨r,.right newLeft fresh :: outside⟩ none := .nav rfl rfl
      obtain ⟨rightReads,rightRun⟩ := ihr nextParent r fits.2 (.move .up :: tasks) (.right newLeft fresh :: outside)
      have upRight : Step program (.ready (.move .up :: tasks)) ⟨newRight,.right newLeft fresh :: outside⟩
          (.ready tasks) ⟨.fork fresh newLeft newRight,outside⟩ none := .nav rfl rfl
      have actual := first.append (downLeft.prefix.append (leftRun.append
        (upLeft.prefix.append (downRight.prefix.append (rightRun.append upRight.prefix)))))
      have costEq : 8+(1+(PhysicalContextRepair.cost left+(1+(1+(PhysicalContextRepair.cost right+1))))) =
          PhysicalContextRepair.cost (.fork plan left right) := by simp only [PhysicalContextRepair.cost]; omega
      rw [costEq] at actual
      exact ⟨_,actual⟩

theorem run (context : Source κ Layers) (parent : Option ι) (source : Source β (Cell α ρ ι))
    (fits : Fits context source) (outside) :
    ∃ reads, Run program (.ready [.visit context parent]) ⟨source,outside⟩ (.ready [])
      ⟨output context parent source,outside⟩ reads (PhysicalContextRepair.cost context) := by
  obtain ⟨reads,actual⟩ := repair context parent source fits [] outside
  exact ⟨reads,actual.run rfl⟩

theorem eight_bound (context : Source κ Layers) (small : context.shape.leaves.length ≤ 8) : PhysicalContextRepair.cost context ≤ 100 := by
  have counted := PhysicalContextRepair.cost_leaves context
  omega

def workingRecords : State κ α ρ ι → Nat
  | .ready _ => 0
  | .running _ _ _ phase => RootNeighborEdit.workingRecords phase

theorem working_records (state : State κ α ρ ι) : workingRecords state ≤ 1 := by
  cases state with
  | ready => exact Nat.zero_le _
  | running => exact RootNeighborEdit.working_records _

end ChaCha.Paper20261030.MixedPacketRepair
