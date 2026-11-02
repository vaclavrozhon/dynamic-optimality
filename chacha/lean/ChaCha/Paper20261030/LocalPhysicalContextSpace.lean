import ChaCha.Paper20261030.LocalPhysicalContextRepair

/-! A decreasing control budget for the finite physical-boundary repair.
One visit is charged by its fixed source-shape cost, one explicit move by
one. The pending control data never increase this budget, and at most one
record is retained by the active primitive. These are bounds for this
kernel, not a complete workspace theorem for the primary algorithm.
-/

namespace ChaCha.Paper20261030.PhysicalContextRepair

open ColoredStorage SourcePointer SourceLocalProgram
open PhysicalBoundaryRepair (Record)

variable {κ α ρ ι : Type*}

def taskBudget : List (Task κ ι) → Nat
  | [] => 0
  | .move _ :: rest => 1+taskBudget rest
  | .visit shape _ :: rest => cost shape+taskBudget rest

def budget : State κ ρ ι → Nat
  | .ready tasks => taskBudget tasks
  | .running shape _ tasks _ => cost shape+taskBudget tasks

theorem finish_budget (shape : Source κ Unit) (parent : Option ι) (tasks : List (Task κ ι))
    (phase : PhysicalBoundaryRepair.State ρ ι) : budget (finish shape parent tasks phase) ≤ cost shape+taskBudget tasks := by
  cases phase <;> first | exact le_rfl | skip
  case done id =>
    cases shape <;> simp only [finish,children,budget,taskBudget,cost] <;> omega

private def AllNext {σ τ : Type*} (predicate : σ → Prop) : Instruction σ τ → Prop
  | .halt => True
  | .read next => ∀ record leaf, predicate (next record leaf)
  | .nav _ next | .write _ next => predicate next

private theorem allNext_map {σ τ υ : Type*} (predicate : τ → Prop) (f : σ → τ)
    (instruction : Instruction σ υ) (valid : ∀ state, predicate (f state)) :
    AllNext predicate (instruction.mapState f) := by
  cases instruction <;> simp_all [Instruction.mapState,AllNext]

private theorem instruction_budget (identifier : ρ → ι) (state : State κ ρ ι) :
    AllNext (fun next => budget next ≤ budget state) (program identifier state) := by
  cases state with
  | running shape parent tasks phase =>
    exact allNext_map _ _ _ (finish_budget shape parent tasks)
  | ready tasks => cases tasks with
    | nil => trivial
    | cons task rest => cases task with
      | move action => simp only [program,AllNext,budget,taskBudget]; omega
      | visit shape parent =>
        change AllNext (fun next => budget next ≤ cost shape+taskBudget rest)
          ((PhysicalBoundaryRepair.program identifier parent (branch shape) .start).mapState (finish shape parent rest))
        exact allNext_map _ _ _ (finish_budget shape parent rest)

theorem step_budget (identifier : ρ → ι) {state next : State κ ρ ι}
    {before after : Cursor α (Record ρ ι)} {entry}
    (step : Step (program identifier) state before next after entry) : budget next ≤ budget state := by
  have bounded := instruction_budget identifier state
  cases step with
  | read instruction =>
    simp only [instruction,AllNext] at bounded
    exact bounded _ _
  | nav instruction moved => simpa only [instruction,AllNext] using bounded
  | write instruction => simpa only [instruction,AllNext] using bounded

theorem steps_budget (identifier : ρ → ι) {state next : State κ ρ ι}
    {before after : Cursor α (Record ρ ι)} {reads steps}
    (execution : Steps (program identifier) state before next after reads steps) : budget next ≤ budget state := by
  induction execution with
  | nil => exact le_rfl
  | next first rest ih => exact ih.trans (step_budget identifier first)

theorem cost_mapRecords {σ τ : Type*} (f : σ → τ) (context : Source κ σ) : cost (context.mapRecords f) = cost context := by
  induction context <;> simp_all only [Source.mapRecords,cost]

theorem reachable_budget (identifier : ρ → ι) (shape : Source κ Unit) (parent : Option ι)
    {state : State κ ρ ι} {before after : Cursor α (Record ρ ι)} {reads steps}
    (execution : Steps (program identifier) (.ready [.visit shape parent]) before state after reads steps) :
    budget state ≤ cost shape := by
  simpa only [budget,taskBudget,Nat.add_zero] using steps_budget identifier execution

def workingRecords : State κ ρ ι → Nat
  | .ready _ => 0
  | .running _ _ _ phase => PhysicalBoundaryRepair.workingRecords phase

theorem working_records (state : State κ ρ ι) : workingRecords state ≤ 1 := by
  cases state with
  | ready => exact Nat.zero_le _
  | running shape parent tasks phase => exact PhysicalBoundaryRepair.working_records phase

theorem eight_reachable (identifier : ρ → ι) (shape : Source κ Unit) (parent : Option ι)
    (eight : shape.shape.leaves.length = 8)
    {state : State κ ρ ι} {before after : Cursor α (Record ρ ι)} {reads steps}
    (execution : Steps (program identifier) (.ready [.visit shape parent]) before state after reads steps) :
    budget state ≤ 100 ∧ workingRecords state ≤ 1 := by
  have bound := reachable_budget identifier shape parent execution
  rw [eight_blocks shape eight] at bound
  exact ⟨bound,working_records state⟩

end ChaCha.Paper20261030.PhysicalContextRepair
