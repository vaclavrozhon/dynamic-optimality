import DynamicOptimality.LocalSnapshot

/-! Space used by the concrete snapshot controller. The explicit stack
and partial snapshots retain at most one record for each charged read.
Consequently the four-level observer stores at most fifteen records at
every prefix of its execution, not just at the end of the tour. -/

namespace DynamicOptimality.LocalSnapshot

open TangoSquared.MTR TangoSquared.Paper20261030.Auxiliary LocalProgram

variable {α ρ : Type*}

def Frame.records : Frame α ρ → Nat
  | .left _ _ _ => 1
  | .right _ leftSnapshot => 1+leftSnapshot.records.length

def stackRecords (stack : List (Frame α ρ)) : Nat := (stack.map Frame.records).sum

def State.records : State α ρ → Nat
  | .read _ stack => stackRecords stack
  | .left _ _ _ stack => 1+stackRecords stack
  | .right _ _ leftSnapshot stack => 1+leftSnapshot.records.length+stackRecords stack
  | .up result frame stack => result.records.length+frame.records+stackRecords stack
  | .done result => result.records.length

theorem node_records (entry : Record α ρ) (left right : Snapshot α ρ) :
    (node entry left right).records.length = 1+left.records.length+right.records.length := by
  rcases entry with ⟨size,key,value⟩
  simp [node,TangoSquared.Paper20261030.Auxiliary.Snapshot.records]
  omega

theorem finish_records (result : Snapshot α ρ) (stack : List (Frame α ρ)) :
    (finish result stack).records = result.records.length+stackRecords stack := by
  cases stack <;> simp [finish,State.records,stackRecords,Nat.add_assoc]

theorem afterLeft_records (depth : Nat) (entry : Record α ρ) (rightEmpty : Bool)
    (left : Snapshot α ρ) (stack : List (Frame α ρ)) :
    (afterLeft depth entry rightEmpty left stack).records = 1+left.records.length+stackRecords stack := by
  cases rightEmpty with
  | false => rfl
  | true =>
    change (finish (node entry left .empty) stack).records = _
    rw [finish_records,node_records]
    rfl

theorem step_records {state next : State α ρ} {before after : Metadata.Cursor α (fun _ => ρ)} {entry}
    (step : Step program state before next after entry) : next.records = state.records+entry.toList.length := by
  cases step with
  | @read next cursor view instruction observed =>
    cases state with
    | read depth stack =>
      cases depth with
      | zero =>
        simp only [program,Instruction.read.injEq] at instruction
        rw [← instruction]
        change (finish (node view.entry .unseen .unseen) stack).records = stackRecords stack+1
        rw [finish_records,node_records]
        simp [TangoSquared.Paper20261030.Auxiliary.Snapshot.records,Nat.add_comm]
      | succ depth =>
        simp only [program,Instruction.read.injEq] at instruction
        rw [← instruction]
        dsimp only
        split
        · rw [afterLeft_records]
          simp [State.records,Nat.add_comm,TangoSquared.Paper20261030.Auxiliary.Snapshot.records]
        · simp [State.records,Nat.add_comm]
    | left | right | done => simp [program] at instruction
    | up result frame stack => cases frame <;> simp [program] at instruction
  | @nav next before after action instruction moved =>
    cases state with
    | read depth stack => cases depth <;> simp [program] at instruction
    | done => simp [program] at instruction
    | left depth entry rightEmpty stack =>
      simp only [program,Instruction.nav.injEq] at instruction
      obtain ⟨rfl,rfl⟩ := instruction
      simp [State.records,stackRecords,Frame.records]
    | right depth entry left stack =>
      simp only [program,Instruction.nav.injEq] at instruction
      obtain ⟨rfl,rfl⟩ := instruction
      simp [State.records,stackRecords,Frame.records]
    | up result frame stack =>
      cases frame with
      | left depth entry rightEmpty =>
        simp only [program,Instruction.nav.injEq] at instruction
        obtain ⟨rfl,rfl⟩ := instruction
        rw [afterLeft_records]
        simp only [State.records,Frame.records,Option.toList_none,List.length_nil,Nat.add_zero]
        omega
      | right entry leftSnapshot =>
        simp only [program,Instruction.nav.injEq] at instruction
        obtain ⟨rfl,rfl⟩ := instruction
        rw [finish_records,node_records]
        simp only [State.records,Frame.records,Option.toList_none,List.length_nil,Nat.add_zero]
        omega
  | write instruction =>
    cases state with
    | read depth stack => cases depth <;> simp [program] at instruction
    | left | right | done => simp [program] at instruction
    | up result frame stack => cases frame <;> simp [program] at instruction
  | writeSize instruction =>
    cases state with
    | read depth stack => cases depth <;> simp [program] at instruction
    | left | right | done => simp [program] at instruction
    | up result frame stack => cases frame <;> simp [program] at instruction

theorem prefix_records {state last : State α ρ} {before after : Metadata.Cursor α (fun _ => ρ)} {reads cost}
    (run : Steps program state before last after reads cost) : last.records = state.records+reads.length := by
  induction run with
  | nil => simp
  | next first rest ih =>
    rw [ih,step_records first,List.length_append]
    omega

theorem working_records (tree : RawTree (Record α ρ)) (nonempty : tree ≠ .empty)
    (outside : List (Pointer.Frame (Record α ρ))) {state : State α ρ} {cursor reads cost}
    (run : Steps program (.read 3 []) ⟨tree,outside⟩ state cursor reads cost) : state.records ≤ 15 := by
  obtain ⟨total,bound,full⟩ := four_levels tree nonempty outside
  obtain ⟨tailReads,tailCost,tailRun,readEq,costEq⟩ := run.agrees_run full
  have size := records_bound 4 tree
  rw [readEq,List.length_append] at size
  have exactCount := prefix_records run
  change state.records = 0+reads.length at exactCount
  norm_num at size
  omega

end DynamicOptimality.LocalSnapshot
