import ChaCha.Paper20261030.ImmutableSourceProgram
import ChaCha.Paper20261030.SourceRecordPredicate

/-! Relational invariants between an immutable vertex identifier and its
mutable payload. Read, move, and write obligations for the source control
state imply preservation at every step of the actual identifier-retaining
compiler, including its intermediate read-before-write state.
-/

namespace ChaCha.Paper20261030.ImmutableSourceRecordInvariant

open ColoredStorage SourcePointer SourceLocalProgram ImmutableSource

variable {α ρ ι σ : Type*}

structure Rules (source : Program σ ρ) (predicate : (ι × ρ) → Prop) (valid : σ → ι → Prop) : Prop where
  read : ∀ state next, source state = .read next → ∀ id payload leaf,
    valid state id → predicate (id,payload) → valid (next payload leaf) id
  navigation : ∀ state action next, source state = .nav action next → ∀ oldId newId,
    valid state oldId → valid next newId
  write : ∀ state fresh next, source state = .write fresh next → ∀ id,
    valid state id → predicate (id,fresh) ∧ valid next id

def Valid (predicate : (ι × ρ) → Prop) (valid : σ → ι → Prop)
    (state : ImmutableSource.State σ ρ ι) (current : Cursor α (ι × ρ)) : Prop :=
  match state with
  | .ready state => valid state current.focus.rootRecord.1
  | .writing id fresh next => id = current.focus.rootRecord.1 ∧ predicate (id,fresh) ∧ valid next id

theorem read_valid (source : Program σ ρ) (predicate : (ι × ρ) → Prop) (valid : σ → ι → Prop)
    (rules : Rules source predicate valid) (state : ImmutableSource.State σ ρ ι)
    (next : (ι × ρ) → Bool → ImmutableSource.State σ ρ ι)
    (instruction : ImmutableSource.program source state = .read next)
    (current : Cursor α (ι × ρ)) (stateValid : Valid predicate valid state current)
    (recordValid : predicate current.focus.rootRecord) :
    Valid predicate valid (next current.focus.rootRecord (isLeaf current.focus)) current := by
  cases state with
  | writing => simp only [ImmutableSource.program,reduceCtorEq] at instruction
  | ready state =>
    cases code : source state with
    | halt | nav => simp only [ImmutableSource.program,code,reduceCtorEq] at instruction
    | read reader =>
      simp only [ImmutableSource.program,code,Instruction.read.injEq] at instruction
      cases instruction
      exact rules.read state reader code _ _ _ stateValid recordValid
    | write fresh after =>
      simp only [ImmutableSource.program,code,Instruction.read.injEq] at instruction
      cases instruction
      exact ⟨rfl,rules.write state fresh after code _ stateValid⟩

theorem nav_valid (source : Program σ ρ) (predicate : (ι × ρ) → Prop) (valid : σ → ι → Prop)
    (rules : Rules source predicate valid) (state next : ImmutableSource.State σ ρ ι) (action)
    (instruction : ImmutableSource.program source state = .nav action next)
    (before after : Cursor α (ι × ρ)) (stateValid : Valid predicate valid state before) :
    Valid predicate valid next after := by
  cases state with
  | writing => simp only [ImmutableSource.program,reduceCtorEq] at instruction
  | ready state =>
    cases code : source state with
    | halt | read | write => simp only [ImmutableSource.program,code,reduceCtorEq] at instruction
    | nav move following =>
      simp only [ImmutableSource.program,code,Instruction.nav.injEq] at instruction
      rcases instruction with ⟨rfl,rfl⟩
      exact rules.navigation state move following code _ _ stateValid

theorem step (source : Program σ ρ) (predicate : (ι × ρ) → Prop) (valid : σ → ι → Prop)
    (rules : Rules source predicate valid) {state next : ImmutableSource.State σ ρ ι}
    {before after : Cursor α (ι × ρ)} {entry}
    (actual : Step (ImmutableSource.program source) state before next after entry)
    (stateValid : Valid predicate valid state before)
    (treeValid : SourceRecordPredicate.Holds predicate before.tree) :
    Valid predicate valid next after ∧ SourceRecordPredicate.Holds predicate after.tree := by
  cases actual with
  | read instruction =>
    exact ⟨read_valid source predicate valid rules state _ instruction before stateValid
      (SourceRecordPredicate.focused predicate before treeValid),treeValid⟩
  | nav instruction moved =>
    exact ⟨nav_valid source predicate valid rules state next _ instruction before after stateValid,
      SourceRecordPredicate.navigation predicate _ before after moved treeValid⟩
  | write instruction =>
    cases state with
    | ready state => cases code : source state <;> simp_all only [ImmutableSource.program,reduceCtorEq]
    | writing id fresh following =>
      simp only [ImmutableSource.program,Instruction.write.injEq] at instruction
      rcases instruction with ⟨rfl,rfl⟩
      refine ⟨?_,SourceRecordPredicate.write predicate before (id,fresh) treeValid stateValid.2.1⟩
      change valid following (before.focus.setRoot (id,fresh)).rootRecord.1
      cases before.focus <;> exact stateValid.2.2

theorem run (source : Program σ ρ) (predicate : (ι × ρ) → Prop) (valid : σ → ι → Prop)
    (rules : Rules source predicate valid) {state next : ImmutableSource.State σ ρ ι}
    {before after : Cursor α (ι × ρ)} {reads cost}
    (actual : Run (ImmutableSource.program source) state before next after reads cost)
    (stateValid : Valid predicate valid state before)
    (treeValid : SourceRecordPredicate.Holds predicate before.tree) :
    Valid predicate valid next after ∧ SourceRecordPredicate.Holds predicate after.tree := by
  induction actual with
  | halt => exact ⟨stateValid,treeValid⟩
  | next first rest ih =>
    obtain ⟨nextValid,nextTree⟩ := step source predicate valid rules first stateValid treeValid
    exact ih nextValid nextTree

end ChaCha.Paper20261030.ImmutableSourceRecordInvariant
