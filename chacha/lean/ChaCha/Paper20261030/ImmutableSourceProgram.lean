import ChaCha.Paper20261030.SourceProgramRecordMap

/-! Immutable vertex identifiers are structural metadata, separate from
the application payload, as in the manuscript's local simulation lemma.
A payload write first reads the reached identifier and then keeps it.
This costs at most two instructions and makes the complete identifier
inventory invariant, including inside helper routines.
-/

namespace ChaCha.Paper20261030.ImmutableSource

open ColoredStorage SourcePointer SourceLocalProgram

variable {α ρ ι σ : Type*}

inductive State (σ ρ ι : Type*) where
  | ready (state : σ)
  | writing (id : ι) (fresh : ρ) (next : σ)

def program (source : Program σ ρ) : Program (State σ ρ ι) (ι × ρ)
  | .ready state => match source state with
    | .halt => .halt
    | .read next => .read (fun record leaf => .ready (next record.2 leaf))
    | .nav action next => .nav action (.ready next)
    | .write fresh next => .read (fun record _ => .writing record.1 fresh next)
  | .writing id fresh next => .write (id,fresh) (.ready next)

def Valid (state : State σ ρ ι) (current : Cursor α (ι × ρ)) : Prop :=
  match state with
  | .ready _ => True
  | .writing id _ _ => id = current.focus.rootRecord.1

theorem read_valid (source : Program σ ρ) (state : State σ ρ ι) (next : (ι × ρ) → Bool → State σ ρ ι)
    (instruction : program source state = .read next) (current : Cursor α (ι × ρ)) :
    Valid (next current.focus.rootRecord (isLeaf current.focus)) current := by
  cases state with
  | writing => simp only [program,reduceCtorEq] at instruction
  | ready state =>
    cases h : source state <;> simp_all [program,Valid]
    all_goals (rw [← instruction] <;> trivial)

theorem nav_valid (source : Program σ ρ) (state next : State σ ρ ι) (action)
    (instruction : program source state = .nav action next) (current : Cursor α (ι × ρ)) :
    Valid next current := by
  cases state with
  | writing => simp only [program,reduceCtorEq] at instruction
  | ready state =>
    cases h : source state <;> simp_all [program,Valid]
    rw [← instruction.2]
    trivial

theorem step_invariant {source : Program σ ρ} {state next : State σ ρ ι}
    {before after : Cursor α (ι × ρ)} {entry}
    (step : SourceLocalProgram.Step (program source) state before next after entry) (valid : Valid state before) :
    Valid next after ∧ before.tree.inventory Prod.fst = after.tree.inventory Prod.fst := by
  cases step with
  | read instruction => exact ⟨read_valid source state _ instruction before,rfl⟩
  | nav instruction moved => exact ⟨nav_valid source state next _ instruction after,navigate_inventory Prod.fst _ moved⟩
  | write instruction =>
    cases state with
    | ready state => cases h : source state <;> simp_all [program]
    | writing id fresh next =>
      simp only [program,Instruction.write.injEq] at instruction
      obtain ⟨rfl,rfl⟩ := instruction
      exact ⟨trivial,plug_inventory_congr Prod.fst
        (Source.inventory_setRoot Prod.fst before.focus (id,fresh) valid).symm before.ancestors⟩

theorem steps_invariant {source : Program σ ρ} {state next : State σ ρ ι}
    {before after : Cursor α (ι × ρ)} {reads cost}
    (steps : Steps (program source) state before next after reads cost) (valid : Valid state before) :
    Valid next after ∧ before.tree.inventory Prod.fst = after.tree.inventory Prod.fst := by
  induction steps with
  | nil => exact ⟨valid,rfl⟩
  | next first rest ih =>
    obtain ⟨middleValid,firstInventory⟩ := step_invariant first valid
    obtain ⟨lastValid,lastInventory⟩ := ih middleValid
    exact ⟨lastValid,firstInventory.trans lastInventory⟩

theorem run_invariant {source : Program σ ρ} {state next : State σ ρ ι}
    {before after : Cursor α (ι × ρ)} {reads cost}
    (run : Run (program source) state before next after reads cost) (valid : Valid state before) :
    Valid next after ∧ before.tree.inventory Prod.fst = after.tree.inventory Prod.fst := by
  induction run with
  | halt => exact ⟨valid,rfl⟩
  | next first rest ih =>
    obtain ⟨middleValid,firstInventory⟩ := step_invariant first valid
    obtain ⟨lastValid,lastInventory⟩ := ih middleValid
    exact ⟨lastValid,firstInventory.trans lastInventory⟩

theorem step (source : Program σ ρ) {state next : σ} {before after : Cursor α ρ} {entry}
    (execution : SourceLocalProgram.Step source state before next after entry)
    (decorated : Cursor α (ι × ρ)) (erases : decorated.mapRecords Prod.snd = before) :
    ∃ target reads cost,
      Steps (program source) (.ready state) decorated (.ready next) target reads cost ∧
      target.mapRecords Prod.snd = after ∧ cost ≤ 2 := by
  cases execution with
  | read instruction =>
    rename_i nextRead
    have actual : SourceLocalProgram.Step (program source) (.ready state) decorated
        (.ready (nextRead decorated.focus.rootRecord.2 (isLeaf decorated.focus))) decorated
        (some decorated.focus.rootRecord) := by
      apply SourceLocalProgram.Step.read (program := program source)
        (next := fun (record : ι × ρ) leaf => State.ready (nextRead record.2 leaf))
      simp only [program,instruction]
    refine ⟨decorated,[decorated.focus.rootRecord],1,?_,erases,by decide⟩
    simpa only [← erases,Cursor.mapRecords,Source.mapRecords_root,isLeaf_mapRecords,Option.toList_some] using actual.prefix
  | nav instruction moved =>
    rename_i action
    obtain ⟨target,actualMove,targetErases⟩ := lift_navigation Prod.snd action decorated after (erases ▸ moved)
    have actual : SourceLocalProgram.Step (program source) (.ready state) decorated (.ready next) target none :=
      .nav (by simp only [program,instruction]) actualMove
    exact ⟨target,[],1,actual.prefix,targetErases,by decide⟩
  | write instruction =>
    rename_i fresh
    let target : Cursor α (ι × ρ) :=
      ⟨decorated.focus.setRoot (decorated.focus.rootRecord.1,fresh),decorated.ancestors⟩
    have read : SourceLocalProgram.Step (program source) (.ready state) decorated
        (.writing decorated.focus.rootRecord.1 fresh next) decorated (some decorated.focus.rootRecord) :=
      by
        apply SourceLocalProgram.Step.read (program := program source)
          (next := fun (record : ι × ρ) _ => State.writing record.1 fresh next)
        simp only [program,instruction]
    have write : SourceLocalProgram.Step (program source) (.writing decorated.focus.rootRecord.1 fresh next)
        decorated (.ready next) target none := .write rfl
    refine ⟨target,[decorated.focus.rootRecord],2,?_,?_,le_rfl⟩
    · simpa only [Option.toList_some,Option.toList_none,List.append_nil] using read.prefix.append write.prefix
    · simp only [← erases,target,Cursor.mapRecords,Source.mapRecords_setRoot]

theorem compile_steps (source : Program σ ρ) {state next : σ} {before after : Cursor α ρ} {reads cost}
    (steps : Steps source state before next after reads cost)
    (decorated : Cursor α (ι × ρ)) (erases : decorated.mapRecords Prod.snd = before) :
    ∃ target actualReads actualCost,
      Steps (program source) (.ready state) decorated (.ready next) target actualReads actualCost ∧
      target.mapRecords Prod.snd = after ∧ actualCost ≤ 2*cost := by
  induction steps generalizing decorated with
  | nil => exact ⟨decorated,[],0,.nil _ _,erases,by omega⟩
  | next first rest ih =>
    obtain ⟨middle,firstReads,firstCost,compiled,middleErases,firstBound⟩ := step source first decorated erases
    obtain ⟨target,lastReads,lastCost,tail,lastErases,lastBound⟩ := ih middle middleErases
    exact ⟨target,_,_,compiled.append tail,lastErases,by omega⟩

theorem compile_run (source : Program σ ρ) {state next : σ} {before after : Cursor α ρ} {reads cost}
    (run : Run source state before next after reads cost)
    (decorated : Cursor α (ι × ρ)) (erases : decorated.mapRecords Prod.snd = before) :
    ∃ target actualReads actualCost,
      Run (program source) (.ready state) decorated (.ready next) target actualReads actualCost ∧
      target.mapRecords Prod.snd = after ∧ actualCost ≤ 2*cost := by
  induction run generalizing decorated with
  | halt stopped => exact ⟨decorated,[],0,.halt (by simp only [program,stopped]),erases,by omega⟩
  | next first rest ih =>
    obtain ⟨middle,firstReads,firstCost,compiled,middleErases,firstBound⟩ := step source first decorated erases
    obtain ⟨target,lastReads,lastCost,tail,lastErases,lastBound⟩ := ih middle middleErases
    exact ⟨target,_,_,compiled.then_run tail,lastErases,by omega⟩

theorem compile_leaf_read (source : Program σ ρ) {initial : σ} {before : Cursor α ρ} {key : α}
    (reaches : ReachesLeafRead source initial before key)
    (decorated : Cursor α (ι × ρ)) (erases : decorated.mapRecords Prod.snd = before) :
    ReachesLeafRead (program source) (.ready initial) decorated key := by
  obtain ⟨state,atLeaf,record,reads,cost,next,steps,focus,instruction⟩ := reaches
  obtain ⟨target,actualReads,actualCost,compiled,targetErases,bounded⟩ := compile_steps source steps decorated erases
  have erasedFocus : target.focus.mapRecords Prod.snd = .leaf key record := by
    rw [← focus]
    exact congrArg Cursor.focus targetErases
  have leaf : ∃ entry, target.focus = .leaf key entry := by
    cases shape : target.focus with
    | leaf label entry =>
      simp only [shape,Source.mapRecords,Source.leaf.injEq] at erasedFocus
      exact ⟨entry,by rw [erasedFocus.1]⟩
    | fork => simp only [shape,Source.mapRecords,reduceCtorEq] at erasedFocus
  obtain ⟨entry,leaf⟩ := leaf
  exact ⟨.ready state,target,entry,actualReads,actualCost,(fun record leaf => .ready (next record.2 leaf)),
    compiled,leaf,by simp only [program,instruction]⟩

end ChaCha.Paper20261030.ImmutableSource
