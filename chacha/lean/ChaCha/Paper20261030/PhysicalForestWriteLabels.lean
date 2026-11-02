import ChaCha.Paper20261030.PhysicalPrimitiveWriteLabels
import ChaCha.Paper20261030.PhysicalForestCompiler

set_option autoImplicit false

/-! The existing physical forest compiler with the additional guarantee
that each individual write preserves its reached vertex's physical id.
The controller and cost are unchanged; the stronger checked execution
composes the physical primitives' existing write-stability proofs. -/

namespace ChaCha.Paper20261030.PhysicalForestCompiler

open ColoredStorage SourcePointer ForestLocalProgram PhysicalForestMetadata

variable {α ρ ι C σ : Type*} [DecidableEq ι] [DecidableEq C]

theorem operation_label_steps (source : Program σ C ρ) (state next : σ) (q : C) (operation : Operation ρ)
    (instruction : program (ι := ι) source (.ready state) =
      (operationProgram q operation operationInitial).mapState (finish q operation next))
    (forest : TaggedForest C α ρ ι) (current : Cursor α (Payload ρ ι))
    (present : forest q = some current) (unique : Unique forest)
    (after : Cursor α (List ρ)) (effect : Effect operation (current.mapRecords Prod.snd) after) :
    ∃ target reads cost,
      ForestWriteLabels.Steps (fun record => record.1.1) (program source) (.ready state) (encode forest) (.ready next)
        (encode (Function.update forest q (some target))) reads cost ∧
      target.mapRecords Prod.snd = after ∧ Unique (Function.update forest q (some target)) ∧ cost ≤ 38 := by
  obtain ⟨target,reads,cost,run,erases,_,targetUnique,bounded⟩ :=
    PhysicalForestMetadata.execute_write_labels q operation forest current present unique after effect
  have positive : 0 < cost := by cases run with
    | next => omega
  have actual := run.map_prefix (finish q operation next) (operation_code source q operation next)
  refine ⟨target,reads,cost,actual.change_start positive ?_,erases,targetUnique,bounded⟩
  exact instruction

theorem label_step (source : Program σ C ρ) {state next : σ} {before after : ProjectionForest.State C α ρ} {entry}
    (execution : Step source state before next after entry)
    (forest : TaggedForest C α ρ ι) (erases : erase forest = before) (unique : Unique forest) :
    ∃ target reads cost,
      ForestWriteLabels.Steps (fun record => record.1.1) (program source) (.ready state) (encode forest) (.ready next) (encode target) reads cost ∧
      erase target = after ∧ Unique target ∧ cost ≤ 38 := by
  cases execution with
  | readNone instruction absent =>
    rename_i nextRead q
    have absentTagged : forest q = none := by
      have empty : erase forest q = none := erases ▸ absent
      cases location : forest q with
      | none => rfl
      | some current => simp only [erase,location,Option.map_some,reduceCtorEq] at empty
    have atCursor : encode forest q = none := by simp only [encode,absentTagged,Option.map_none]
    have actual := Step.readNone (program := program source) (state := .ready state)
      (next := readNext nextRead) (by simp only [program,instruction]) atCursor
    exact ⟨forest,[],1,(ForestWriteLabels.step_prefix actual (by simp only [program,instruction,ForestWriteLabels.Stable])),erases,unique,by decide⟩
  | readSome instruction present =>
    rename_i nextRead q bare
    obtain ⟨current,location,currentErases⟩ := present_of_erased forest q bare (erases ▸ present)
    have atCursor : encode forest q = some (encodeCursor current) := by
      simp only [encode,location,Option.map_some]
    have actual := Step.readSome (program := program source) (state := .ready state)
      (next := readNext nextRead) (by simp only [program,instruction]) atCursor
    refine ⟨forest,[(q,(encodeCursor current).focus.rootRecord)],1,?_,erases,unique,by decide⟩
    simpa only [← currentErases,encodeCursor,SourceForestLift.packet,Structural.cursor,Cursor.mapRecords,
      Source.mapRecords_root,Structural.annotate_root,Structural.Compiler.isLeaf_annotate,isLeaf_mapRecords,
      readNext,Option.toList_some] using (ForestWriteLabels.step_prefix actual (by simp only [program,instruction,ForestWriteLabels.Stable]))
  | nav instruction present moved =>
    rename_i q bare fresh action
    obtain ⟨current,location,currentErases⟩ := present_of_erased forest q bare (erases ▸ present)
    obtain ⟨target,reads,cost,actual,targetErases,targetUnique,bounded⟩ :=
      operation_label_steps source state next q (.nav action) (by simp only [program,instruction])
        forest current location unique fresh (currentErases ▸ moved)
    exact ⟨Function.update forest q (some target),reads,cost,actual,
      by rw [erase_update,targetErases,erases],targetUnique,bounded⟩
  | write instruction present =>
    rename_i q bare records
    obtain ⟨current,location,currentErases⟩ := present_of_erased forest q bare (erases ▸ present)
    obtain ⟨target,reads,cost,actual,targetErases,targetUnique,bounded⟩ :=
      operation_label_steps source state next q (.write records) (by simp only [program,instruction])
        forest current location unique ⟨bare.focus.setRoot records,bare.ancestors⟩ (by
          change _ = _; rw [currentErases])
    exact ⟨Function.update forest q (some target),reads,cost,actual,
      by rw [erase_update,targetErases,erases],targetUnique,bounded⟩

theorem compile_write_labels (source : Program σ C ρ) {state last : σ} {before after : ProjectionForest.State C α ρ}
    {reads cost} (execution : Run source state before last after reads cost)
    (forest : TaggedForest C α ρ ι) (erases : erase forest = before) (unique : Unique forest) :
    ∃ target observations actualCost,
      ForestWriteLabels.Run (fun record => record.1.1) (program source) (.ready state) (encode forest) (.ready last) (encode target) observations actualCost ∧
      erase target = after ∧ Unique target ∧ actualCost ≤ 38*cost := by
  induction execution generalizing forest with
  | halt stopped => exact ⟨forest,[],0,.halt (by simp only [program,stopped]),erases,unique,by omega⟩
  | next first rest ih =>
    obtain ⟨middle,firstReads,firstCost,firstRun,middleErases,middleUnique,firstBound⟩ :=
      label_step source first forest erases unique
    obtain ⟨target,lastReads,lastCost,lastRun,targetErases,targetUnique,lastBound⟩ :=
      ih middle middleErases middleUnique
    exact ⟨target,firstReads++lastReads,firstCost+lastCost,firstRun.then_run lastRun,
      targetErases,targetUnique,by omega⟩

end ChaCha.Paper20261030.PhysicalForestCompiler
