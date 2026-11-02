import ChaCha.Paper20261030.PackedSourceNavigation

/-! Correctness of the executable color-forest compiler for every
source execution with instruction-by-instruction metadata readiness.
Logical and physical identifier uniqueness are required only initially.
The structural compiler's discharge of readiness is a separate obligation.
-/

namespace ChaCha.Paper20261030.PackedSourceCompiler

open ColoredStorage SourcePointer ForestLocalProgram Structural PhysicalForestMetadata

variable {α ρ ι η C σ : Type*} [DecidableEq α] [DecidableEq ι] [DecidableEq η] [LinearOrder C] [Fintype C]

theorem step (identifier : ρ → η) (color : α → C)
    (source : SourceLocalProgram.Program σ (LogicalRecord ρ η C)) {state next : σ}
    {before after : Cursor α (LogicalRecord ρ η C)} {entry}
    (execution : SourceLocalProgram.Step source state before next after entry)
    (ready : PackedReadiness.Ready identifier color (source state) before)
    (forest : TaggedForest C α (LogicalRecord ρ η C) ι)
    (represented : ProjectionForest.Represents color before (erase forest))
    (physicalUnique : Unique forest)
    (logicalUnique : (before.tree.inventory (fun (record : LogicalRecord ρ η C) => identifier record.1)).Nodup) :
    ∃ target reads cost,
      Steps (program identifier source) (.ready state (identifier before.focus.rootRecord.1)) (encode forest)
        (.ready next (identifier after.focus.rootRecord.1)) (encode target) reads cost ∧
      ProjectionForest.Represents color after (erase target) ∧
      Unique target ∧ cost ≤ 780*(Fintype.card C+1) := by
  cases execution with
  | nav instruction moved =>
    exact nav_steps identifier color source state next _ instruction before after moved ready forest represented physicalUnique logicalUnique
  | read instruction =>
    obtain ⟨reads,cost,actual,bounded⟩ := PhysicalRecordFinder.find_current
      (fun (record : LogicalRecord ρ η C) => identifier record.1) color before forest represented physicalUnique
      (Multiset.inj_on_of_nodup_map logicalUnique)
    have positive : 0 < cost := by cases actual with | next => omega
    let wanted := identifier before.focus.rootRecord.1
    have mapped := actual.map_prefix (finishRead identifier source state wanted) (read_code identifier source state wanted)
    have changed := mapped.change_start (replacement := .ready state wanted) positive (by
      simp only [program,instruction,finishRead])
    have leaf : before.focus.rootRecord.2.children.isNone = SourceLocalProgram.isLeaf before.focus := by
      simpa only [instruction,PackedReadiness.Ready] using ready
    refine ⟨forest,reads,cost,?_,represented,physicalUnique,by omega⟩
    simpa only [finishRead,instruction,leaf] using changed
  | write instruction =>
    rename_i fresh
    have same : identifier fresh.1 = identifier before.focus.rootRecord.1 := by
      simpa only [instruction,PackedReadiness.Ready] using ready
    obtain ⟨target,reads,cost,actual,targetRep,targetUnique,_,bounded⟩ :=
      PhysicalPackedWriteController.write (fun (record : LogicalRecord ρ η C) => identifier record.1) color before fresh same forest represented physicalUnique logicalUnique
    have positive : 0 < cost := by cases actual with | next => omega
    let wanted := identifier before.focus.rootRecord.1
    have mapped := actual.map_prefix (finishWrite next wanted fresh) (write_code identifier source next wanted fresh)
    have changed := mapped.change_start (replacement := .ready state wanted) positive (by
      simp only [program,instruction,finishWrite])
    refine ⟨target,reads,cost,?_,targetRep,targetUnique,by omega⟩
    have root : (before.focus.setRoot fresh).rootRecord = fresh := by cases before.focus <;> rfl
    simpa only [root,same,finishWrite,wanted] using changed

theorem compile_run (identifier : ρ → η) (color : α → C)
    (source : SourceLocalProgram.Program σ (LogicalRecord ρ η C)) {state last : σ}
    {before after : Cursor α (LogicalRecord ρ η C)} {readWord sourceCost}
    (execution : PackedReadiness.CheckedRun identifier color source state before last after readWord sourceCost)
    (forest : TaggedForest C α (LogicalRecord ρ η C) ι)
    (represented : ProjectionForest.Represents color before (erase forest))
    (physicalUnique : Unique forest)
    (logicalUnique : (before.tree.inventory (fun (record : LogicalRecord ρ η C) => identifier record.1)).Nodup) :
    ∃ target reads cost,
      Run (program identifier source) (.ready state (identifier before.focus.rootRecord.1)) (encode forest)
        (.ready last (identifier after.focus.rootRecord.1)) (encode target) reads cost ∧
      ProjectionForest.Represents color after (erase target) ∧
      Unique target ∧ cost ≤ (780*(Fintype.card C+1))*sourceCost := by
  induction execution generalizing forest with
  | halt stopped =>
    exact ⟨forest,[],0,.halt (by simp only [program,stopped]),represented,physicalUnique,by omega⟩
  | next first ready rest ih =>
    obtain ⟨middle,firstReads,firstCost,firstRun,middleRep,middleUnique,firstBound⟩ :=
      step identifier color source first ready forest represented physicalUnique logicalUnique
    have middleLogical := logicalUnique
    rw [PackedReadiness.step_inventory identifier color first ready] at middleLogical
    obtain ⟨target,lastReads,lastCost,lastRun,targetRep,targetUnique,lastBound⟩ :=
      ih middle middleRep middleUnique middleLogical
    refine ⟨target,firstReads++lastReads,firstCost+lastCost,firstRun.then_run lastRun,targetRep,targetUnique,?_⟩
    rw [Nat.mul_add]
    omega

end ChaCha.Paper20261030.PackedSourceCompiler
