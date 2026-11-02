import ChaCha.Paper20261030.ForestWriteLabels
import ChaCha.Paper20261030.VirtualHeaderCompiler

set_option autoImplicit false

/-! Replacing the virtual projection by a header retains physical-id
labels on real records. All header records receive the neutral label,
so virtual operations cannot change a physical id. -/

namespace ChaCha.Paper20261030.VirtualHeaderController

open ColoredStorage SourcePointer ForestLocalProgram

variable {α ρ ι C σ : Type*} [DecidableEq C]

def physicalLabel (label : ρ → ι) : Datum α ρ → Option ι
  | .real record => some (label record)
  | .header _ => none

theorem stable_ready (label : ρ → ι) (virtualColor : C) (source : Program σ C ρ)
    (key : α) (state : σ) (forest : ProjectionForest.State C α ρ)
    (safe : ForestWriteLabels.Stable label (source state) forest) :
    ForestWriteLabels.Stable (physicalLabel label) (program virtualColor source (.ready state))
      (encode virtualColor key forest) := by
  cases code : source state with
  | halt | read => simp only [program,code,ForestWriteLabels.Stable]
  | nav q action next => by_cases virtual : q = virtualColor <;>
      simp only [program,code,virtual,if_true,if_false,ForestWriteLabels.Stable]
  | write q fresh next =>
    by_cases virtual : q = virtualColor
    · simp only [program,code,virtual,if_true,ForestWriteLabels.Stable]
    · simp only [program,code,virtual,if_false,ForestWriteLabels.Stable]
      intro current present
      cases location : forest q with
      | none => simp only [encode,virtual,if_false,location,Option.map_none,reduceCtorEq] at present
      | some original =>
        have equal : original.mapRecords (List.map Datum.real) = current := by
          simpa only [encode,virtual,if_false,location,Option.map_some,Option.some.injEq] using present
        have checked := safe
        simp only [code,ForestWriteLabels.Stable] at checked
        have same := checked original location
        rw [← equal]
        simp only [Cursor.mapRecords,Source.mapRecords_root,List.map_map,physicalLabel]
        simpa only [List.map_map,Function.comp_def,physicalLabel] using congrArg (List.map some) same

theorem commit_labels (label : ρ → ι) (virtualColor : C) (source : Program σ C ρ)
    (key : α) (forest : ProjectionForest.State C α ρ) (next : σ) (current : Virtual α ρ) :
    ForestWriteLabels.Steps (physicalLabel label) (program virtualColor source)
      (.commit next current) (encode virtualColor key forest) (.ready next)
      (encode virtualColor key (Function.update forest virtualColor current)) [] 1 := by
  rw [encode_update_virtual]
  have present : encode virtualColor key forest virtualColor =
      some ⟨.leaf key [.header (forest virtualColor)],[]⟩ := by simp [encode]
  apply ForestWriteLabels.step_prefix (Step.write (program := program virtualColor source)
    (fresh := [.header current]) rfl present)
  intro actual located
  have equal := Option.some.inj (located.symm.trans present)
  subst actual
  rfl

theorem virtual_steps_labels (label : ρ → ι) (virtualColor : C) (source : Program σ C ρ) (key : α)
    (state next : σ) (operation : Operation ρ) (forest : ProjectionForest.State C α ρ)
    (target : Cursor α (List ρ))
    (instruction : program (α := α) virtualColor source (.ready state) = .read virtualColor (virtualAction operation next))
    (changed : effect operation (forest virtualColor) = some target) :
    ForestWriteLabels.Steps (physicalLabel label) (program virtualColor source) (.ready state) (encode virtualColor key forest)
      (.ready next) (encode virtualColor key (Function.update forest virtualColor (some target)))
      [(virtualColor,[.header (forest virtualColor)])] 2 := by
  have actual := Step.readSome (program := program virtualColor source) (state := .ready state)
    (next := virtualAction operation next) instruction
    (show encode virtualColor key forest virtualColor = some ⟨.leaf key [.header (forest virtualColor)],[]⟩ by simp [encode])
  have first : ForestWriteLabels.Steps (physicalLabel label) (program virtualColor source) (.ready state) (encode virtualColor key forest)
      (.commit next (some target)) (encode virtualColor key forest) [(virtualColor,[.header (forest virtualColor)])] 1 := by
    simpa only [Source.rootRecord,SourceLocalProgram.isLeaf,virtualAction,changed,Option.toList_some] using (ForestWriteLabels.step_prefix actual (by rw [instruction]; trivial))
  simpa only [List.append_nil] using first.append (commit_labels label virtualColor source key forest next (some target))

theorem step_labels (label : ρ → ι) (virtualColor : C) (source : Program σ C ρ) (key : α) {state next : σ}
    {before after : ProjectionForest.State C α ρ} {entry}
    (execution : Step source state before next after entry)
    (safe : ForestWriteLabels.Stable label (source state) before) :
    ∃ reads cost, ForestWriteLabels.Steps (physicalLabel label) (program virtualColor source) (.ready state) (encode virtualColor key before)
      (.ready next) (encode virtualColor key after) reads cost ∧ cost ≤ 2 := by
  cases execution with
  | readNone instruction absent =>
    rename_i nextRead q
    by_cases virtual : q = virtualColor
    · subst q
      have actual := Step.readSome (program := program virtualColor source) (state := .ready state)
        (next := virtualRead nextRead) (by simp only [program,instruction,ite_true])
        (show encode virtualColor key before virtualColor = some ⟨.leaf key [.header (before virtualColor)],[]⟩ by simp [encode])
      refine ⟨[(virtualColor,[.header (before virtualColor)])],1,?_,by decide⟩
      simpa only [Source.rootRecord,SourceLocalProgram.isLeaf,virtualRead,view,absent,Option.map_none,Option.toList_some] using (ForestWriteLabels.step_prefix actual (stable_ready label virtualColor source key state before safe))
    · have actual : Step (program virtualColor source) (.ready state) (encode virtualColor key before)
          (.ready (nextRead none)) (encode virtualColor key before) none :=
        .readNone (q := q) (next := realRead nextRead) (by simp only [program,instruction,virtual,if_false])
          (by simp only [encode,virtual,if_false,absent,Option.map_none])
      exact ⟨[],1,(ForestWriteLabels.step_prefix actual (stable_ready label virtualColor source key state before safe)),by decide⟩
  | readSome instruction present =>
    rename_i nextRead q current
    by_cases virtual : q = virtualColor
    · subst q
      have actual := Step.readSome (program := program virtualColor source) (state := .ready state)
        (next := virtualRead nextRead) (by simp only [program,instruction,ite_true])
        (show encode virtualColor key before virtualColor = some ⟨.leaf key [.header (before virtualColor)],[]⟩ by simp [encode])
      refine ⟨[(virtualColor,[.header (before virtualColor)])],1,?_,by decide⟩
      simpa only [Source.rootRecord,SourceLocalProgram.isLeaf,virtualRead,view,present,Option.map_some,Option.toList_some] using (ForestWriteLabels.step_prefix actual (stable_ready label virtualColor source key state before safe))
    · have actual := Step.readSome (program := program virtualColor source) (state := .ready state)
        (next := realRead nextRead) (by simp only [program,instruction,virtual,if_false])
        (show encode virtualColor key before q = some (current.mapRecords (List.map Datum.real)) by
          simp only [encode,virtual,if_false,present,Option.map_some])
      refine ⟨[(q,current.focus.rootRecord.map Datum.real)],1,?_,by decide⟩
      simpa only [Cursor.mapRecords,Source.mapRecords_root,isLeaf_mapRecords,realRead,Option.map_some,payload_map,Option.toList_some] using (ForestWriteLabels.step_prefix actual (stable_ready label virtualColor source key state before safe))
  | nav instruction present moved =>
    rename_i q current target action
    by_cases virtual : q = virtualColor
    · subst q
      refine ⟨_,2,virtual_steps_labels label virtualColor source key state next (.nav action) before target ?_ ?_,le_rfl⟩
      · simp only [program,instruction,ite_true]
      · simp only [effect,present,Option.bind_some,moved]
    · rw [encode_update_real virtualColor q virtual]
      have navigation : SourceLocalProgram.navigate action (current.mapRecords (List.map (Datum.real (α := α)))) =
          some (target.mapRecords (List.map Datum.real)) := by
        rw [← navigate_mapRecords,moved]
        rfl
      have actual : Step (program virtualColor source) (.ready state) (encode virtualColor key before)
          (.ready next) (Function.update (encode virtualColor key before) q (some (target.mapRecords (List.map Datum.real)))) none :=
        .nav (by simp only [program,instruction,virtual,if_false])
          (by simp only [encode,virtual,if_false,present,Option.map_some]) navigation
      exact ⟨[],1,(ForestWriteLabels.step_prefix actual (stable_ready label virtualColor source key state before safe)),by decide⟩
  | write instruction present =>
    rename_i q current records
    by_cases virtual : q = virtualColor
    · subst q
      refine ⟨_,2,virtual_steps_labels label virtualColor source key state next (.write records) before
        ⟨current.focus.setRoot records,current.ancestors⟩ ?_ ?_,le_rfl⟩
      · simp only [program,instruction,ite_true]
      · simp only [effect,present,Option.bind_some]
    · rw [encode_update_real virtualColor q virtual]
      have actual := Step.write (program := program virtualColor source) (state := .ready state)
        (next := .ready next) (fresh := records.map Datum.real) (by simp only [program,instruction,virtual,if_false])
        (show encode virtualColor key before q = some (current.mapRecords (List.map Datum.real)) by
          simp only [encode,virtual,if_false,present,Option.map_some])
      refine ⟨[],1,?_,by decide⟩
      simpa only [Cursor.mapRecords,Source.mapRecords_setRoot,Option.toList_none] using (ForestWriteLabels.step_prefix actual (stable_ready label virtualColor source key state before safe))

theorem compile_write_labels (label : ρ → ι) (virtualColor : C) (source : Program σ C ρ) (key : α) {state last : σ}
    {before after : ProjectionForest.State C α ρ} {reads cost}
    (execution : ForestWriteLabels.Run label source state before last after reads cost) :
    ∃ actualReads actualCost, ForestWriteLabels.Run (physicalLabel label) (program virtualColor source) (.ready state) (encode virtualColor key before)
      (.ready last) (encode virtualColor key after) actualReads actualCost ∧ actualCost ≤ 2*cost := by
  induction execution with
  | halt stopped => exact ⟨[],0,.halt (by simp only [program,stopped]),by omega⟩
  | next first safe rest ih =>
    obtain ⟨firstReads,firstCost,front,firstBound⟩ := step_labels label virtualColor source key first safe
    obtain ⟨lastReads,lastCost,tail,lastBound⟩ := ih
    exact ⟨_,_,front.then_run tail,by omega⟩

end ChaCha.Paper20261030.VirtualHeaderController
