import ChaCha.Paper20261030.VirtualHeaderProgram

/-! Actual header reads and writes implement the virtual-color forest
operations at factor two. Real routing fingers remain independent.
-/

namespace ChaCha.Paper20261030.VirtualHeaderController

open ColoredStorage SourcePointer ForestLocalProgram

variable {α ρ C σ : Type*} [DecidableEq C]

theorem virtual_steps (virtualColor : C) (source : Program σ C ρ) (key : α)
    (state next : σ) (operation : Operation ρ) (forest : ProjectionForest.State C α ρ)
    (target : Cursor α (List ρ))
    (instruction : program (α := α) virtualColor source (.ready state) = .read virtualColor (virtualAction operation next))
    (changed : effect operation (forest virtualColor) = some target) :
    Steps (program virtualColor source) (.ready state) (encode virtualColor key forest)
      (.ready next) (encode virtualColor key (Function.update forest virtualColor (some target)))
      [(virtualColor,[.header (forest virtualColor)])] 2 := by
  have actual := Step.readSome (program := program virtualColor source) (state := .ready state)
    (next := virtualAction operation next) instruction
    (show encode virtualColor key forest virtualColor = some ⟨.leaf key [.header (forest virtualColor)],[]⟩ by simp [encode])
  have first : Steps (program virtualColor source) (.ready state) (encode virtualColor key forest)
      (.commit next (some target)) (encode virtualColor key forest) [(virtualColor,[.header (forest virtualColor)])] 1 := by
    simpa only [Source.rootRecord,SourceLocalProgram.isLeaf,virtualAction,changed,Option.toList_some] using actual.prefix
  simpa only [List.append_nil] using first.append (commit_run virtualColor source key forest next (some target))

theorem step (virtualColor : C) (source : Program σ C ρ) (key : α) {state next : σ}
    {before after : ProjectionForest.State C α ρ} {entry}
    (execution : Step source state before next after entry) :
    ∃ reads cost, Steps (program virtualColor source) (.ready state) (encode virtualColor key before)
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
      simpa only [Source.rootRecord,SourceLocalProgram.isLeaf,virtualRead,view,absent,Option.map_none,Option.toList_some] using actual.prefix
    · have actual : Step (program virtualColor source) (.ready state) (encode virtualColor key before)
          (.ready (nextRead none)) (encode virtualColor key before) none :=
        .readNone (q := q) (next := realRead nextRead) (by simp only [program,instruction,virtual,if_false])
          (by simp only [encode,virtual,if_false,absent,Option.map_none])
      exact ⟨[],1,actual.prefix,by decide⟩
  | readSome instruction present =>
    rename_i nextRead q current
    by_cases virtual : q = virtualColor
    · subst q
      have actual := Step.readSome (program := program virtualColor source) (state := .ready state)
        (next := virtualRead nextRead) (by simp only [program,instruction,ite_true])
        (show encode virtualColor key before virtualColor = some ⟨.leaf key [.header (before virtualColor)],[]⟩ by simp [encode])
      refine ⟨[(virtualColor,[.header (before virtualColor)])],1,?_,by decide⟩
      simpa only [Source.rootRecord,SourceLocalProgram.isLeaf,virtualRead,view,present,Option.map_some,Option.toList_some] using actual.prefix
    · have actual := Step.readSome (program := program virtualColor source) (state := .ready state)
        (next := realRead nextRead) (by simp only [program,instruction,virtual,if_false])
        (show encode virtualColor key before q = some (current.mapRecords (List.map Datum.real)) by
          simp only [encode,virtual,if_false,present,Option.map_some])
      refine ⟨[(q,current.focus.rootRecord.map Datum.real)],1,?_,by decide⟩
      simpa only [Cursor.mapRecords,Source.mapRecords_root,isLeaf_mapRecords,realRead,Option.map_some,payload_map,Option.toList_some] using actual.prefix
  | nav instruction present moved =>
    rename_i q current target action
    by_cases virtual : q = virtualColor
    · subst q
      refine ⟨_,2,virtual_steps virtualColor source key state next (.nav action) before target ?_ ?_,le_rfl⟩
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
      exact ⟨[],1,actual.prefix,by decide⟩
  | write instruction present =>
    rename_i q current records
    by_cases virtual : q = virtualColor
    · subst q
      refine ⟨_,2,virtual_steps virtualColor source key state next (.write records) before
        ⟨current.focus.setRoot records,current.ancestors⟩ ?_ ?_,le_rfl⟩
      · simp only [program,instruction,ite_true]
      · simp only [effect,present,Option.bind_some]
    · rw [encode_update_real virtualColor q virtual]
      have actual := Step.write (program := program virtualColor source) (state := .ready state)
        (next := .ready next) (fresh := records.map Datum.real) (by simp only [program,instruction,virtual,if_false])
        (show encode virtualColor key before q = some (current.mapRecords (List.map Datum.real)) by
          simp only [encode,virtual,if_false,present,Option.map_some])
      refine ⟨[],1,?_,by decide⟩
      simpa only [Cursor.mapRecords,Source.mapRecords_setRoot,Option.toList_none] using actual.prefix

theorem compile_run (virtualColor : C) (source : Program σ C ρ) (key : α) {state last : σ}
    {before after : ProjectionForest.State C α ρ} {reads cost}
    (execution : Run source state before last after reads cost) :
    ∃ actualReads actualCost, Run (program virtualColor source) (.ready state) (encode virtualColor key before)
      (.ready last) (encode virtualColor key after) actualReads actualCost ∧ actualCost ≤ 2*cost := by
  induction execution with
  | halt stopped => exact ⟨[],0,.halt (by simp only [program,stopped]),by omega⟩
  | next first rest ih =>
    obtain ⟨firstReads,firstCost,front,firstBound⟩ := step virtualColor source key first
    obtain ⟨lastReads,lastCost,tail,lastBound⟩ := ih
    exact ⟨_,_,front.then_run tail,by omega⟩

end ChaCha.Paper20261030.VirtualHeaderController
