import TangoSquared.Paper20261030.PayloadForestProgram

/-! A checked factor-two execution compiler for unchanged attached
payloads. It decodes logical observations from reached records and never
enters a payload's interior on behalf of a routing-skeleton operation.
-/

namespace TangoSquared.Paper20261030.PayloadForestController

open ColoredStorage SourcePointer ForestLocalProgram

variable {α β ρ C σ : Type*} [DecidableEq C]

theorem step (source : Program σ C ρ) (payload : C → α → Source β (List (Option ρ)))
    {state next : σ} {before after : ProjectionForest.State C α ρ} {entry}
    (execution : Step source state before next after entry) :
    ∃ reads cost, Steps (program source) (.ready state) (transform payload before)
      (.ready next) (transform payload after) reads cost ∧ cost ≤ 2 := by
  cases execution with
  | readNone instruction absent =>
    rename_i nextRead q
    have actual : Step (program source) (.ready state) (transform payload before)
        (.ready (nextRead none)) (transform payload before) none :=
      .readNone (q := q) (next := readNext nextRead) (by simp only [program,instruction])
        (by simp only [transform,absent,Option.map_none])
    exact ⟨[],1,actual.prefix,by decide⟩
  | readSome instruction present =>
    rename_i nextRead q current
    have actual := Step.readSome (program := program source) (state := .ready state)
      (next := readNext nextRead) (by simp only [program,instruction])
      (show transform payload before q = some (SourcePayloads.cursor (payload q) current) by
        simp only [transform,present,Option.map_some])
    refine ⟨[(q,(SourcePayloads.graft (payload q) current.focus).rootRecord)],1,?_,by decide⟩
    simpa only [SourcePayloads.cursor,readNext,Option.map_some,SourcePayloads.graft_root_decode,
      SourcePayloads.graft_leaf,Option.toList_some] using actual.prefix
  | nav instruction present moved =>
    rename_i q current target action
    rw [transform_update]
    have actual : Step (program source) (.ready state) (transform payload before) (.ready next)
        (Function.update (transform payload before) q (some (SourcePayloads.cursor (payload q) target))) none :=
      .nav (by simp only [program,instruction])
        (by simp only [transform,present,Option.map_some]) (SourcePayloads.navigate_graft (payload q) action moved)
    exact ⟨[],1,actual.prefix,by decide⟩
  | write instruction present =>
    rename_i q current fresh
    let stored := SourcePayloads.cursor (payload q) current
    let records := SourcePayloads.replace fresh stored.focus.rootRecord
    have location : transform payload before q = some stored := by simp only [transform,present,Option.map_some,stored]
    have first : Step (program source) (.ready state) (transform payload before)
        (.writing q records next) (transform payload before) (some (q,stored.focus.rootRecord)) := by
      simpa only [writeNext,records] using
        (Step.readSome (program := program source) (state := .ready state)
          (next := writeNext q fresh next) (by simp only [program,instruction]) location)
    have last : Step (program source) (.writing q records next) (transform payload before) (.ready next)
        (Function.update (transform payload before) q (some ⟨stored.focus.setRoot records,stored.ancestors⟩)) none :=
      .write rfl location
    refine ⟨[(q,stored.focus.rootRecord)],2,?_,le_rfl⟩
    rw [transform_update]
    simpa only [stored,records,SourcePayloads.cursor,SourcePayloads.graft_write,
      Option.toList_some,Option.toList_none,List.append_nil] using first.prefix.append last.prefix

theorem compile_run (source : Program σ C ρ) (payload : C → α → Source β (List (Option ρ)))
    {state last : σ} {before after : ProjectionForest.State C α ρ} {reads cost}
    (execution : Run source state before last after reads cost) :
    ∃ actualReads actualCost, Run (program source) (.ready state) (transform payload before)
      (.ready last) (transform payload after) actualReads actualCost ∧ actualCost ≤ 2*cost := by
  induction execution with
  | halt stopped => exact ⟨[],0,.halt (by simp only [program,stopped]),by omega⟩
  | next first rest ih =>
    obtain ⟨firstReads,firstCost,front,firstBound⟩ := step source payload first
    obtain ⟨lastReads,lastCost,tail,lastBound⟩ := ih
    exact ⟨_,_,front.then_run tail,by omega⟩

end TangoSquared.Paper20261030.PayloadForestController
