import ChaCha.Paper20261030.ForestWriteLabels
import ChaCha.Paper20261030.PayloadForestCompiler

set_option autoImplicit false

/-! Retaining per-vertex labels when routing leaves carry whole payload
subtrees. Replacing the routing prefix preserves its labels by the
source guarantee and leaves the entire payload suffix unchanged. -/

namespace ChaCha.Paper20261030.SourcePayloads

open ColoredStorage SourcePointer

variable {α β ρ ι : Type*}

theorem map_some_labels (label : ρ → ι) (records : List ρ) :
    (records.map some).map (Option.map label) = (records.map label).map some := by
  simp only [List.map_map,Function.comp_def,Option.map_some]

theorem replace_graft_labels (label : ρ → ι) (payload : α → Source β (List (Option ρ)))
    (source : Source α (List ρ)) (fresh : List ρ)
    (same : fresh.map label = source.rootRecord.map label) :
    (replace fresh (graft payload source).rootRecord).map (Option.map label) =
      (graft payload source).rootRecord.map (Option.map label) := by
  cases source with
  | leaf key records =>
    cases reached : payload key <;>
      simp only [graft,reached,Source.setRoot,Source.rootRecord,replace_attachment,List.map_append,
        map_some_labels,Source.rootRecord] at same ⊢ <;> rw [same]
  | fork records left right =>
    simp only [graft,Source.rootRecord,replace_internal,map_some_labels,Source.rootRecord] at same ⊢
    rw [same]

end ChaCha.Paper20261030.SourcePayloads

namespace ChaCha.Paper20261030.PayloadForestController

open ColoredStorage SourcePointer ForestLocalProgram

variable {α β ρ ι C σ : Type*} [DecidableEq C]

theorem stable_ready (label : ρ → ι) (source : Program σ C ρ) (state : σ)
    (forest : ProjectionForest.State C β (Option ρ)) :
    ForestWriteLabels.Stable (Option.map label) (program source (.ready state)) forest := by
  cases code : source state <;> simp only [program,code,ForestWriteLabels.Stable]

theorem step_labels (label : ρ → ι) (source : Program σ C ρ) (payload : C → α → Source β (List (Option ρ)))
    {state next : σ} {before after : ProjectionForest.State C α ρ} {entry}
    (execution : Step source state before next after entry)
    (safe : ForestWriteLabels.Stable label (source state) before) :
    ∃ reads cost, ForestWriteLabels.Steps (Option.map label) (program source) (.ready state) (transform payload before)
      (.ready next) (transform payload after) reads cost ∧ cost ≤ 2 := by
  cases execution with
  | readNone instruction absent =>
    rename_i nextRead q
    have actual : Step (program source) (.ready state) (transform payload before)
        (.ready (nextRead none)) (transform payload before) none :=
      .readNone (q := q) (next := readNext nextRead) (by simp only [program,instruction])
        (by simp only [transform,absent,Option.map_none])
    exact ⟨[],1,(ForestWriteLabels.step_prefix actual (stable_ready label source state _)),by decide⟩
  | readSome instruction present =>
    rename_i nextRead q current
    have actual := Step.readSome (program := program source) (state := .ready state)
      (next := readNext nextRead) (by simp only [program,instruction])
      (show transform payload before q = some (SourcePayloads.cursor (payload q) current) by
        simp only [transform,present,Option.map_some])
    refine ⟨[(q,(SourcePayloads.graft (payload q) current.focus).rootRecord)],1,?_,by decide⟩
    simpa only [SourcePayloads.cursor,readNext,Option.map_some,SourcePayloads.graft_root_decode,
      SourcePayloads.graft_leaf,Option.toList_some] using (ForestWriteLabels.step_prefix actual (stable_ready label source state _))
  | nav instruction present moved =>
    rename_i q current target action
    rw [transform_update]
    have actual : Step (program source) (.ready state) (transform payload before) (.ready next)
        (Function.update (transform payload before) q (some (SourcePayloads.cursor (payload q) target))) none :=
      .nav (by simp only [program,instruction])
        (by simp only [transform,present,Option.map_some]) (SourcePayloads.navigate_graft (payload q) action moved)
    exact ⟨[],1,(ForestWriteLabels.step_prefix actual (stable_ready label source state _)),by decide⟩
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
    have checked := safe
    simp only [instruction,ForestWriteLabels.Stable] at checked
    have same := checked current present
    have lastSafe : ForestWriteLabels.Stable (Option.map label)
        (program source (.writing q records next)) (transform payload before) := by
      intro actual located
      have equal := Option.some.inj (located.symm.trans location)
      subst actual
      exact SourcePayloads.replace_graft_labels label (payload q) current.focus fresh same
    refine ⟨[(q,stored.focus.rootRecord)],2,?_,le_rfl⟩
    rw [transform_update]
    simpa only [stored,records,SourcePayloads.cursor,SourcePayloads.graft_write,
      Option.toList_some,Option.toList_none,List.append_nil] using (ForestWriteLabels.step_prefix first (stable_ready label source state _)).append (ForestWriteLabels.step_prefix last lastSafe)

theorem compile_write_labels (label : ρ → ι) (source : Program σ C ρ) (payload : C → α → Source β (List (Option ρ)))
    {state last : σ} {before after : ProjectionForest.State C α ρ} {reads cost}
    (execution : ForestWriteLabels.Run label source state before last after reads cost) :
    ∃ actualReads actualCost, ForestWriteLabels.Run (Option.map label) (program source) (.ready state) (transform payload before)
      (.ready last) (transform payload after) actualReads actualCost ∧ actualCost ≤ 2*cost := by
  induction execution with
  | halt stopped => exact ⟨[],0,.halt (by simp only [program,stopped]),by omega⟩
  | next first safe rest ih =>
    obtain ⟨firstReads,firstCost,front,firstBound⟩ := step_labels label source payload first safe
    obtain ⟨lastReads,lastCost,tail,lastBound⟩ := ih
    exact ⟨_,_,front.then_run tail,by omega⟩

end ChaCha.Paper20261030.PayloadForestController
