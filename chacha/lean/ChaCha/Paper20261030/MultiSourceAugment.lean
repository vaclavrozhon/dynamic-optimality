import ChaCha.Paper20261030.MultiSourceRecordMap

/-! Running a shared-tree program while preserving an extra metadata field.
Every physical record is a pair. The source program observes its first
field. Before a write, the compiler reads the reached pair and carries
its second field through the write. This costs at most two instructions
per source instruction and uses one saved metadata value.
-/

namespace ChaCha.Paper20261030.MultiSourceAugment

open ColoredStorage SourcePointer SourcePositions MultiSourceProgram

variable {α ρ μ F σ : Type*} [DecidableEq F]

inductive State (σ F ρ μ : Type*) where
  | ready (state : σ)
  | writeBack (finger : F) (fresh : ρ) (saved : μ) (next : σ)
  | blocked

def view (observed : View (ρ × μ)) : View ρ :=
  observed.map (fun pair => (pair.1.1,pair.2))

def program (source : Program σ F ρ) : Program (State σ F ρ μ) F (ρ × μ)
  | .blocked => .halt
  | .writeBack finger fresh saved next => .write finger (fresh,saved) (.ready next)
  | .ready state => match source state with
    | .halt => .halt
    | .read finger next => .read finger (fun observed => .ready (next (view observed)))
    | .nav finger action next => .nav finger action (.ready next)
    | .copy destination origin next => .copy destination origin (.ready next)
    | .write finger fresh next => .read finger (fun observed => match observed with
      | none => .blocked
      | some pair => .writeBack finger fresh pair.1.2 next)

theorem write_metadata (config : Configuration F α (ρ × μ)) (current : Cursor α (ρ × μ))
    (fresh : ρ) (sameTree : current.tree = config.tree) :
    (writeResult config current (fresh,current.focus.rootRecord.2)).tree.inventory Prod.snd =
      config.tree.inventory Prod.snd := by
  rw [← sameTree]
  exact plug_inventory_congr Prod.snd
    (Source.inventory_setRoot Prod.snd current.focus (fresh,current.focus.rootRecord.2) rfl) current.ancestors

theorem compile_step {source : Program σ F ρ} {state next : σ}
    {before after : Configuration F α ρ} {entry}
    (step : Step source state before next after entry)
    (config : Configuration F α (ρ × μ)) (erases : config.mapRecords Prod.fst = before) :
    ∃ target reads cost,
      Steps (program source) (.ready state) config (.ready next) target reads cost ∧
      target.mapRecords Prod.fst = after ∧
      target.tree.inventory Prod.snd = config.tree.inventory Prod.snd ∧ cost ≤ 2 := by
  subst before
  cases step with
  | @readNone finger next instruction absent =>
    refine ⟨config,[],1,?_,rfl,rfl,by omega⟩
    exact (Step.readNone (program := program source) (state := .ready state)
      (next := fun observed => .ready (next (view observed)))
      (by simp only [program,instruction]) absent).prefix
  | @readSome finger position original next instruction present reached =>
    obtain ⟨current,found,same⟩ := lift_locate Prod.fst config.tree _ _ reached
    subst_vars
    refine ⟨config,[(finger,current.focus.rootRecord)],1,?_,rfl,rfl,by omega⟩
    simpa only [Cursor.mapRecords,Source.mapRecords_root,isLeaf_mapRecords,view,Option.map_some,Option.toList_some] using
      (Step.readSome (program := program source) (state := .ready state)
        (next := fun observed => .ready (next (view observed)))
        (by simp only [program,instruction]) present found).prefix
  | @nav finger position before after action next instruction present reached moved =>
    obtain ⟨current,found,same⟩ := lift_locate Prod.fst config.tree position before reached
    rw [← same] at moved
    obtain ⟨target,advance,erased⟩ := lift_navigation Prod.fst action current after moved
    refine ⟨moveResult config finger action current target,[],1,?_,?_,?_,by omega⟩
    · exact (Step.nav (program := program source) (state := .ready state)
        (by simp only [program,instruction]) present found advance).prefix
    · simpa only [moveResult_mapRecords,same,erased]
    · change target.tree.inventory Prod.snd = config.tree.inventory Prod.snd
      rw [← locate_tree found]
      exact (navigate_inventory Prod.snd action advance).symm
  | @write finger position current fresh next instruction present reached =>
    obtain ⟨actual,found,same⟩ := lift_locate Prod.fst config.tree position current reached
    let final := writeResult config actual (fresh,actual.focus.rootRecord.2)
    refine ⟨final,[(finger,actual.focus.rootRecord)],2,?_,?_,write_metadata config actual fresh (locate_tree found),by omega⟩
    · have readStep : Step (program source) (.ready state) config
          (.writeBack finger fresh actual.focus.rootRecord.2 next) config (some (finger,actual.focus.rootRecord)) :=
        .readSome (program := program source) (config := config)
          (next := fun observed => match observed with
            | none => .blocked
            | some pair => .writeBack finger fresh pair.1.2 next)
          (by simp only [program,instruction]; rfl) present found
      have writeStep : Step (program source) (.writeBack finger fresh actual.focus.rootRecord.2 next)
          config (.ready next) final none := .write rfl present found
      exact .next readStep writeStep.prefix
    · simpa only [final,writeResult_mapRecords,same]
  | @copy destination origin next instruction =>
    refine ⟨copyResult config destination origin,[],1,?_,rfl,rfl,by omega⟩
    exact (Step.copy (program := program source) (state := .ready state)
      (by simp only [program,instruction])).prefix

theorem compile_run {source : Program σ F ρ} {state last : σ}
    {before after : Configuration F α ρ} {reads cost}
    (run : Run source state before last after reads cost)
    (config : Configuration F α (ρ × μ)) (erases : config.mapRecords Prod.fst = before) :
    ∃ target actualReads actualCost,
      Run (program source) (.ready state) config (.ready last) target actualReads actualCost ∧
      target.mapRecords Prod.fst = after ∧
      target.tree.inventory Prod.snd = config.tree.inventory Prod.snd ∧ actualCost ≤ 2*cost := by
  induction run generalizing config with
  | halt stopped => exact ⟨config,[],0,.halt (by simp only [program,stopped]),erases,rfl,by omega⟩
  | next first rest ih =>
    obtain ⟨middle,firstReads,firstCost,firstRun,firstErases,firstMetadata,firstBound⟩ := compile_step first config erases
    obtain ⟨target,lastReads,lastCost,lastRun,lastErases,lastMetadata,lastBound⟩ := ih middle firstErases
    exact ⟨target,firstReads++lastReads,firstCost+lastCost,firstRun.then_run lastRun,
      lastErases,lastMetadata.trans firstMetadata,by omega⟩

end ChaCha.Paper20261030.MultiSourceAugment
