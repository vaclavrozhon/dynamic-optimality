import TangoSquared.Paper20261030.MultiSourceAugment
import TangoSquared.Paper20261030.MultiSourceWriteLabelSteps

set_option autoImplicit false

/-! The metadata compiler preserves the reached immutable field at
 every write, not just its global inventory. This exposes the stronger
 execution invariant needed for parked physical anchors. -/

namespace TangoSquared.Paper20261030.MultiSourceAugment

open ColoredStorage SourcePointer SourcePositions MultiSourceProgram

variable {α ρ μ F σ : Type*} [DecidableEq F]

theorem stable_saved (config : Configuration F α (ρ × μ)) (finger : F) (position : List Bool)
    (current : Cursor α (ρ × μ)) (fresh : ρ) (next : σ)
    (present : config.fingers finger = some position) (reached : locate config.tree position = some current) :
    MultiSourceWriteLabels.Stable Prod.snd (program (fun _ : σ => .halt) (.writeBack finger fresh current.focus.rootRecord.2 next)) config := by
  intro otherPosition other atFinger found
  have samePosition := Option.some.inj (atFinger.symm.trans present)
  subst otherPosition
  have same := Option.some.inj (found.symm.trans reached)
  subst other
  rfl

theorem compile_metadata_step {source : Program σ F ρ} {state next : σ}
    {before after : Configuration F α ρ} {entry}
    (step : Step source state before next after entry)
    (config : Configuration F α (ρ × μ)) (erases : config.mapRecords Prod.fst = before) :
    ∃ target reads cost,
      MultiSourceWriteLabels.Steps Prod.snd (program source) (.ready state) config (.ready next) target reads cost ∧
      target.mapRecords Prod.fst = after ∧
      target.tree.inventory Prod.snd = config.tree.inventory Prod.snd ∧ cost ≤ 2 := by
  subst before
  cases step with
  | @readNone finger next instruction absent =>
    refine ⟨config,[],1,?_,rfl,rfl,by omega⟩
    exact (Step.readNone (program := program source) (state := .ready state)
      (next := fun observed => .ready (next (view observed)))
      (by simp only [program,instruction]) absent).label_prefix (label := Prod.snd) (by simp only [program,instruction,MultiSourceWriteLabels.Stable])
  | @readSome finger position original next instruction present reached =>
    obtain ⟨current,found,same⟩ := lift_locate Prod.fst config.tree _ _ reached
    subst_vars
    refine ⟨config,[(finger,current.focus.rootRecord)],1,?_,rfl,rfl,by omega⟩
    simpa only [Cursor.mapRecords,Source.mapRecords_root,isLeaf_mapRecords,view,Option.map_some,Option.toList_some] using
      (Step.readSome (program := program source) (state := .ready state)
        (next := fun observed => .ready (next (view observed)))
        (by simp only [program,instruction]) present found).label_prefix (label := Prod.snd) (by simp only [program,instruction,MultiSourceWriteLabels.Stable])
  | @nav finger position before after action next instruction present reached moved =>
    obtain ⟨current,found,same⟩ := lift_locate Prod.fst config.tree position before reached
    rw [← same] at moved
    obtain ⟨target,advance,erased⟩ := lift_navigation Prod.fst action current after moved
    refine ⟨moveResult config finger action current target,[],1,?_,?_,?_,by omega⟩
    · exact (Step.nav (program := program source) (state := .ready state)
        (by simp only [program,instruction]) present found advance).label_prefix (label := Prod.snd) (by simp only [program,instruction,MultiSourceWriteLabels.Stable])
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
      exact .next readStep (by simp only [program,instruction,MultiSourceWriteLabels.Stable])
        (writeStep.label_prefix (stable_saved config finger position actual fresh next present found))
    · simpa only [final,writeResult_mapRecords,same]
  | @copy destination origin next instruction =>
    refine ⟨copyResult config destination origin,[],1,?_,rfl,rfl,by omega⟩
    exact (Step.copy (program := program source) (state := .ready state)
      (by simp only [program,instruction])).label_prefix (label := Prod.snd) (by simp only [program,instruction,MultiSourceWriteLabels.Stable])

theorem compile_metadata_run {source : Program σ F ρ} {state last : σ}
    {before after : Configuration F α ρ} {reads cost}
    (run : Run source state before last after reads cost)
    (config : Configuration F α (ρ × μ)) (erases : config.mapRecords Prod.fst = before) :
    ∃ target actualReads actualCost,
      MultiSourceWriteLabels.Run Prod.snd (program source) (.ready state) config (.ready last) target actualReads actualCost ∧
      target.mapRecords Prod.fst = after ∧
      target.tree.inventory Prod.snd = config.tree.inventory Prod.snd ∧ actualCost ≤ 2*cost := by
  induction run generalizing config with
  | halt stopped => exact ⟨config,[],0,.halt (by simp only [program,stopped]),erases,rfl,by omega⟩
  | next first rest ih =>
    obtain ⟨middle,firstReads,firstCost,firstRun,firstErases,firstMetadata,firstBound⟩ := compile_metadata_step first config erases
    obtain ⟨target,lastReads,lastCost,lastRun,lastErases,lastMetadata,lastBound⟩ := ih middle firstErases
    exact ⟨target,firstReads++lastReads,firstCost+lastCost,firstRun.then_run lastRun,
      lastErases,lastMetadata.trans firstMetadata,by omega⟩

end TangoSquared.Paper20261030.MultiSourceAugment
