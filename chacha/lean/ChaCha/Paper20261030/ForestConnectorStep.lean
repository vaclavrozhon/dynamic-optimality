import ChaCha.Paper20261030.ForestConnectorSingle

/-! A forest step is one step in the joined physical tree. Distinct
layout leaves ensure that a color operation leaves every other piece's
finger registers and interior in place. The only instruction-scoping
condition concerns the current instruction and will be discharged from
the layout's coverage of the initial forest.
-/

namespace ChaCha.Paper20261030.ForestConnector

open ColoredStorage SourcePointer

variable {α ρ C σ : Type*} [DecidableEq C]

theorem step (source : ForestLocalProgram.Program σ C ρ) {state next : σ}
    {before after : ProjectionForest.State C α ρ} {entry}
    (execution : ForestLocalProgram.Step source state before next after entry)
    (layout : Source C Unit) (distinct : (colors layout).Nodup)
    (config : MultiSourceProgram.Configuration C α (List ρ)) (represented : assemble before layout = some config)
    (scopeReady : Scoped source state before layout) :
    ∃ target, assemble after layout = some target ∧ MultiSourceProgram.Step (program source) state config next target entry := by
  obtain ⟨selected,targets,unchanged⟩ := step_target source execution
  induction layout generalizing config with
  | leaf q value =>
    cases location : before q with
    | none => simp only [assemble,location,Option.map_none,reduceCtorEq] at represented
    | some current =>
      have equal : single q current = config := by simpa only [assemble,location,Option.map_some,Option.some.injEq] using represented
      subst config
      obtain ⟨target,present,actual⟩ := single_step source execution q current location scopeReady
      exact ⟨single q target,by simp only [assemble,present,Option.map_some],actual⟩
  | fork value left right ihl ihr =>
    obtain ⟨l,r,leftRep,rightRep,rfl⟩ := assemble_fork represented
    have noDuplicates : (colors left).Nodup ∧ (colors right).Nodup ∧ ∀ a ∈ colors left, ∀ b ∈ colors right, a ≠ b := by
      simpa only [colors,Source.shape,RouterProjection.Router.leaves,List.nodup_append] using distinct
    by_cases inLeft : selected ∈ colors left
    · have outRight : selected ∉ colors right := by
        intro member
        exact noDuplicates.2.2 selected inLeft selected member rfl
      have leftScope : Scoped source state before left := by
        intro q member current location
        have equal : q = selected := by simpa only [targets,List.mem_singleton] using member
        simpa only [equal] using inLeft
      obtain ⟨target,leftAfter,actual⟩ := ihl noDuplicates.1 l leftRep leftScope
      have rightSame : assemble before right = assemble after right := assemble_congr right before after (fun q member =>
        unchanged q (by intro equal; subst q; exact outRight member))
      have avoid : ∀ q ∈ (program source state).targets, r.fingers q = none := by
        intro q member
        have equal : q = selected := by simpa only [targets,List.mem_singleton] using member
        subst q
        exact assemble_outside before right r rightRep selected outRight
      refine ⟨MultiSourceProgram.join [] target r,?_,actual.join_left [] r avoid⟩
      simp only [assemble,leftAfter,← rightSame,rightRep,Option.bind_some,Option.map_some]
    · have rightScope : Scoped source state before right := by
        intro q member current location
        have equal : q = selected := by simpa only [targets,List.mem_singleton] using member
        subst q
        have either : selected ∈ colors left ∨ selected ∈ colors right := by
          simpa only [colors,Source.shape,RouterProjection.Router.leaves,List.mem_append] using scopeReady selected member current location
        exact either.resolve_left inLeft
      obtain ⟨target,rightAfter,actual⟩ := ihr noDuplicates.2.1 r rightRep rightScope
      have leftSame : assemble before left = assemble after left := assemble_congr left before after (fun q member =>
        unchanged q (by intro equal; subst q; exact inLeft member))
      have avoid : ∀ q ∈ (program source state).targets, l.fingers q = none := by
        intro q member
        have equal : q = selected := by simpa only [targets,List.mem_singleton] using member
        subst q
        exact assemble_outside before left l leftRep selected inLeft
      refine ⟨MultiSourceProgram.join [] l target,?_,actual.join_right [] l avoid⟩
      simp only [assemble,← leftSame,leftRep,rightAfter,Option.bind_some,Option.map_some]

end ChaCha.Paper20261030.ForestConnector
