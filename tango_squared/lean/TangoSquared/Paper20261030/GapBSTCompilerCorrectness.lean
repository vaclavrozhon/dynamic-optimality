import TangoSquared.Paper20261030.GapBSTCompilerKernels

/-! Complete simulation of source-local programs by the uniform ordinary
BST controller compiler. The same source register state is retained, with
only a slot flag and constant-size helper state added. Each source step
costs at most seven physical operations. -/

namespace TangoSquared.Paper20261030.GapBST.Controller

open ColoredStorage Storage DynamicOptimality

variable {α ρ σ : Type*}

theorem move_prefix {source : SourceLocalProgram.Program σ ρ} {state next : σ} {action : LocalProgram.Move}
    (instruction : source state = .nav action next) {before after : SourcePointer.Cursor α ρ}
    (moved : SourceLocalProgram.navigate action before = some after) :
    ∃ reads cost, LocalProgram.Steps (code source) (.ready state (flag before)) (Storage.cursor before)
      (.ready next (flag after)) (Storage.cursor after) reads cost ∧ cost ≤ 7 := by
  rcases before with ⟨focus,rest⟩
  cases action with
  | left => cases focus with
    | leaf => simp [SourceLocalProgram.navigate] at moved
    | fork value left right =>
      cases Option.some.inj moved
      obtain ⟨reads,cost,run,bound⟩ := left_program left right value rest
      exact ⟨reads,cost,navigation_prefix (action := .left) instruction run,bound.trans (by decide)⟩
  | right => cases focus with
    | leaf => simp [SourceLocalProgram.navigate] at moved
    | fork value left right =>
      cases Option.some.inj moved
      obtain ⟨reads,cost,run,bound⟩ := right_program left right value rest
      exact ⟨reads,cost,navigation_prefix (action := .right) instruction run,bound.trans (by decide)⟩
  | up => cases rest with
    | nil => simp [SourceLocalProgram.navigate] at moved
    | cons first rest => cases first with
      | left value right =>
        cases Option.some.inj moved
        obtain ⟨reads,cost,run,bound⟩ := up_left_program focus right value rest
        exact ⟨reads,cost,navigation_prefix (action := .up) instruction run,bound.trans (by decide)⟩
      | right left value =>
        cases Option.some.inj moved
        obtain ⟨reads,cost,run,bound⟩ := up_right_program left focus value rest
        exact ⟨reads,cost,navigation_prefix (action := .up) instruction run,bound.trans (by decide)⟩
  | rotateRight => cases focus with
    | leaf => simp [SourceLocalProgram.navigate] at moved
    | fork q left w => cases left with
      | leaf => simp [SourceLocalProgram.navigate] at moved
      | fork p u v =>
        cases Option.some.inj moved
        exact ⟨_,7,rotation_prefix (right := true) instruction (rotate_right_program u v w p q rest),le_rfl⟩
  | rotateLeft => cases focus with
    | leaf => simp [SourceLocalProgram.navigate] at moved
    | fork p u right => cases right with
      | leaf => simp [SourceLocalProgram.navigate] at moved
      | fork q v w =>
        cases Option.some.inj moved
        exact ⟨_,7,rotation_prefix (right := false) instruction (rotate_left_program u v w p q rest),le_rfl⟩

theorem flag_write (logical : SourcePointer.Cursor α ρ) (fresh : ρ) :
    flag ⟨logical.focus.setRoot fresh,logical.ancestors⟩ = flag logical := by
  rcases logical with ⟨focus,rest⟩
  cases focus <;> rfl

theorem compile_step {source : SourceLocalProgram.Program σ ρ} {state next : σ}
    {before after : SourcePointer.Cursor α ρ} {entry}
    (step : SourceLocalProgram.Step source state before next after entry) :
    ∃ reads cost, LocalProgram.Steps (code source) (.ready state (flag before)) (Storage.cursor before)
      (.ready next (flag after)) (Storage.cursor after) reads cost ∧ cost ≤ 7 := by
  cases step with
  | @read next logical instruction =>
    obtain ⟨reads,run⟩ := read_prefix instruction before
    exact ⟨reads,1,run,by decide⟩
  | nav instruction moved => exact move_prefix instruction moved
  | @write next logical fresh instruction =>
    obtain ⟨reads,run⟩ := write_program before fresh
    exact ⟨reads,2,by simpa only [flag_write] using write_prefix instruction run,by decide⟩

theorem compile_run {source : SourceLocalProgram.Program σ ρ} {state last : σ}
    {before after : SourcePointer.Cursor α ρ} {observations budget}
    (run : SourceLocalProgram.Run source state before last after observations budget) :
    ∃ reads cost, LocalProgram.Run (code source) (.ready state (flag before)) (Storage.cursor before)
      (.ready last (flag after)) (Storage.cursor after) reads cost ∧ cost ≤ 7*budget := by
  induction run with
  | halt stopped => exact ⟨[],0,.halt (by simp only [code,stopped]),by omega⟩
  | next first rest ih =>
    obtain ⟨firstReads,firstCost,firstRun,firstBound⟩ := compile_step first
    obtain ⟨lastReads,lastCost,lastRun,lastBound⟩ := ih
    exact ⟨firstReads++lastReads,firstCost+lastCost,firstRun.then_run lastRun,by omega⟩

end TangoSquared.Paper20261030.GapBST.Controller
