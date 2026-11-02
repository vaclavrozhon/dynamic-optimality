import ChaCha.Paper20261030.GapBSTCompilerCorrectness
import ChaCha.Paper20261030.SourceProgramObservation

/-! Compile a finite helper prefix, without halting or reinitializing the
single-pointer simulator. The resulting physical cursor is retained for the
next helper call. This is the prefix form of the existing GapBST compiler.
-/

namespace DynamicOptimality.SingleFinger.SourceCompile

open ChaCha.Paper20261030

variable {α ρ σ : Type*}

theorem compile_steps {source : SourceLocalProgram.Program σ ρ} {state last : σ}
    {before after : SourcePointer.Cursor α ρ} {observations budget}
    (run : SourceLocalProgram.Steps source state before last after observations budget) :
    ∃ reads cost, LocalProgram.Steps (GapBST.Controller.code source)
      (.ready state (GapBST.Storage.flag before)) (GapBST.Storage.cursor before)
      (.ready last (GapBST.Storage.flag after)) (GapBST.Storage.cursor after) reads cost ∧
      cost ≤ 7*budget := by
  induction run with
  | nil => exact ⟨[],0,.nil _ _,by omega⟩
  | next first rest ih =>
    obtain ⟨firstReads,firstCost,firstRun,firstBound⟩ := GapBST.Controller.compile_step first
    obtain ⟨lastReads,lastCost,lastRun,lastBound⟩ := ih
    exact ⟨firstReads++lastReads,firstCost+lastCost,firstRun.append lastRun,by omega⟩

end DynamicOptimality.SingleFinger.SourceCompile
