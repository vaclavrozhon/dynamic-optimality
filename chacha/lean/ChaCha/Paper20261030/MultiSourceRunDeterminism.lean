import ChaCha.Paper20261030.MultiSourceComposition

set_option autoImplicit false

/-! Two terminating executions of the same shared-tree controller from
the same configuration have identical results, reads, and charged cost. -/

namespace ChaCha.Paper20261030.MultiSourceProgram

variable {α ρ F σ : Type*} [DecidableEq F]

theorem Run.deterministic {source : Program σ F ρ} {state firstLast secondLast : σ}
    {before firstAfter secondAfter : Configuration F α ρ} {firstReads secondReads firstCost secondCost}
    (first : Run source state before firstLast firstAfter firstReads firstCost)
    (second : Run source state before secondLast secondAfter secondReads secondCost) :
    firstLast = secondLast ∧ firstAfter = secondAfter ∧ firstReads = secondReads ∧ firstCost = secondCost := by
  induction first generalizing secondLast secondAfter secondReads secondCost with
  | halt stopped => cases second with
    | halt => exact ⟨rfl,rfl,rfl,rfl⟩
    | next step rest => exact False.elim (step.not_halted stopped)
  | next step rest ih => cases second with
    | halt stopped => exact False.elim (step.not_halted stopped)
    | next other tail =>
      obtain ⟨sameState,sameConfig,sameRead⟩ := step.deterministic other
      cases sameState
      cases sameConfig
      cases sameRead
      obtain ⟨lastEq,afterEq,readsEq,costEq⟩ := ih tail
      exact ⟨lastEq,afterEq,congrArg _ readsEq,congrArg (·+1) costEq⟩

end ChaCha.Paper20261030.MultiSourceProgram
