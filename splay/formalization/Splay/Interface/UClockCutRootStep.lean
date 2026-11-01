import Splay.Interface.UCrossingKeyBelowHistory

namespace Splay.Interface

/--
The fixed chronological cut's root uniqueness and pass-floor invariants are
preserved by every exact legal operation.

This closes the last one-step hypothesis used by the concrete `u`-column
history argument.
-/
theorem clockCutRootStep : ClockCutRootStepHypothesis := by
  intro n params before after labels ledger clock events operation
    exact clockSound aligned phase step eventIndex past accumulator
  apply
    clockCutRootStepResult_of_unique_after
      before after labels ledger clock events operation exact step aligned
      phase eventIndex past accumulator
  exact
    RootClockCutUniqueAt.after_step
      exact clockSound aligned phase
      accumulator.ordered accumulator.unique step

end Splay.Interface
