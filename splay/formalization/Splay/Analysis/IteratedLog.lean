import Splay.Analysis.ContractedGap
import Mathlib.Tactic.Positivity

namespace Splay.Analysis

/--
A base-two upper logarithm stabilized at one. The `max 2` convention removes
all small-input side conditions from the eventual competitiveness statement.
-/
def stabilizedLog (n : ℕ) : ℕ :=
  Nat.clog 2 (max 2 n)

/-- Apply `stabilizedLog` exactly `depth` times. -/
def iteratedLog : ℕ → ℕ → ℕ
  | 0, n => n
  | depth + 1, n => stabilizedLog (iteratedLog depth n)

/--
The factor in the main theorem:
`log log n * (log log log n)^2`, with stabilized integer logarithms.
-/
def targetFactor (n : ℕ) : ℕ :=
  iteratedLog 2 n * (iteratedLog 3 n) ^ 2

/--
The corresponding factor when the analysis is parameterized by a comparison
tree's maximum depth rather than by the number of keys.
-/
def heightFactor (height : ℕ) : ℕ :=
  contractedGap (height + 1) *
    (stabilizedLog (contractedGap (height + 1))) ^ 2

theorem stabilizedLog_pos (n : ℕ) : 0 < stabilizedLog n := by
  unfold stabilizedLog
  exact Nat.clog_pos (by omega) (by omega)

theorem iteratedLog_pos {depth n : ℕ} (hDepth : 0 < depth) :
    0 < iteratedLog depth n := by
  cases depth with
  | zero => contradiction
  | succ depth =>
      exact stabilizedLog_pos (iteratedLog depth n)

theorem targetFactor_pos (n : ℕ) : 0 < targetFactor n := by
  unfold targetFactor
  have h₂ : 0 < iteratedLog 2 n := iteratedLog_pos (by omega)
  have h₃ : 0 < iteratedLog 3 n := iteratedLog_pos (by omega)
  positivity

end Splay.Analysis
