import Greedy.Algorithm
import Splay.Analysis.IteratedLog

/-!
# The Greedy competitiveness statement in the shared model

`loglogFactor` applies the base-two upper logarithm twice, stabilizing
each input at two. Thus it is positive for every universe size and grows
as `1 + log log n`. `Target` compares the actual geometric touch cost
with the shared attained offline optimum, allowing the initial-tree term.
-/

namespace Greedy

def loglogFactor (n : ℕ) : ℕ := Splay.Analysis.iteratedLog 2 n

def Target : Prop := DynamicOptimality.Competitive cost loglogFactor

theorem loglogFactor_pos (n : ℕ) : 0 < loglogFactor n :=
  Splay.Analysis.iteratedLog_pos (by decide)

end Greedy
