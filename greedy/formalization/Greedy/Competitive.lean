import Greedy.ActualLedger
import Greedy.ComparisonReduction

/-!
# Greedy is log-log competitive in the shared BST model

`cost` counts the geometric Greedy touches from the prescribed initial
BST. The comparator is a genuine sequence of BST rotations and requests.
The constructed block execution and its initialized journal discharge
all accounting premises internally. The shared polylogarithmic-height
normal form then supplies comparison with the attained offline optimum.
-/

namespace Greedy

open Splay.Tree Splay.Tree.BST Splay.Analysis Splay.Assumptions.NormalForm

theorem cost_le_bounded_trace {n : ℕ} (positive : 0 < n) (initial : BST 0 n)
    (requests : List (Fin n)) (trace : ComparisonTrace n requests) (H : ℕ)
    (height : ∀ time, (trace.state time).height ≤ H)
    (depth : ∀ step, trace.rotationDepth step ≤ 1) :
    cost initial requests ≤ 32000 * (n + trace.cost) * contractedGap H := by
  obtain ⟨last, execution, _valid, _comparator, rotations, births, bounded, costIdentity⟩ :=
    Execution.exists_shared_run initial requests trace H height depth (contractedGap H)
  have linkBound := execution_link_bound initial (trace.state 0) H execution bounded
  have reserve : 3*(2*n+1) + execution.births + 33*execution.rotations ≤ 132*(n+trace.cost) := by
    rw [rotations]
    unfold ComparisonTrace.cost
    omega
  have cap : 1 ≤ contractedGap H := by unfold contractedGap; omega
  have requestBound : requests.length ≤ (n+trace.cost)*contractedGap H := by
    have within : requests.length ≤ n+trace.cost := by unfold ComparisonTrace.cost; omega
    nlinarith
  have scaled := Nat.mul_le_mul_left (239 * contractedGap H) reserve
  have links : execution.links ≤ 239 * contractedGap H * (132*(n+trace.cost)) := linkBound.trans scaled
  have costBound : cost initial requests ≤ requests.length + execution.links := by omega
  nlinarith only [costBound, links, requestBound]

theorem bounded_comparison : BoundedComparisonBound := by
  refine ⟨32000, by decide, ?_⟩
  intro n positive initial requests trace H height depth
  have bound := cost_le_bounded_trace positive initial requests trace H height depth
  have range : contractedGap H ≤ 1 + Nat.clog 2 (H+2) := by
    unfold contractedGap gapBucket
    exact Nat.add_le_add_left (Nat.clog_mono_right 2 (by omega)) 1
  exact bound.trans (Nat.mul_le_mul_left _ range)

/-- The actual geometric Greedy algorithm is `O(1 + log log n)` competitive
against the shared attained optimum, with the usual additive initial size. -/
theorem competitive : Target := target_of_bounded_comparison bounded_comparison

end Greedy
