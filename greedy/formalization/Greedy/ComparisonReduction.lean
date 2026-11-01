import Greedy.Statement
import Splay.Accounting.ConstructedPolylogNormalForm

/-!
# Reducing the final theorem to bounded-height comparison

The existing splay development constructs actual depth-one comparison
rotations at polylogarithmic height, at cost linear in `OPT + n`.
Their logarithmic label range is still `O(log log n)`. The reduction
below takes the Greedy comparison inequality as a premise.
`Greedy.Competitive` proves that premise and the unconditional target.
-/

namespace Greedy

open Splay.Analysis Splay.Assumptions.NormalForm

theorem labelRange_of_polylog (multiplier exponent n height : ℕ)
    (heightBound : height ≤ multiplier * (stabilizedLog n) ^ exponent) :
    1 + Nat.clog 2 (height + 2) ≤
      (Nat.clog 2 (multiplier + 2) + exponent + 2) * loglogFactor n := by
  let first := stabilizedLog n
  let second := stabilizedLog first
  let constant := Nat.clog 2 (multiplier + 2)
  have firstPositive : 0 < first := stabilizedLog_pos n
  have secondPositive : 0 < second := stabilizedLog_pos first
  have constantPower : multiplier + 2 ≤ 2 ^ constant := Nat.le_pow_clog (by decide) _
  have firstPower : max 2 first ≤ 2 ^ second := Nat.le_pow_clog (by decide) _
  have monotonePower : first ^ exponent ≤ (max 2 first) ^ exponent :=
    Nat.pow_le_pow_left (Nat.le_max_right _ _) exponent
  have positivePower : 1 ≤ (max 2 first) ^ exponent := by
    have positive : 0 < (max 2 first) ^ exponent := by positivity
    omega
  have argument : height + 2 ≤ (multiplier + 2) * (max 2 first) ^ exponent := by
    calc
      height + 2 ≤ multiplier * first ^ exponent + 2 := Nat.add_le_add_right heightBound 2
      _ ≤ multiplier * (max 2 first) ^ exponent + 2 * (max 2 first) ^ exponent :=
        Nat.add_le_add (Nat.mul_le_mul_left _ monotonePower) (by omega)
      _ = _ := by ring
  have powerBound : height + 2 ≤ 2 ^ (constant + second * exponent) := by
    calc
      height + 2 ≤ (multiplier + 2) * (max 2 first) ^ exponent := argument
      _ ≤ 2 ^ constant * (2 ^ second) ^ exponent :=
        Nat.mul_le_mul constantPower (Nat.pow_le_pow_left firstPower exponent)
      _ = _ := by rw [Nat.pow_add, Nat.pow_mul]
  have logarithm : Nat.clog 2 (height + 2) ≤ constant + second * exponent :=
    Nat.clog_le_of_le_pow powerBound
  change 1 + Nat.clog 2 (height + 2) ≤ (constant + exponent + 2) * second
  nlinarith

/-- The bounded-height comparison property proved by `Greedy.bounded_comparison`.
The comparator consists of genuine BST rotations. -/
def BoundedComparisonBound : Prop :=
  ∃ C : ℕ, 0 < C ∧ ∀ n : ℕ, 0 < n →
    ∀ initial : DynamicOptimality.BST 0 n, ∀ requests : List (Fin n),
    ∀ trace : ComparisonTrace n requests, ∀ height : ℕ,
      (∀ time, (trace.state time).height ≤ height) →
      (∀ step, trace.rotationDepth step ≤ 1) →
      cost initial requests ≤ C * (n + trace.cost) * (1 + Nat.clog 2 (height + 2))

theorem target_of_bounded_comparison (core : BoundedComparisonBound) : Target := by
  obtain ⟨C, positive, bound⟩ := core
  let scale := Nat.clog 2 (54000 + 2) + 3 + 2
  refine ⟨C * 400000001 * scale, by dsimp [scale]; positivity, ?_⟩
  intro n hn initial requests
  let trace := Splay.Accounting.ConstructedPolylogNormalForm.trace requests
  let height := 54000 * (stabilizedLog n) ^ 3
  have greedyBound := bound n hn initial requests trace height
    (Splay.Accounting.ConstructedPolylogNormalForm.trace_height requests)
    (Splay.Accounting.ConstructedPolylogNormalForm.trace_depth requests)
  have traceBound := Splay.Accounting.ConstructedPolylogNormalForm.trace_cost requests
  have labelBound := labelRange_of_polylog 54000 3 n height (le_refl _)
  have costBound : n + trace.cost ≤ 400000001 * (DynamicOptimality.OPT requests + n) := by
    change trace.cost ≤ 400000000 * (DynamicOptimality.OPT requests + n) at traceBound
    omega
  calc
    cost initial requests ≤ C * (n + trace.cost) * (1 + Nat.clog 2 (height + 2)) := greedyBound
    _ ≤ C * (400000001 * (DynamicOptimality.OPT requests + n)) * (scale * loglogFactor n) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left C costBound) labelBound
    _ = (C * 400000001 * scale) * (DynamicOptimality.OPT requests + n) * loglogFactor n := by ring

end Greedy
