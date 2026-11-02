import Splay.Accounting.LogHeightHeavyBoundedSteps
import Splay.Accounting.OfflineConnectedBoundedTrace

namespace Splay.Accounting.OfflineConnectedSupport.LogHeightChocolate

open Splay.Tree OfflineNormalForm

/-- Telescope the real local macros against one persistent representation
history, retaining the exact request order and all intermediate bounds. -/
theorem simulate_boundedTrace {n height rotations : ℕ} {accesses : List (Fin n)}
    {before after actual : BST 0 n}
    (trace : BoundedTrace height 1 accesses before after rotations)
    (representation : HeavyRepresentation n before actual) :
    ∃ (resultTree : BST 0 n) (result : HeavyRepresentation n after resultTree) (count : ℕ),
      BoundedTrace (heavyHeight n) 1 accesses actual resultTree count ∧
      count + 4 * result.potential ≤
        4 * representation.potential + 3712 * rotations + 920 * accesses.length := by
  induction trace generalizing actual with
  | done tree height_le =>
      have heightBound := representation.height_le_capacity (by simp)
      exact ⟨_, representation, 0, .done _ (by dsimp [heavyHeight]; omega), by simp⟩
  | rotate rotation depth_le height_le tail ih =>
      obtain ⟨middle, middleRep, firstCount, firstTrace, firstCost⟩ :=
        representation.exists_boundedRotation rotation depth_le
      obtain ⟨resultTree, result, restCount, restTrace, restCost⟩ := ih middleRep
      refine ⟨resultTree, result, firstCount + restCount, ?_, by omega⟩
      simpa using firstTrace.append restTrace
  | serve root tail ih =>
      obtain ⟨middle, middleRep, firstCount, firstTrace, firstCost⟩ :=
        representation.exists_boundedService _ root
      obtain ⟨resultTree, result, restCount, restTrace, restCost⟩ := ih middleRep
      refine ⟨resultTree, result, firstCount + restCount, ?_, ?_⟩
      · simpa using firstTrace.append restTrace
      · simp only [List.length_cons]
        omega

/-- Full height normalization from an arbitrary original execution. This
stage imposes no assumption on an offline simulator or a stack realization. -/
theorem exists_heavyTrace_of_execution {n rotations : ℕ} {accesses : List (Fin n)}
    {before after : BST 0 n} (execution : OfflineOptimum.Execution accesses before after rotations) :
    ∃ (initial final : BST 0 n) (count : ℕ),
      BoundedTrace (heavyHeight n) 1 accesses initial final count ∧
      accesses.length + count ≤ 16000 * (accesses.length + rotations + n) := by
  obtain ⟨reorderedAfter, reorderedRotations, support, connected, rotationBound, supportBound⟩ :=
    exists_connectedReordered execution
  obtain ⟨shallowCount, shallowTrace, shallowCost⟩ := connected.exists_boundedTrace
  obtain ⟨initial, ⟨representation⟩⟩ := HeavyRepresentation.exists_representation n before (by simp)
  obtain ⟨final, finalRep, count, trace, cost⟩ := simulate_boundedTrace shallowTrace representation
  have credit := representation.potential_le_size
  simp only [BST.size_eq_upper] at credit
  exact ⟨initial, final, count, trace, by omega⟩

theorem heavyHeight_le_log (n : ℕ) :
    heavyHeight n ≤ 1200 * (Nat.clog 2 (n + 1) + 1) := by
  dsimp [heavyHeight, heavyUnitCost, stackUnitCost]
  nlinarith [Nat.zero_le (Nat.clog 2 (n + 1))]

/-- An attained offline optimum has a shallow comparison trace of logarithmic height and constant-factor cost, with a linear initialization term. -/
theorem exists_logHeightComparisonTrace {n : ℕ} (accesses : List (Fin n)) :
    ∃ trace : Splay.Assumptions.NormalForm.ComparisonTrace n accesses,
      trace.cost ≤ 16000 * (OfflineOptimum.offlineOptCost accesses + n) ∧
      (∀ time, (trace.state time).height ≤ 1200 * (Nat.clog 2 (n + 1) + 1)) ∧
      (∀ step, trace.rotationDepth step ≤ 1) := by
  obtain ⟨before, after, rotations, execution, costEq⟩ := OfflineOptimum.exists_optimalExecution_eq accesses
  obtain ⟨initial, final, count, trace, cost⟩ := exists_heavyTrace_of_execution execution
  obtain ⟨exactTrace, heights, depths⟩ := trace.exists_exactTrace
  refine ⟨exactTrace.toComparisonTrace, ?_, fun time => (heights time).trans (heavyHeight_le_log n), depths⟩
  rw [ExactTrace.toComparisonTrace_cost]
  omega

end Splay.Accounting.OfflineConnectedSupport.LogHeightChocolate
