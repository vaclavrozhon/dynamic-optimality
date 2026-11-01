import Splay.Accounting.OfflineRibBoundedSteps
import Splay.Accounting.OfflineHeavySimulation

namespace Splay.Accounting.OfflineConnectedSupport

open Splay.Tree OfflineNormalForm

theorem simulate_ribTrace {n height rotations : ℕ} {side : Bool} {accesses : List (Fin n)}
    {before after actual : BST 0 n} (trace : BoundedTrace height 1 accesses before after rotations)
    (representation : RibRepresentation n side before actual) :
    ∃ (resultTree : BST 0 n) (result : RibRepresentation n side after resultTree) (count : ℕ),
      RibbedTrace (ribHeight n height) 1 20 accesses actual resultTree count ∧
      count + 4 * result.potential ≤ 4 * representation.potential + 21552 * rotations + 3584 * accesses.length := by
  induction trace generalizing actual with
  | done tree height_le =>
      have bounded := representation.height_le_of_bound (by simp) height_le
      exact ⟨_, representation, 0, .done _ (by dsimp [ribHeight]; omega) (representation.geometry.1.mono (by decide)), by simp⟩
  | rotate rotation depth_le height_le tail ih =>
      obtain ⟨middle, middleRep, firstCount, firstTrace, firstCost⟩ :=
        representation.exists_boundedRotation rotation depth_le height_le tail.initial_height
      obtain ⟨resultTree, result, restCount, restTrace, restCost⟩ := ih middleRep
      exact ⟨resultTree, result, firstCount + restCount, by simpa using firstTrace.append restTrace, by omega⟩
  | serve root tail ih =>
      obtain ⟨middle, middleRep, firstCount, firstTrace, firstCost⟩ :=
        representation.exists_boundedService tail.initial_height _ root
      obtain ⟨resultTree, result, restCount, restTrace, restCost⟩ := ih middleRep
      refine ⟨resultTree, result, firstCount + restCount, by simpa using firstTrace.append restTrace, ?_⟩
      simp only [List.length_cons]
      omega

/-- The complete second simulator, including its initialization credit. -/
theorem exists_ribbedTrace_of_boundedTrace {n height rotations : ℕ} {accesses : List (Fin n)}
    {before after : BST 0 n} (trace : BoundedTrace height 1 accesses before after rotations) :
    ∃ (initial final : BST 0 n) (count : ℕ),
      RibbedTrace (ribHeight n height) 1 20 accesses initial final count ∧
      accesses.length + count ≤ 21552 * (accesses.length + rotations + n) := by
  obtain ⟨initial, ⟨representation⟩⟩ := RibRepresentation.exists_representation n false before (by simp)
  obtain ⟨final, finalRep, count, result, cost⟩ := simulate_ribTrace trace representation
  have credit := representation.potential_le_size
  simp only [BST.size_eq_upper] at credit
  exact ⟨initial, final, count, result, by omega⟩

theorem ribHeight_heavyHeight_le_logCubed (n : ℕ) :
    ribHeight n (heavyHeight n) ≤ 2000 * (Nat.clog 2 (n + 1) + 1) ^ 3 := by
  have height := heavyHeight_le_logSquared n
  have multiplied := Nat.mul_le_mul_right (5 * Nat.clog 2 (n + 1)) height
  dsimp [ribHeight, ribUnitCost]
  nlinarith [Nat.zero_le ((Nat.clog 2 (n + 1)) ^ 2), Nat.zero_le ((Nat.clog 2 (n + 1)) ^ 3)]

/-- Unconditional structural normalization with the polylogarithmic height
sufficient for the unchanged target factor. Every request and physical
intermediate state belongs to the exported comparison trace. -/
theorem exists_structuralPolylogComparisonTrace {n : ℕ} (accesses : List (Fin n)) :
    ∃ trace : Splay.Assumptions.NormalForm.ComparisonTrace n accesses,
      trace.cost ≤ 400000000 * (OfflineOptimum.offlineOptCost accesses + n) ∧
      (∀ time, (trace.state time).height ≤ 2000 * (Nat.clog 2 (n + 1) + 1) ^ 3) ∧
      (∀ step, trace.rotationDepth step ≤ 1) ∧
      (∀ time, HasBoundedMinorRibs (trace.state time) 20) := by
  obtain ⟨before, after, rotations, execution, costEq⟩ := OfflineOptimum.exists_optimalExecution_eq accesses
  obtain ⟨heavyInitial, heavyFinal, heavyCount, heavyTrace, heavyCost⟩ := exists_heavyTrace_of_execution execution
  obtain ⟨initial, final, count, trace, cost⟩ := exists_ribbedTrace_of_boundedTrace heavyTrace
  obtain ⟨exactTrace, heights, depths, ribs⟩ := trace.exists_exactTrace
  refine ⟨exactTrace.toComparisonTrace, ?_, fun time => (heights time).trans (ribHeight_heavyHeight_le_logCubed n), depths, ribs⟩
  rw [ExactTrace.toComparisonTrace_cost]
  omega

end Splay.Accounting.OfflineConnectedSupport
