import Splay.Accounting.LogHeightHeavySimulation
import Splay.Accounting.LogHeightRibSimulation
import Splay.Accounting.ConstructedPolylogNormalForm
import Splay.Accounting.AdditiveStructuralNormalForm

/-!
# Uniform logarithmic-height structural comparison

The weighted Chocolate stacks make every long-path representation logarithmic
in physical universe size. The height-preserving rib simulation then gives
constant rotation depth, bounded minor ribs, and one universal cost factor
relative to the attained ordinary-BST optimum. Initial representation credits
are paid once through the additive universe-size allowance.
-/

namespace Splay.Accounting.LogHeightNormalForm

open Splay.Tree Splay.Assumptions.NormalForm OfflineConnectedSupport OfflineNormalForm

/-- A physical comparison trace with all constants uniform in `n` and in
the request sequence. Every intermediate rotation is included. -/
theorem exists_structuralLogHeightComparisonTrace {n : ℕ} (accesses : List (Fin n)) :
    ∃ trace : ComparisonTrace n accesses,
      trace.cost ≤ 400000000 * (OfflineOptimum.offlineOptCost accesses + n) ∧
      (∀ time, (trace.state time).height ≤ 30025000 * (Nat.clog 2 (n + 1) + 1)) ∧
      (∀ step, trace.rotationDepth step ≤ 1) ∧
      (∀ time, HasBoundedMinorRibs (trace.state time) 20) := by
  obtain ⟨before, after, rotations, execution, costEq⟩ := OfflineOptimum.exists_optimalExecution_eq accesses
  obtain ⟨heavyInitial, heavyFinal, heavyCount, heavyTrace, heavyCost⟩ :=
    LogHeightChocolate.exists_heavyTrace_of_execution execution
  obtain ⟨initial, final, count, trace, cost⟩ := exists_linearRibbedTrace_of_boundedTrace heavyTrace
  obtain ⟨exactTrace, heights, depths, ribs⟩ := trace.exists_exactTrace
  refine ⟨exactTrace.toComparisonTrace, ?_, ?_, depths, ribs⟩
  · rw [ExactTrace.toComparisonTrace_cost]
    omega
  · intro time
    have bound := heights time
    have linear := linearRibHeight_le (LogHeightChocolate.heavyHeight n)
    have heavy := LogHeightChocolate.heavyHeight_le_log n
    exact bound.trans (by omega)

/-- Fixed structural constants; in particular, the height multiplier does
not depend on the universe size. -/
def bounds : StructuralBounds where
  heightMultiplier := 100000000
  maxRotationDepth := 1
  costMultiplier := 400000000
  heightMultiplier_pos := by decide
  costMultiplier_pos := by decide
  neighborDepthSlack := 20

/-- The paper's full additive structural hypothesis, now discharged by
actual weighted stacks, ordinary rotations, and the existing attained OPT. -/
theorem additiveStructuralHypothesis :
    AdditiveStructuralHypothesis OfflineOptimum.concreteOfflineCostModel := by
  refine ⟨bounds, ?_⟩
  intro n positive accesses
  obtain ⟨trace, cost, height, depth, ribs⟩ := exists_structuralLogHeightComparisonTrace accesses
  refine ⟨trace, ⟨⟨?_, depth⟩, ?_⟩, cost⟩
  · intro time
    have shift := ConstructedPolylogNormalForm.shiftedLog_le n
    have atTime := height time
    change (trace.state time).height ≤ 100000000 * Analysis.stabilizedLog n
    omega
  · intro time
    exact (hasBoundedMinorRibs_iff_relevantNeighborDepth _).mp (ribs time)

end Splay.Accounting.LogHeightNormalForm
