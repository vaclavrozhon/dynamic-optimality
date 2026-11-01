import Splay.Accounting.OfflineRibSimulation
import Splay.Accounting.PolylogHeightBridge
import Splay.Accounting.Certificate

namespace Splay.Accounting.ConstructedPolylogNormalForm

open Splay.Assumptions.NormalForm OfflineConnectedSupport OfflineNormalForm

theorem shiftedLog_le (n : ℕ) : Nat.clog 2 (n + 1) + 1 ≤ 3 * Analysis.stabilizedLog n := by
  have upper : n ≤ 2 ^ Analysis.stabilizedLog n :=
    (le_max_right 2 n).trans (Nat.le_pow_clog (by decide) (max 2 n))
  have powerPositive : 0 < 2 ^ Analysis.stabilizedLog n := pow_pos (by decide) _
  have shifted : Nat.clog 2 (n + 1) ≤ Analysis.stabilizedLog n + 1 :=
    Nat.clog_le_of_le_pow (by rw [pow_succ]; omega)
  have positive := Analysis.stabilizedLog_pos n
  omega

/-- A fixed choice of the already constructed physical comparison traces. -/
noncomputable def trace {n : ℕ} (accesses : List (Fin n)) : ComparisonTrace n accesses :=
  Classical.choose (exists_structuralPolylogComparisonTrace accesses)

theorem trace_cost {n : ℕ} (accesses : List (Fin n)) :
    (trace accesses).cost ≤ 400000000 * (OfflineOptimum.offlineOptCost accesses + n) :=
  (Classical.choose_spec (exists_structuralPolylogComparisonTrace accesses)).1

theorem trace_height {n : ℕ} (accesses : List (Fin n)) (time) :
    ((trace accesses).state time).height ≤ 54000 * (Analysis.stabilizedLog n) ^ 3 := by
  have height := (Classical.choose_spec (exists_structuralPolylogComparisonTrace accesses)).2.1 time
  have powers := Nat.pow_le_pow_left (shiftedLog_le n) 3
  change ((trace accesses).state time).height ≤ _ at height
  calc
    ((trace accesses).state time).height ≤ 2000 * (Nat.clog 2 (n + 1) + 1) ^ 3 := height
    _ ≤ 2000 * (3 * Analysis.stabilizedLog n) ^ 3 := Nat.mul_le_mul_left _ powers
    _ = _ := by ring

theorem trace_depth {n : ℕ} (accesses : List (Fin n)) (step) : (trace accesses).rotationDepth step ≤ 1 :=
  (Classical.choose_spec (exists_structuralPolylogComparisonTrace accesses)).2.2.1 step

theorem trace_ribs {n : ℕ} (accesses : List (Fin n)) (time) :
    HasBoundedMinorRibs ((trace accesses).state time) 20 :=
  (Classical.choose_spec (exists_structuralPolylogComparisonTrace accesses)).2.2.2 time

theorem trace_neighbors {n : ℕ} (accesses : List (Fin n)) (time) :
    HasRelevantNeighborDepthBound ((trace accesses).state time) 20 :=
  (hasBoundedMinorRibs_iff_relevantNeighborDepth _).mp (trace_ribs accesses time)

/-- The existing local structural API may be used at each universe size.
Only its height multiplier varies; depth and neighbor slack remain universal. -/
def bounds (n : ℕ) : StructuralBounds where
  heightMultiplier := 54000 * (Analysis.stabilizedLog n) ^ 2
  maxRotationDepth := 1
  costMultiplier := 400000000
  heightMultiplier_pos := by have := Analysis.stabilizedLog_pos n; positivity
  costMultiplier_pos := by decide
  neighborDepthSlack := 20

theorem structurallyNormal {n : ℕ} (accesses : List (Fin n)) :
    IsStructurallyNormal (bounds n) (trace accesses) := by
  refine ⟨⟨?_, trace_depth accesses⟩, trace_neighbors accesses⟩
  intro time
  simpa only [bounds, pow_succ, Nat.mul_assoc] using trace_height accesses time

noncomputable def comparisonProfile : ComparisonProfile where
  cost := fun accesses => (trace accesses).cost
  maxHeight := fun {n} _ => 54000 * (Analysis.stabilizedLog n) ^ 3

theorem hasNormalFormBound : HasNormalFormBound OfflineOptimum.concreteOfflineCostModel comparisonProfile := by
  exact ⟨400000000, by decide, fun n _ accesses => trace_cost accesses⟩

theorem hasHeightFactorBound : HasHeightFactorBound comparisonProfile :=
  comparisonProfile.hasHeightFactorBound_of_polylog 54000 3 (fun _ _ _ => le_rfl)

theorem requestCostDominates : RequestCostDominates comparisonProfile := by
  intro n positive accesses
  simp [comparisonProfile, ComparisonTrace.cost]

/-- Compose the core accounting bound with this constructed comparison
family. `ConcreteTargetBound` supplies the unconditional core theorem. -/
theorem targetBound_of_core
    (core : HasCoreAnalysisBound OfflineOptimum.concreteOfflineCostModel comparisonProfile) :
    TargetBound OfflineOptimum.concreteOfflineCostModel :=
  targetBound_of_conditional_layers _ comparisonProfile hasNormalFormBound core hasHeightFactorBound

end Splay.Accounting.ConstructedPolylogNormalForm
