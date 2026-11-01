import Splay.Accounting.ArticleUniformPairingBound
import Splay.Accounting.ArticleGlobalBends

namespace Splay.Accounting

/-- The doubled-priority gap cap differs by only a uniform factor from the
height factor in the public statement. -/
theorem articleParameters_factor_le (height : ℕ) :
    (articleParameters height).valueBound *
      (Nat.clog 2 (articleParameters height).valueBound + 1) ^ 2 ≤
        18 * Analysis.heightFactor height := by
  have gap := articleParameters_valueBound_le height
  have logarithm := articleParameters_log_le height
  have positive := gapLog_pos height
  have logBound : Nat.clog 2 (articleParameters height).valueBound + 1 ≤ 3 * gapLog height := by omega
  calc
    _ ≤ (2 * gapBound height) * (3 * gapLog height) ^ 2 :=
      Nat.mul_le_mul gap (Nat.pow_le_pow_left logBound 2)
    _ = _ := by unfold gapLog gapBound Analysis.heightFactor; ring

namespace ConstructedPolylogNormalForm

/-- Actual zig-zigs are paid by the run, while actual zig-zags are controlled
by the already constructed chronological bend argument. -/
theorem articleRun_cost_le_pairings {n : ℕ} (tree : Splay.Tree.BST 0 n) (accesses : List (Fin n)) :
    concreteSplayCost tree accesses ≤
      4 * (Interface.totalActivity (articleRun tree accesses).operations + (articleRun tree accesses).boundaryCount) +
        268 * (n + (trace accesses).cost) := by
  have zig := (articleRun tree accesses).zigZigs
  have zigZag := articleRun_zigZags tree accesses
  have cost := concreteSplayTranscript_cost_decomposition tree accesses
  have volume : accesses.length + (trace accesses).rotationCount ≤ n + (trace accesses).cost := by
    unfold Splay.Assumptions.NormalForm.ComparisonTrace.cost
    omega
  nlinarith

/-- The complete core analysis for the physically constructed comparison
trace, with a single constant uniform in the tree size and access sequence. -/
theorem hasCoreAnalysisBound :
    HasCoreAnalysisBound OfflineOptimum.concreteOfflineCostModel comparisonProfile := by
  obtain ⟨constant, constantPositive, pairingBound⟩ := articleRun_activity_add_boundary
  refine ⟨72 * constant + 268, by omega, ?_⟩
  intro n positive tree accesses
  have pairings := pairingBound n tree accesses positive
  have factor := articleParameters_factor_le (comparisonProfile.maxHeight accesses)
  have cost := articleRun_cost_le_pairings tree accesses
  have factorPositive : 0 < Analysis.heightFactor (comparisonProfile.maxHeight accesses) := by
    change 0 < gapBound (comparisonProfile.maxHeight accesses) * gapLog (comparisonProfile.maxHeight accesses) ^ 2
    have := gapBound_pos (comparisonProfile.maxHeight accesses)
    have := gapLog_pos (comparisonProfile.maxHeight accesses)
    positivity
  have pairingHeight : Interface.totalActivity (articleRun tree accesses).operations +
      (articleRun tree accesses).boundaryCount ≤
        18 * constant * (n + (trace accesses).cost) * Analysis.heightFactor (comparisonProfile.maxHeight accesses) := by
    calc
      _ ≤ constant * (n + (trace accesses).cost) *
          (articleParameters (comparisonProfile.maxHeight accesses)).valueBound *
            (Nat.clog 2 (articleParameters (comparisonProfile.maxHeight accesses)).valueBound + 1) ^ 2 := pairings
      _ = constant * (n + (trace accesses).cost) *
          ((articleParameters (comparisonProfile.maxHeight accesses)).valueBound *
            (Nat.clog 2 (articleParameters (comparisonProfile.maxHeight accesses)).valueBound + 1) ^ 2) := by ring
      _ ≤ constant * (n + (trace accesses).cost) *
          (18 * Analysis.heightFactor (comparisonProfile.maxHeight accesses)) := Nat.mul_le_mul_left _ factor
      _ = _ := by ring
  have lowerFactor : 268 * (n + (trace accesses).cost) ≤
      268 * (n + (trace accesses).cost) * Analysis.heightFactor (comparisonProfile.maxHeight accesses) := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (268 * (n + (trace accesses).cost)) factorPositive
  change concreteSplayCost tree accesses ≤ (72 * constant + 268) *
    ((trace accesses).cost + n) * Analysis.heightFactor (comparisonProfile.maxHeight accesses)
  calc
    _ ≤ 4 * (Interface.totalActivity (articleRun tree accesses).operations + (articleRun tree accesses).boundaryCount) +
        268 * (n + (trace accesses).cost) := cost
    _ ≤ 4 * (18 * constant * (n + (trace accesses).cost) * Analysis.heightFactor (comparisonProfile.maxHeight accesses)) +
        268 * (n + (trace accesses).cost) * Analysis.heightFactor (comparisonProfile.maxHeight accesses) :=
      Nat.add_le_add (Nat.mul_le_mul_left 4 pairingHeight) lowerFactor
    _ = _ := by ring

end ConstructedPolylogNormalForm
end Splay.Accounting

namespace Splay

/-- The manuscript's competitiveness theorem for the concrete standard splay
algorithm and the attained root-based offline rotation optimum. -/
theorem concreteTargetBound : TargetBound Accounting.OfflineOptimum.concreteOfflineCostModel :=
  Accounting.ConstructedPolylogNormalForm.targetBound_of_core
    Accounting.ConstructedPolylogNormalForm.hasCoreAnalysisBound

end Splay
