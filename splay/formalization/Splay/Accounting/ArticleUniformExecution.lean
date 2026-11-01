import Splay.Accounting.ArticleInitializedExecution
import Splay.Accounting.ConstructedPolylogNormalForm

namespace Splay.Accounting

open Splay.Rank Splay.Tree.BST Splay.Assumptions.NormalForm

/-- Two growing slots, the first two passes exempt, and a one-eighth
matching threshold for the subsequent whole-source pairing passes. -/
def articleShape : Interface.Shape where
  growingLimit := 2
  exemptPasses := 2
  matchingNumerator := 1
  matchingDenominator := 8
  matchingNumerator_pos := by decide
  matchingFraction_le_half := by decide

/-- Fixed doubled priorities require this cap, including temporary ranks. -/
def articleParameters (height : ℕ) : Interface.Parameters where
  toShape := articleShape
  valueBound := Analysis.contractedGap (2 * height + 1)
  valueBound_ge_two := by
    have positive : 0 < Nat.clog 2 (2 * height + 1 + 1) := Nat.clog_pos (by omega) (by omega)
    unfold Analysis.contractedGap Analysis.gapBucket
    omega

theorem articleParameters_valueBound_le (height : ℕ) :
    (articleParameters height).valueBound ≤ 2 * gapBound height := by
  have power := Nat.le_pow_clog (by decide : 1 < 2) (height + 2)
  have doubled : 2 * height + 2 ≤ 2 ^ (Nat.clog 2 (height + 2) + 1) := by
    rw [pow_succ]
    omega
  have logarithm := Nat.clog_le_of_le_pow doubled
  change 1 + Nat.clog 2 (2 * height + 2) ≤ 2 * (1 + Nat.clog 2 (height + 2))
  omega

theorem articleParameters_log_le (height : ℕ) :
    Nat.clog 2 (articleParameters height).valueBound ≤ 2 * gapLog height := by
  have base := Nat.le_pow_clog (by decide : 1 < 2) (max 2 (gapBound height))
  have baseBound : gapBound height ≤ 2 ^ gapLog height := (le_max_right _ _).trans base
  have gap := articleParameters_valueBound_le height
  have power : (articleParameters height).valueBound ≤ 2 ^ (gapLog height + 1) := by
    rw [pow_succ]
    omega
  have logarithm := Nat.clog_le_of_le_pow power
  have positive := gapLog_pos height
  omega

def articleBlockCoefficient (slack depth : ℕ) : ℕ :=
  6 + articleRequestBirthBudget slack + articleFullComparisonBirthBudget depth

theorem ArticleInitializedExecution.blocks_le_coefficient
    {n : ℕ} {params : Interface.Parameters} {bounds : StructuralBounds}
    {accesses : List (Fin n)} {comparison : ComparisonTrace n accesses} {tree : BST 0 n}
    (run : ArticleInitializedExecution params bounds comparison tree) (positive : 0 < n) :
    run.final.blocks.length ≤ articleBlockCoefficient bounds.neighborDepthSlack bounds.maxRotationDepth * (n + comparison.cost) := by
  calc
    run.final.blocks.length ≤ (2 * n + 1) * 2 +
        articleRequestBirthBudget bounds.neighborDepthSlack * accesses.length +
        articleFullComparisonBirthBudget bounds.maxRotationDepth * comparison.rotationCount := run.blocks
    _ ≤ 6 * (n + comparison.cost) +
        articleRequestBirthBudget bounds.neighborDepthSlack * (n + comparison.cost) +
        articleFullComparisonBirthBudget bounds.maxRotationDepth * (n + comparison.cost) := by
      apply Nat.add_le_add
      · apply Nat.add_le_add
        · omega
        · exact Nat.mul_le_mul_left _ (by unfold ComparisonTrace.cost; omega)
      · exact Nat.mul_le_mul_left _ (by unfold ComparisonTrace.cost; omega)
    _ = _ := by unfold articleBlockCoefficient; ring

theorem exists_articleExecution_of_height {n height : ℕ} {accesses : List (Fin n)}
    {comparison : ComparisonTrace n accesses} {bounds : StructuralBounds}
    (normal : IsStructurallyNormal bounds comparison)
    (heightBound : ∀ time, (comparison.state time).height ≤ height) (tree : BST 0 n) :
    Nonempty (ArticleInitializedExecution (articleParameters height) bounds comparison tree) := by
  apply ArticleInitializedExecution.exists_of_normal normal (by exact le_rfl)
  intro time
  apply Analysis.contractedGap_mono
  change 2 * (comparison.state time).height + 1 ≤ 2 * height + 1
  have := heightBound time
  omega

namespace ConstructedPolylogNormalForm

/-- The actual rich run against the already constructed near-optimal trace;
there are no local realization, rank, or initialization hypotheses. -/
noncomputable def articleRun {n : ℕ} (tree : BST 0 n) (accesses : List (Fin n)) :
    ArticleInitializedExecution (articleParameters (comparisonProfile.maxHeight accesses))
      (bounds n) (trace accesses) tree :=
  Classical.choice (exists_articleExecution_of_height (structurallyNormal accesses) (trace_height accesses) tree)

theorem articleRun_blocks {n : ℕ} (tree : BST 0 n) (accesses : List (Fin n)) (positive : 0 < n) :
    (articleRun tree accesses).final.blocks.length ≤ 79855 * (n + (trace accesses).cost) := by
  have bound := (articleRun tree accesses).blocks_le_coefficient positive
  change (articleRun tree accesses).final.blocks.length ≤ articleBlockCoefficient 20 1 * (n + (trace accesses).cost) at bound
  norm_num [articleBlockCoefficient, articleRequestBirthBudget, articleRestorationBirthBudget,
    articleFullComparisonBirthBudget, articleComparisonOwnerBudget] at bound
  exact bound

end ConstructedPolylogNormalForm
end Splay.Accounting
