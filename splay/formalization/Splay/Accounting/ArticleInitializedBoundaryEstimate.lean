import Splay.Accounting.ArticleMacroBoundaryCredit
import Splay.Accounting.ArticleUniformExecution

namespace Splay.Accounting

open Splay.Lazy Splay.Lazy.Canonical Splay.Rank Splay.Tree.BST Splay.Assumptions.NormalForm

private theorem boundaryCredit_le_capacity_length {n cutoff : ℕ} (state : Interface.State n) :
    Interface.boundaryCredit cutoff state ≤ Interface.boundaryCreditCapacity cutoff * state.blocks.length := by
  unfold Interface.boundaryCredit
  induction state.blocks with
  | nil => simp
  | cons block blocks ih =>
    have bound := Interface.boundaryBlockCredit_le cutoff block
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.mul_add, Nat.mul_one]
    omega

/-- The complete run's boundary estimate depends only on the historical
creation budget and its own actual interface activity. -/
theorem ArticleInitializedExecution.boundary_estimate
    {n cutoff : ℕ} {params : Interface.Parameters} {bounds : StructuralBounds}
    {accesses : List (Fin n)} {comparison : ComparisonTrace n accesses} {tree : BST 0 n}
    (run : ArticleInitializedExecution params bounds comparison tree) (positive : 0 < n)
    (exempt : params.exemptPasses = 2) (numerator : params.matchingNumerator = 1)
    (denominator : params.matchingDenominator = 8) :
    cutoff * (2 * run.boundaryCount) ≤
      4 * cutoff * Interface.boundaryCreditCapacity cutoff *
        articleBlockCoefficient bounds.neighborDepthSlack bounds.maxRotationDepth * (n + comparison.cost) +
      16 * Interface.totalActivity run.operations := by
  let start := canonicalState (Snapshot.ofTree comparison.initialTree).withTruePriority tree
  have zero : Interface.GrowingPassCountZero start.toInterface := by
    intro id block found growing
    have found' : start.toInterface.blocks[id]? = some block := found
    obtain ⟨rich, richFound, blockEq⟩ := Option.map_eq_some_iff.mp (by
      simpa only [State.toInterface, List.getElem?_map] using found')
    obtain ⟨placement, _, richEq⟩ := List.mem_map.mp (List.mem_of_getElem? richFound)
    subst rich
    subst block
    rfl
  have paid := run.execution.history.boundary_credit_estimate exempt numerator denominator
    (cutoff := cutoff) zero (canonicalState_passedBlocksUnbroken _ _)
  have initialCredit := boundaryCredit_le_capacity_length (cutoff := cutoff) start.toInterface
  simp only [State.toInterface, List.length_map] at initialCredit
  change Interface.boundaryCredit cutoff start.toInterface ≤
    Interface.boundaryCreditCapacity cutoff * start.blocks.length at initialCredit
  have born : start.blocks.length + run.execution.history.birthBudget ≤
      articleBlockCoefficient bounds.neighborDepthSlack bounds.maxRotationDepth * (n + comparison.cost) := by
    have budget := run.execution.budget
    have count : start.blocks.length = (2 * n + 1) * 2 := canonicalState_blocks_length _ _
    rw [count]
    calc
      (2 * n + 1) * 2 + run.execution.history.birthBudget ≤ (2 * n + 1) * 2 +
          articleRequestBirthBudget bounds.neighborDepthSlack * accesses.length +
          articleFullComparisonBirthBudget bounds.maxRotationDepth * comparison.rotationCount := by omega
      _ ≤ 6 * (n + comparison.cost) +
          articleRequestBirthBudget bounds.neighborDepthSlack * (n + comparison.cost) +
          articleFullComparisonBirthBudget bounds.maxRotationDepth * (n + comparison.cost) := by
        apply Nat.add_le_add
        · apply Nat.add_le_add
          · omega
          · exact Nat.mul_le_mul_left _ (by unfold ComparisonTrace.cost; omega)
        · exact Nat.mul_le_mul_left _ (by unfold ComparisonTrace.cost; omega)
      _ = _ := by unfold articleBlockCoefficient; ring
  have initialWeighted := Nat.mul_le_mul_left (4 * cutoff) initialCredit
  have bornWeighted := Nat.mul_le_mul_left (4 * cutoff * Interface.boundaryCreditCapacity cutoff) born
  change cutoff * (2 * run.boundaryCount) + _ ≤
    4 * cutoff * Interface.boundaryCredit cutoff start.toInterface +
      4 * cutoff * Interface.boundaryCreditCapacity cutoff * run.execution.history.birthBudget +
      16 * Interface.totalActivity (eraseOperations run.execution.history.events) at paid
  rw [run.activity_eq]
  nlinarith

theorem ConstructedPolylogNormalForm.articleRun_boundary_estimate
    {n cutoff : ℕ} (tree : BST 0 n) (accesses : List (Fin n)) (positive : 0 < n) :
    cutoff * (2 * (articleRun tree accesses).boundaryCount) ≤
      319420 * cutoff * Interface.boundaryCreditCapacity cutoff * (n + (trace accesses).cost) +
        16 * Interface.totalActivity (articleRun tree accesses).operations := by
  have bound := (articleRun tree accesses).boundary_estimate (cutoff := cutoff) positive rfl rfl rfl
  change cutoff * (2 * (articleRun tree accesses).boundaryCount) ≤
    4 * cutoff * Interface.boundaryCreditCapacity cutoff * articleBlockCoefficient 20 1 * (n + (trace accesses).cost) +
      16 * Interface.totalActivity (articleRun tree accesses).operations at bound
  norm_num [articleBlockCoefficient, articleRequestBirthBudget, articleRestorationBirthBudget,
    articleFullComparisonBirthBudget, articleComparisonOwnerBudget] at bound
  nlinarith

end Splay.Accounting
