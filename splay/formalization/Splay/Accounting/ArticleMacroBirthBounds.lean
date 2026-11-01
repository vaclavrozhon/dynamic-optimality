import Splay.Accounting.ArticleMacroHistory

namespace Splay.Accounting

open Splay.Rank Splay.Tree.BST Splay.Lazy Splay.Assumptions.NormalForm
open WholeSplayTemporaryPriorityReduction

theorem articleFullComparisonBirthBudget_mono {first second : ℕ} (bound : first ≤ second) :
    articleFullComparisonBirthBudget first ≤ articleFullComparisonBirthBudget second := by
  unfold articleFullComparisonBirthBudget articleComparisonOwnerBudget
  gcongr

/-- Only the fixed neighbor slack enters the once-per-request creation cost. -/
def articleRequestBirthBudget (slack : ℕ) : ℕ :=
  32 + articleRestorationBirthBudget (2 * slack + 2)

theorem ArticleTemporaryTransferStage.restorationJunctionBound_le
    {n slack : ℕ} {params : Interface.Parameters} {comparison before : BST 0 n}
    {key : Fin n} {kinds : List SplayStepKind} {initial : Lazy.State n}
    (stage : ArticleTemporaryTransferStage params (Snapshot.ofTree comparison) before key kinds initial)
    (root : comparison.HasRoot key.val)
    (neighbors : HasRelevantNeighborRankBound (Snapshot.ofTree comparison) slack) :
    stage.restorationJunctionBound ≤ 2 * slack + 2 := by
  let selection := WholeSplayTemporaryBoundaryGeometry.KeyFocus.boundaryMinimumSelection
    (Snapshot.ofTree comparison).withTruePriority before key
  have selected := stage.setup.boundary_selection_eq
  have leftBound := selection.left_rank_le_neighbor
  have rightBound := selection.right_rank_le_neighbor
  have near := neighbors key
  rw [ofTree_rank_valuePos_eq_zero_of_hasRoot comparison key root, Nat.zero_add] at near
  change 2 * (Snapshot.ofTree comparison).rank selection.left ≤
    2 * (Snapshot.ofTree comparison).rank (leftNullPos key) at leftBound
  change 2 * (Snapshot.ofTree comparison).rank selection.right ≤
    2 * (Snapshot.ofTree comparison).rank (rightNullPos key) at rightBound
  unfold ArticleTemporaryTransferStage.restorationJunctionBound
  dsimp only
  rw [selected.1, selected.2]
  change (Snapshot.ofTree comparison).rank selection.left + (Snapshot.ofTree comparison).rank selection.right + 2 ≤ _
  omega

theorem ArticleCompleteRequest.birthBudget_le
    {n slack : ℕ} {params : Interface.Parameters} {comparison before after : BST 0 n}
    {key : Fin n} {kinds : List SplayStepKind} {initial : Lazy.State n}
    (request : ArticleCompleteRequest params comparison before after key kinds initial)
    (root : comparison.HasRoot key.val)
    (neighbors : HasRelevantNeighborRankBound (Snapshot.ofTree comparison) slack) :
    32 + articleRestorationBirthBudget request.stage.restorationJunctionBound ≤ articleRequestBirthBudget slack := by
  exact Nat.add_le_add_left (articleRestorationBirthBudget_mono
    (request.stage.restorationJunctionBound_le root neighbors)) 32

namespace ArticleMacroHistory

variable {n : ℕ} {params : Interface.Parameters} {first middle last : ArticleCheckpoint n}

@[simp] theorem birthBudget_append (left : ArticleMacroHistory params first middle) (right : ArticleMacroHistory params middle last) :
    (left.append right).birthBudget = left.birthBudget + right.birthBudget := by
  induction left with
  | done => simp [append, birthBudget]
  | next head tail ih => simp [append, birthBudget, ih, Nat.add_assoc]

theorem blocks_le_of_budget (history : ArticleMacroHistory params first last)
    {requestBudget rotationBudget : ℕ}
    (budget : history.birthBudget ≤ requestBudget * history.requests.length + rotationBudget * history.rotationCount) :
    last.state.blocks.length ≤ first.state.blocks.length +
      requestBudget * history.requests.length + rotationBudget * history.rotationCount := by
  have := history.births
  omega

end ArticleMacroHistory
end Splay.Accounting
