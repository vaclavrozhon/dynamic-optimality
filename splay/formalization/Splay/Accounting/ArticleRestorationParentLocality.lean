import Splay.Accounting.ArticleBoundaryRankRestoration
import Splay.Lazy.RankRaiseGeometry

namespace Splay.Accounting

open Splay.Lazy Splay.Lazy.Canonical Splay.Rank Splay.Tree.BST
open WholeSplayTemporaryPriorityReduction WholeSplayTemporaryCoreGeometry

/-- Restoring the two artificial priorities only raises their numeric ranks;
all other interval minima and all ordinary light edges are retained. -/
theorem temporarySnapshot_minimumChangesFrom_true
    {n : ℕ} (comparison : BST 0 n) (key : Fin n)
    (comparisonRoot : comparison.HasRoot key.val)
    (left right : External n) (ordered : left < valuePos key ∧ valuePos key < right) :
    (temporarySnapshot comparison key comparisonRoot left right ordered).MinimumChangesFrom
      (Snapshot.ofTree comparison).withTruePriority {left, right} := by
  classical
  apply Snapshot.minimumChangesFrom_of_rank_raise
  · intro element
    change twoBoundaryTemporaryRank (Snapshot.ofTree comparison) left right element ≤
      truePriority ((Snapshot.ofTree comparison).rank element)
    by_cases atLeft : element = left
    · subst element
      rw [twoBoundaryTemporaryRank_eq_one_left]
      have positive := ofTree_rank_pos_of_ne_valuePos comparison key comparisonRoot left (ne_of_lt ordered.1)
      simp only [truePriority]
      omega
    · by_cases atRight : element = right
      · subst element
        rw [twoBoundaryTemporaryRank_eq_one_right]
        have positive := ofTree_rank_pos_of_ne_valuePos comparison key comparisonRoot right (ne_of_gt ordered.2)
        simp only [truePriority]
        omega
      · rw [twoBoundaryTemporaryRank_eq_truePriority _ _ _ _ ⟨atLeft, atRight⟩]
  · intro element ordinary
    have outside : element ≠ left ∧ element ≠ right := by simpa using ordinary
    exact (twoBoundaryTemporaryRank_eq_truePriority _ _ _ _ outside).symm

namespace ArticleTemporaryTransferStage

variable {n : ℕ} {params : Interface.Parameters} {comparison before : BST 0 n}
  {key : Fin n} {kinds : List SplayStepKind} {initial : Lazy.State n}
  (stage : ArticleTemporaryTransferStage params (Snapshot.ofTree comparison) before key kinds initial)

/-- The rank-restored checkpoint has exactly the old temporary parent map. -/
@[simp]
theorem restoredRanks_parent (after : BST 0 n) :
    (stage.restoredRanks after).view.parent = canonicalParent stage.setup.temporarySnapshot after := rfl

theorem setup_minimumChangesFrom_true (comparisonRoot : comparison.HasRoot key.val) :
    let selection := WholeSplayTemporaryBoundaryGeometry.KeyFocus.boundaryMinimumSelection stage.setup.temporarySnapshot before key
    stage.setup.temporarySnapshot.MinimumChangesFrom (Snapshot.ofTree comparison).withTruePriority
      {selection.left, selection.right} := by
  dsimp only
  have snapshotEq := stage.setup.temporarySnapshot_eq_comparison comparison key comparisonRoot
  have result := temporarySnapshot_minimumChangesFrom_true comparison key comparisonRoot _ _
    (WholeSplayTemporaryBoundaryGeometry.KeyFocus.boundaryMinimumSelection stage.setup.temporarySnapshot before key).ordered
  rw [← snapshotEq] at result
  exact result

/-- Every edge between ordinary vertices is already its final canonical
edge. Thus structural repair is confined to the old boundary heavy paths
and the two boundary singletons. -/
theorem restoredRanks_parent_unchanged (comparisonRoot : comparison.HasRoot key.val)
    (after : BST 0 n) {owner child : Element n}
    (parent : (stage.restoredRanks after).view.parent child = some owner)
    (ordinary :
      let selection := WholeSplayTemporaryBoundaryGeometry.KeyFocus.boundaryMinimumSelection stage.setup.temporarySnapshot before key
      owner ∉ ({selection.left, selection.right} : Finset (Element n)) ∧
        child ∉ ({selection.left, selection.right} : Finset (Element n))) :
    canonicalParent (Snapshot.ofTree comparison).withTruePriority after child = some owner :=
  canonicalParent_eq_of_minimumChangesFrom (stage.setup_minimumChangesFrom_true comparisonRoot)
    after parent ordinary.1 ordinary.2

end ArticleTemporaryTransferStage
end Splay.Accounting
