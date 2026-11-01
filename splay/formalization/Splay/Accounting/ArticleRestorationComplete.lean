import Splay.Accounting.ArticleCanonicalRankChange
import Splay.Accounting.ArticleRestorationSupport

namespace Splay.Accounting

open Splay.Rank Splay.Tree.BST Splay.Lazy Splay.Lazy.Canonical JunctionBendReduction
open WholeSplayTemporaryPriorityReduction

/-- A deliberately coarse quadratic bound in the number of junctions.
It is independent of the ambient tree height and number of keys. -/
def articleRestorationBirthBudget (junctionBound : ℕ) : ℕ :=
  5 * (6 * junctionBound + 2) + 2 * (junctionBound + 4) +
    4 * (junctionBound + 4) * (10 * junctionBound)

theorem articleRestorationBirthBudget_mono {first second : ℕ} (bound : first ≤ second) :
    articleRestorationBirthBudget first ≤ articleRestorationBirthBudget second := by
  unfold articleRestorationBirthBudget
  gcongr

namespace ArticleTemporaryTransferStage

variable {n : ℕ} {params : Interface.Parameters} {comparison before : BST 0 n}
  {key : Fin n} {kinds : List SplayStepKind} {initial : Lazy.State n}
  (stage : ArticleTemporaryTransferStage params (Snapshot.ofTree comparison) before key kinds initial)

noncomputable def restorationJunctionBound : ℕ :=
  let selection := WholeSplayTemporaryBoundaryGeometry.KeyFocus.boundaryMinimumSelection stage.setup.temporarySnapshot before key
  (Snapshot.ofTree comparison).rank selection.left + (Snapshot.ofTree comparison).rank selection.right + 2

theorem restoration_same_root (after : BST 0 n) :
    (canonicalHeapView (Snapshot.ofTree comparison).withTruePriority after).root =
      (canonicalHeapView stage.setup.temporarySnapshot after).root := by
  change canonicalRoot _ after = canonicalRoot _ after
  rw [canonicalRoot_eq_of_rank_eq_zero _ after stage.setup.temporary_rank_zero,
    canonicalRoot_eq_of_rank_eq_zero (Snapshot.ofTree comparison).withTruePriority after
      (element := valuePos key) (by simp [stage.setup.rankZero, truePriority])]

/-- The complete request suffix is now constructed: finite preparation,
one simultaneous canonical block relocation, then one isolated true-rank
restoration. Its endpoint represents the actual final splay tree with fixed
doubled true priorities. Every suffix operation has zero inserts/increases. -/
theorem exists_restoration (comparisonRoot : comparison.HasRoot key.val)
    {after : BST 0 n} {execution : SplayExecution key.val before after} {zig zigZig zigZag : ℕ}
    (transcript : SplayExecutionTranscript key.val execution kinds zig zigZig zigZag) :
    Nonempty (ArticleCanonicalRankChange params (stage.canonicalFinal after)
      (Snapshot.ofTree comparison).withTruePriority after
      (articleRestorationBirthBudget stage.restorationJunctionBound)) := by
  classical
  let selection := WholeSplayTemporaryBoundaryGeometry.KeyFocus.boundaryMinimumSelection stage.setup.temporarySnapshot before key
  let changed : Finset (Element n) := {selection.left, selection.right}
  let trueSnapshot := (Snapshot.ofTree comparison).withTruePriority
  have ordinary : ∀ element ∉ changed, trueSnapshot.rank element = stage.setup.temporarySnapshot.rank element := by
    intro element outside
    have different : element ≠ selection.left ∧ element ≠ selection.right := by simpa [changed] using outside
    rw [stage.setup.temporarySnapshot_eq_comparison comparison key comparisonRoot]
    exact (twoBoundaryTemporaryRank_eq_truePriority (Snapshot.ofTree comparison) selection.left selection.right element different).symm
  have changedOwners : changed ⊆ stage.restorationOwners after := Finset.subset_union_left
  obtain ⟨restoration⟩ := ArticleCanonicalRankChange.exists_of_support stage.setup.temporarySnapshot trueSnapshot after
    (stage.canonical_represents comparisonRoot transcript) changed (stage.restorationOwners after)
    (stage.restoration_same_root after) ordinary changedOwners
    (fun owner outside side => topDown_eq_of_not_mem_affectedOwnerSupport
      (stage.setup_minimumChangesFrom_true comparisonRoot) after outside side)
    (stage.setup_minimumChangesFrom_true comparisonRoot) (Finset.Subset.refl _)
  apply Nonempty.intro
  apply restoration.withBudget
  let j := stage.restorationJunctionBound
  have junctions : junctionCount stage.setup.temporarySnapshot trueSnapshot after ≤ j := by
    have bound := temporarySnapshot_true_junctionCount_le comparison key comparisonRoot selection.left selection.right selection.ordered after
    rw [← stage.setup.temporarySnapshot_eq_comparison comparison key comparisonRoot] at bound
    exact bound
  have changedCard : changed.card ≤ 2 := by
    simpa [changed] using Finset.card_insert_le selection.left {selection.right}
  have exceptions := junctionExceptionsFrom_card_le stage.setup.temporarySnapshot trueSnapshot after (Nat.le_refl n)
  have selected : (junctionExceptionsFrom stage.setup.temporarySnapshot trueSnapshot after (Nat.le_refl n) ∪ changed).card ≤ 6 * j + 2 := by
    have unionBound := Finset.card_union_le (junctionExceptionsFrom stage.setup.temporarySnapshot trueSnapshot after (Nat.le_refl n)) changed
    change (junctionExceptionsFrom stage.setup.temporarySnapshot trueSnapshot after (Nat.le_refl n)).card ≤
      6 * junctionCount stage.setup.temporarySnapshot trueSnapshot after at exceptions
    omega
  have owners : (stage.restorationOwners after).card ≤ j + 4 := by
    have bound := stage.restorationOwners_card_le comparisonRoot after
    change (stage.restorationOwners after).card ≤
      (Snapshot.ofTree comparison).rank selection.left + (Snapshot.ofTree comparison).rank selection.right + 6 at bound
    dsimp only [j, restorationJunctionBound]
    omega
  have cuts : (relocationCutsFrom stage.setup.temporarySnapshot trueSnapshot after (Nat.le_refl n)).card ≤ 10 * j := by
    have bound := relocationCutsFrom_card_le stage.setup.temporarySnapshot trueSnapshot after (Nat.le_refl n)
    change (relocationCutsFrom stage.setup.temporarySnapshot trueSnapshot after (Nat.le_refl n)).card ≤
      10 * junctionCount stage.setup.temporarySnapshot trueSnapshot after at bound
    omega
  change _ ≤ 5 * (6 * j + 2) + 2 * (j + 4) + 4 * (j + 4) * (10 * j)
  gcongr

end ArticleTemporaryTransferStage
end Splay.Accounting
