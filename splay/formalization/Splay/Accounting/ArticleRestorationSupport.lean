import Splay.Accounting.ArticleRestorationParentLocality
import Splay.Accounting.JunctionOwnerSupport
import Splay.Accounting.WholeSplayRestorationGeometry

namespace Splay.Accounting

open Splay.Rank Splay.Tree.BST Splay.Lazy.Canonical
open JunctionBendReduction WholeSplayTemporaryPriorityReduction WholeSplayRestorationGeometry

/-- The direct restoration to fixed doubled true priorities uses no more
junctions than the two established one-boundary restorations. -/
theorem temporarySnapshot_true_junctionCount_le {n : ℕ}
    (comparison : BST 0 n) (key : Fin n) (comparisonRoot : comparison.HasRoot key.val)
    (left right : External n) (ordered : left < valuePos key ∧ valuePos key < right)
    (tree : BST 0 n) :
    junctionCount (temporarySnapshot comparison key comparisonRoot left right ordered)
      (Snapshot.ofTree comparison).withTruePriority tree ≤
        (Snapshot.ofTree comparison).rank left + (Snapshot.ofTree comparison).rank right + 2 := by
  let temporary := temporarySnapshot comparison key comparisonRoot left right ordered
  let middle := rightBoundaryTemporarySnapshot comparison key comparisonRoot right ordered.2
  have scaleEq : junctionCount temporary (Snapshot.ofTree comparison).withTruePriority tree =
      junctionCount temporary (Snapshot.ofTree comparison) tree :=
    junctionCountFrom_eq_of_heavyBranch_eq _ _ _
      (fun node => heavyBranch_withTruePriority_eq _ _ _ _ _) tree (Nat.le_refl n)
  have triangle := junctionCountFrom_triangle temporary middle (Snapshot.ofTree comparison) tree (Nat.le_refl n)
  let restoration := canonicalTwoBoundaryRestoration comparison key comparisonRoot left right ordered tree
  have leftBound := restoration.leftChain.junctions_le_rank_succ
  have rightBound := restoration.rightChain.junctions_le_rank_succ
  change junctionCount temporary (Snapshot.ofTree comparison).withTruePriority tree ≤ _
  rw [scaleEq]
  change junctionCount temporary (Snapshot.ofTree comparison) tree ≤
    junctionCount temporary middle tree + junctionCount middle (Snapshot.ofTree comparison) tree at triangle
  change junctionCount temporary middle tree ≤ (Snapshot.ofTree comparison).rank left + 1 at leftBound
  change junctionCount middle (Snapshot.ofTree comparison) tree ≤ (Snapshot.ofTree comparison).rank right + 1 at rightBound
  omega

/-- Only constantly many owner slots can be affected: both old boundary
owners, the new junction owners, and the old parents of the boundaries. -/
theorem temporarySnapshot_affectedOwnerSupport_card_le {n : ℕ}
    (comparison : BST 0 n) (key : Fin n) (comparisonRoot : comparison.HasRoot key.val)
    (left right : External n) (ordered : left < valuePos key ∧ valuePos key < right)
    (tree : BST 0 n) :
    (affectedOwnerSupport (temporarySnapshot comparison key comparisonRoot left right ordered)
      (Snapshot.ofTree comparison).withTruePriority {left, right} tree).card ≤
        (Snapshot.ofTree comparison).rank left + (Snapshot.ofTree comparison).rank right + 6 := by
  have count := temporarySnapshot_true_junctionCount_le comparison key comparisonRoot left right ordered tree
  have support := affectedOwnerSupport_card_le (temporarySnapshot comparison key comparisonRoot left right ordered)
    (Snapshot.ofTree comparison).withTruePriority {left, right} tree
  have different : left ≠ right := ne_of_lt (ordered.1.trans ordered.2)
  have two : ({left, right} : Finset (External n)).card = 2 := by simp [different]
  rw [two] at support
  omega

namespace ArticleTemporaryTransferStage

variable {n : ℕ} {params : Interface.Parameters} {comparison before : BST 0 n}
  {key : Fin n} {kinds : List SplayStepKind} {initial : Lazy.State n}
  (stage : ArticleTemporaryTransferStage params (Snapshot.ofTree comparison) before key kinds initial)

/-- Explicit finite set of slots that may require preparation for the actual
request suffix; it depends on the actual canonical splay endpoint. -/
noncomputable def restorationOwners (after : BST 0 n) : Finset (External n) :=
  let selection := WholeSplayTemporaryBoundaryGeometry.KeyFocus.boundaryMinimumSelection stage.setup.temporarySnapshot before key
  affectedOwnerSupport stage.setup.temporarySnapshot (Snapshot.ofTree comparison).withTruePriority
    {selection.left, selection.right} after

theorem restorationOwners_card_le (comparisonRoot : comparison.HasRoot key.val) (after : BST 0 n) :
    let selection := WholeSplayTemporaryBoundaryGeometry.KeyFocus.boundaryMinimumSelection stage.setup.temporarySnapshot before key
    (stage.restorationOwners after).card ≤
      (Snapshot.ofTree comparison).rank selection.left + (Snapshot.ofTree comparison).rank selection.right + 6 := by
  dsimp only
  have snapshotEq := stage.setup.temporarySnapshot_eq_comparison comparison key comparisonRoot
  have result := temporarySnapshot_affectedOwnerSupport_card_le comparison key comparisonRoot _ _
    (WholeSplayTemporaryBoundaryGeometry.KeyFocus.boundaryMinimumSelection stage.setup.temporarySnapshot before key).ordered after
  rw [← snapshotEq] at result
  exact result

/-- Every growing or shrinking block at an unmarked owner has exactly its
old ambient child order after restoration. No child enumeration is charged. -/
theorem restoration_other_topDown (comparisonRoot : comparison.HasRoot key.val) (after : BST 0 n)
    (owner : External n) (outside : owner ∉ stage.restorationOwners after) (side : Lazy.Side) :
    (canonicalHeapView (Snapshot.ofTree comparison).withTruePriority after).topDown owner side =
      (stage.restoredRanks after).view.topDown owner side :=
  topDown_eq_of_not_mem_affectedOwnerSupport (stage.setup_minimumChangesFrom_true comparisonRoot) after outside side

end ArticleTemporaryTransferStage
end Splay.Accounting
