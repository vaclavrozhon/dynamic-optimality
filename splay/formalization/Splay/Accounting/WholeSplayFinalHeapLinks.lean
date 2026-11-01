import Splay.Accounting.WholeSplayInitialProtectedLinks
import Splay.Accounting.WholeSplayProtectedTranscript

namespace Splay.Accounting

open Splay.Lazy Splay.Lazy.Canonical Splay.Rank Splay.Tree.BST
open WholeSplayTemporarySpineGeometry WholeSplayTemporaryFocusedSpines
open WholeSplayTemporaryPriorityReduction WholeSplayTemporaryCoreGeometry
open WholeSplayTemporaryCoreClassification

/-- The fixed left base has precisely the selected artificial boundary owner. -/
theorem leftBaseOwner_eq_boundary {n : ℕ} (comparison : BST 0 n) (key : Fin n)
    (comparisonRoot : comparison.HasRoot key.val) (leftBoundary rightBoundary : External n)
    (ordered : leftBoundary < valuePos key ∧ valuePos key < rightBoundary)
    (base : SpineBase key leftBoundary rightBoundary) :
    subtreeOwner (temporarySnapshot comparison key comparisonRoot leftBoundary rightBoundary ordered)
      base.leftTree (Nat.le_of_lt key.isLt) = leftBoundary := by
  symm
  apply Snapshot.intervalMin_unique
  apply left_isIntervalMin comparison key comparisonRoot leftBoundary rightBoundary _ _ ordered
  · exact ⟨base.left_lower_mem, base.left_upper_mem⟩
  · change 2 * key.val < 2 * key.val + 1
    omega

/-- The mirrored fixed base has precisely the selected right boundary owner. -/
theorem rightBaseOwner_eq_boundary {n : ℕ} (comparison : BST 0 n) (key : Fin n)
    (comparisonRoot : comparison.HasRoot key.val) (leftBoundary rightBoundary : External n)
    (ordered : leftBoundary < valuePos key ∧ valuePos key < rightBoundary)
    (base : SpineBase key leftBoundary rightBoundary) (bound : base.rightUpper ≤ n) :
    subtreeOwner (temporarySnapshot comparison key comparisonRoot leftBoundary rightBoundary ordered)
      base.rightTree bound = rightBoundary := by
  symm
  apply Snapshot.intervalMin_unique
  apply right_isIntervalMin comparison key comparisonRoot leftBoundary rightBoundary _ _ ordered
  · exact ⟨base.right_lower_mem, base.right_upper_mem⟩
  · change 2 * key.val + 1 < 2 * (key.val + 1)
    omega

/-- Every original non-root link and every actual phase link survives to the
canonical final heap. Conversely, all final links outside the accessed owner
and the two transfer owners come from exactly those two sources. -/
theorem SplayExecutionTranscript.final_heapLinks {n : ℕ} (comparison : BST 0 n) (key : Fin n)
    (comparisonRoot : comparison.HasRoot key.val) (leftBoundary rightBoundary : External n)
    (ordered : leftBoundary < valuePos key ∧ valuePos key < rightBoundary)
    {before after : BST 0 n} {execution : SplayExecution key.val before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    (transcript : SplayExecutionTranscript key.val execution kinds zig zigZig zigZag)
    (placement : BoundaryPlacementAt key leftBoundary rightBoundary before) :
    let snapshot := temporarySnapshot comparison key comparisonRoot leftBoundary rightBoundary ordered
    let inherited := (heapLinks snapshot before (Nat.le_refl n)).filter (fun link => link.1 ≠ valuePos key)
    inherited ∪ transcriptPairingLinks snapshot transcript ⊆ heapLinks snapshot after (Nat.le_refl n) ∧
      ∀ link ∈ heapLinks snapshot after (Nat.le_refl n),
        link.1 ≠ valuePos key → link.1 ≠ leftBoundary → link.1 ≠ rightBoundary →
          link ∈ inherited ∪ transcriptPairingLinks snapshot transcript := by
  dsimp only
  let snapshot := temporarySnapshot comparison key comparisonRoot leftBoundary rightBoundary ordered
  obtain ⟨initial⟩ := FocusedSpines.nonempty_initial_ofBoundaryPlacement snapshot key
    leftBoundary rightBoundary placement (Nat.le_refl n)
  let first := initial.baseFocus.initialFocused snapshot (Nat.le_refl n)
  obtain ⟨result⟩ := nonempty_protectedTranscript comparison key comparisonRoot
    leftBoundary rightBoundary ordered initial.base transcript first
  have rankZero : snapshot.rank (valuePos key) = 0 := temporarySnapshot_rank_valuePos _ _ _ _ _ _
  have initialEq := initial.baseFocus.initialFocused_protected_eq snapshot (Nat.le_refl n) rankZero
  have finalEq := result.protected_eq
  rw [initialEq] at finalEq
  constructor
  · rw [← finalEq]
    exact focusedProtectedLinks_subset result.focused (Nat.le_refl n)
  · intro link member notAccessed notLeft notRight
    rw [← finalEq]
    apply heapLink_protected_of_owner_ne result.focused (Nat.le_refl n) rankZero member notAccessed
    · simpa only [leftBaseOwner_eq_boundary comparison key comparisonRoot leftBoundary rightBoundary ordered initial.base] using notLeft
    · simpa only [rightBaseOwner_eq_boundary comparison key comparisonRoot leftBoundary rightBoundary ordered initial.base] using notRight

end Splay.Accounting
