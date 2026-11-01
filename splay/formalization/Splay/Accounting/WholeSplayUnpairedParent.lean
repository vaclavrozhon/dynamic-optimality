import Splay.Accounting.WholeSplayRootHeapLinks
import Splay.Lazy.ComparisonRotationPreparation

namespace Splay.Accounting

open Splay.Lazy Splay.Lazy.Canonical Splay.Rank Splay.Tree.BST
open WholeSplayTemporarySpineGeometry WholeSplayTemporaryFocusedSpines
open WholeSplayTemporaryPriorityReduction WholeSplayTemporaryCoreGeometry WholeSplayTemporaryCoreClassification

/-- Once the key reaches the BST root, its canonical heap children are
exactly the two fixed artificial boundary minima. -/
theorem SplayExecutionTranscript.final_root_heapLink_iff {n : ℕ} (comparison : BST 0 n) (key : Fin n)
    (comparisonRoot : comparison.HasRoot key.val) (leftBoundary rightBoundary : External n)
    (ordered : leftBoundary < valuePos key ∧ valuePos key < rightBoundary)
    {before after : BST 0 n} {execution : SplayExecution key.val before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    (transcript : SplayExecutionTranscript key.val execution kinds zig zigZig zigZag)
    (placement : BoundaryPlacementAt key leftBoundary rightBoundary before) (child : External n) :
    (valuePos key, child) ∈ heapLinks
      (temporarySnapshot comparison key comparisonRoot leftBoundary rightBoundary ordered) after (Nat.le_refl n) ↔
        child = leftBoundary ∨ child = rightBoundary := by
  obtain ⟨left, right, rfl⟩ := execution.hasRoot_after
  let snapshot := temporarySnapshot comparison key comparisonRoot leftBoundary rightBoundary ordered
  obtain ⟨initial⟩ := FocusedSpines.nonempty_initial_ofBoundaryPlacement snapshot key
    leftBoundary rightBoundary placement (Nat.le_refl n)
  obtain ⟨result⟩ := nonempty_protectedTranscript comparison key comparisonRoot leftBoundary rightBoundary
    ordered initial.base transcript initial.focused
  cases result.focused with
  | atKey leftSpine rightSpine =>
      have leftEq := (leftSpine_owner_eq_base leftSpine).trans
        (leftBaseOwner_eq_boundary comparison key comparisonRoot leftBoundary rightBoundary ordered initial.base)
      have rightEq := (rightSpine_owner_eq_base rightSpine).trans
        (rightBaseOwner_eq_boundary comparison key comparisonRoot leftBoundary rightBoundary ordered initial.base _)
      rw [accessed_root_heapLink_iff _ _ _ _ _ (temporarySnapshot_rank_valuePos _ _ _ _ _ _), leftEq, rightEq]
  | leftContext inner right => have := inner.key_bounds; omega
  | rightContext left inner => have := inner.key_bounds; omega

/-- Every unpaired original root child other than the boundaries is moved to
exactly the boundary on its own side of the accessed key in the canonical
final heap. No transfer endpoint is assumed in this statement. -/
theorem SplayExecutionTranscript.final_unpaired_parent {n : ℕ} (comparison : BST 0 n) (key : Fin n)
    (comparisonRoot : comparison.HasRoot key.val) (leftBoundary rightBoundary : External n)
    (ordered : leftBoundary < valuePos key ∧ valuePos key < rightBoundary)
    {before after : BST 0 n} {execution : SplayExecution key.val before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    (transcript : SplayExecutionTranscript key.val execution kinds zig zigZig zigZag)
    (placement : BoundaryPlacementAt key leftBoundary rightBoundary before)
    (child : External n)
    (originalParent : canonicalParent
      (temporarySnapshot comparison key comparisonRoot leftBoundary rightBoundary ordered) before child = some (valuePos key))
    (notLeft : child ≠ leftBoundary) (notRight : child ≠ rightBoundary)
    (unpaired : ∀ owner, (owner, child) ∉ transcriptPairingLinks
      (temporarySnapshot comparison key comparisonRoot leftBoundary rightBoundary ordered) transcript) :
    canonicalParent (temporarySnapshot comparison key comparisonRoot leftBoundary rightBoundary ordered) after child =
      some (if child < valuePos key then leftBoundary else rightBoundary) := by
  let snapshot := temporarySnapshot comparison key comparisonRoot leftBoundary rightBoundary ordered
  have rankZero : snapshot.rank (valuePos key) = 0 := temporarySnapshot_rank_valuePos _ _ _ _ _ _
  have childNeRoot : child ≠ valuePos key := by
    intro equal
    have rootEq := canonicalRoot_eq_of_rank_eq_zero snapshot before rankZero
    rw [equal, ← rootEq, canonicalParent_canonicalRoot] at originalParent
    contradiction
  obtain ⟨owner, parent⟩ := exists_canonicalParent_eq_some_of_ne_root snapshot after
    (by simpa only [canonicalRoot_eq_of_rank_eq_zero snapshot after rankZero] using childNeRoot)
  have link := (mem_heapLinks_iff_parent snapshot after owner child).mpr parent
  have ownerNeRoot : owner ≠ valuePos key := by
    intro equal
    rw [equal] at link
    have boundary := (transcript.final_root_heapLink_iff comparison key comparisonRoot leftBoundary rightBoundary ordered placement child).mp link
    exact boundary.elim notLeft notRight
  have ownerBoundary : owner = leftBoundary ∨ owner = rightBoundary := by
    by_contra neither
    have notBoundaries : owner ≠ leftBoundary ∧ owner ≠ rightBoundary := not_or.mp neither
    have inherited := (transcript.final_heapLinks comparison key comparisonRoot leftBoundary rightBoundary ordered placement).2
      (owner, child) link ownerNeRoot notBoundaries.1 notBoundaries.2
    rcases Finset.mem_union.mp inherited with old | paired
    · have oldParent := (mem_heapLinks_iff_parent snapshot before owner child).mp (Finset.mem_filter.mp old).1
      have equal := Option.some.inj (oldParent.symm.trans originalParent)
      exact ownerNeRoot equal
    · exact unpaired owner paired
  obtain ⟨left, right, afterEq⟩ := execution.hasRoot_after
  rw [afterEq] at link
  have sameSide := heapLink_sameSide_of_accessed_root snapshot key left right (Nat.le_refl n) rankZero link ownerNeRoot
  rw [parent]
  apply congrArg some
  by_cases leftSide : child < valuePos key
  · rw [if_pos leftSide]
    rcases ownerBoundary with left | right
    · exact left
    · rcases sameSide with bothLeft | bothRight
      · have wrong := bothLeft.1
        rw [right] at wrong
        exact (lt_asymm wrong ordered.2).elim
      · exact (lt_asymm leftSide bothRight.2).elim
  · rw [if_neg leftSide]
    rcases ownerBoundary with left | right
    · rcases sameSide with bothLeft | bothRight
      · exact (leftSide bothLeft.2).elim
      · have wrong := bothRight.1
        rw [left] at wrong
        exact (lt_asymm wrong ordered.1).elim
    · exact right

end Splay.Accounting
