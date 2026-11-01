import Splay.Accounting.WholeSplayContextProtectedTransition
import Splay.Accounting.WholeSplayTranscriptPairingLinks

namespace Splay.Accounting

open Splay.Lazy Splay.Lazy.Canonical Splay.Rank Splay.Tree.BST
open WholeSplayTemporarySpineGeometry WholeSplayTemporaryFocusedSpines
open WholeSplayTemporaryPriorityReduction WholeSplayTemporaryFocusedSpines.FocusedSpines
open WholeSplayTemporaryFocusedTranscript

/-- The same actual transcript constructs the final focused tree and proves
that its protected links are precisely the old protected links together
with all phase links of its genuine zig-zigs. -/
structure ProtectedTranscriptResult {n : ℕ} {snapshot : Snapshot n} {key : Fin n}
    {leftBoundary rightBoundary : External n} {base : SpineBase key leftBoundary rightBoundary}
    {before after : BST 0 n} {execution : SplayExecution key.val before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    (first : FocusedSpines snapshot key leftBoundary rightBoundary base before)
    (transcript : SplayExecutionTranscript key.val execution kinds zig zigZig zigZag)
    extends ProtectedPrefixResult first after (Nat.le_refl n) (transcriptPairingLinks snapshot transcript) where
  run : FocusedTranscript snapshot key leftBoundary rightBoundary base transcript first focused

/-- Construction by the actual chronological transcript; no endpoint
preservation certificate is assumed. -/
theorem nonempty_protectedTranscript {n : ℕ} (comparison : BST 0 n) (key : Fin n)
    (comparisonRoot : comparison.HasRoot key.val) (leftBoundary rightBoundary : External n)
    (ordered : leftBoundary < valuePos key ∧ valuePos key < rightBoundary)
    (base : SpineBase key leftBoundary rightBoundary)
    {before after : BST 0 n} {execution : SplayExecution key.val before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    (transcript : SplayExecutionTranscript key.val execution kinds zig zigZig zigZag)
    (first : FocusedSpines (temporarySnapshot comparison key comparisonRoot leftBoundary rightBoundary ordered)
      key leftBoundary rightBoundary base before) :
    Nonempty (ProtectedTranscriptResult first transcript) := by
  cases transcript with
  | done root =>
      exact ⟨{
        focused := first
        isPrefix := .refl first
        protected_eq := by rw [transcriptPairingLinks_done _ root, Finset.union_empty]
        run := .done root first
      }⟩
  | zig head tail transcript =>
      obtain ⟨headResult⟩ := nonempty_after_zig_withProtectedLinks comparison key comparisonRoot
        leftBoundary rightBoundary ordered base first head (Nat.le_refl n)
      obtain ⟨tailResult⟩ := nonempty_protectedTranscript comparison key comparisonRoot
        leftBoundary rightBoundary ordered base transcript headResult.focused
      exact ⟨{
        focused := tailResult.focused
        isPrefix := .trans headResult.isPrefix tailResult.isPrefix
        protected_eq := by
          rw [tailResult.protected_eq, headResult.protected_eq, transcriptPairingLinks_zig _ head tail transcript, Finset.union_empty]
        run := .zig head tail transcript first headResult.toPrefixResult tailResult.run
      }⟩
  | zigZig head orientation tail transcript =>
      obtain ⟨headResult⟩ := nonempty_after_doubleRotationAt_withProtectedLinks comparison key comparisonRoot
        leftBoundary rightBoundary ordered base first head (Nat.le_refl n)
      obtain ⟨tailResult⟩ := nonempty_protectedTranscript comparison key comparisonRoot
        leftBoundary rightBoundary ordered base transcript headResult.focused
      exact ⟨{
        focused := tailResult.focused
        isPrefix := .trans headResult.isPrefix tailResult.isPrefix
        protected_eq := by
          rw [tailResult.protected_eq, headResult.protected_eq, transcriptPairingLinks_zigZig _ head orientation tail transcript]
          exact Finset.union_assoc _ _ _
        run := .zigZig head orientation tail transcript first headResult.toPrefixResult tailResult.run
      }⟩
  | zigZag head orientation tail transcript =>
      obtain ⟨headResult⟩ := nonempty_after_doubleRotationAt_withProtectedLinks comparison key comparisonRoot
        leftBoundary rightBoundary ordered base first head (Nat.le_refl n)
      obtain ⟨tailResult⟩ := nonempty_protectedTranscript comparison key comparisonRoot
        leftBoundary rightBoundary ordered base transcript headResult.focused
      exact ⟨{
        focused := tailResult.focused
        isPrefix := .trans headResult.isPrefix tailResult.isPrefix
        protected_eq := by
          rw [tailResult.protected_eq, headResult.protected_eq, transcriptPairingLinks_zigZag _ head orientation tail transcript,
            stepPairingLinks_eq_empty_of_zigZag _ orientation, Finset.union_empty]
        run := .zigZag head orientation tail transcript first headResult.toPrefixResult tailResult.run
      }⟩
termination_by kinds.length

end Splay.Accounting
