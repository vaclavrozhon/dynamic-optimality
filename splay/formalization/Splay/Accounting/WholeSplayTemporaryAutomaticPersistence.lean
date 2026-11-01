import Splay.Accounting.WholeSplayTemporaryCreationPersistence
import Splay.Accounting.WholeSplayTemporaryFocusedTranscript
import Splay.Accounting.WholeSplayTemporaryFocusedTerminalAttachments
import Splay.Accounting.WholeSplayTemporaryFocusedStepNontriviality
import Splay.Accounting.WholeSplayTemporaryCreationOrdinal
import Splay.Accounting.WholeSplayTemporaryTerminalBaseAttachments
import Splay.Accounting.WholeSplayTemporaryFocusedZigZigUniqueness

namespace Splay.Accounting.WholeSplayTemporaryAutomaticPersistence

open Splay.Rank
open Splay.Tree.BST
open Splay.Accounting.LocalBendGeometry
open Splay.Accounting.WholeSplayTemporaryCoreGeometry
open Splay.Accounting.WholeSplayTemporaryPriorityReduction
open Splay.Accounting.WholeSplayTemporaryCreationGeometry
open Splay.Accounting.WholeSplayTemporarySpineGeometry
open Splay.Accounting.WholeSplayTemporaryFocusedSpines
open Splay.Accounting.WholeSplayTemporaryCreationChronology
open Splay.Accounting.WholeSplayTemporaryCreationSetDecomposition
open Splay.Accounting.WholeSplayTemporaryCreationPersistence
open Splay.Accounting.WholeSplayTemporaryFocusedTranscript
open Splay.Accounting.WholeSplayTemporaryFocusedTerminalAttachments
open Splay.Accounting.WholeSplayTemporaryFocusedStepNontriviality
open Splay.Accounting.WholeSplayTemporaryTerminalBaseAttachments
open Splay.Accounting.WholeSplayTemporaryFocusedZigZigUniqueness

namespace AutomaticCanonicalPersistence

/--
Every endpoint identity whose first chronological source is an ordinary
zig is one of the two canonical terminal base attachments.
-/
theorem zig_first_is_attachment
    {n : ℕ} (comparison : BST 0 n) (key : Fin n)
    (comparisonRoot : comparison.HasRoot key.val)
    (leftBoundary rightBoundary : External n)
    (ordered :
      leftBoundary < valuePos key ∧ valuePos key < rightBoundary)
    (base : SpineBase key leftBoundary rightBoundary)
    (rightBase_le_n : base.rightUpper ≤ n)
    {before : BST 0 n}
    {finalLeftTree : BST 0 key.val}
    {finalRightTree : BST (key.val + 1) n}
    {execution :
      SplayExecution key.val before
        (.node finalLeftTree finalRightTree)}
    (transcript : SplayExecutionTranscriptWitness execution)
    (initial :
      FocusedSpines
        (temporarySnapshot comparison key comparisonRoot
          leftBoundary rightBoundary ordered)
        key leftBoundary rightBoundary base before)
    (finalLeft :
      LeftSpine
        (temporarySnapshot comparison key comparisonRoot
          leftBoundary rightBoundary ordered)
        base.leftTree finalLeftTree)
    (finalRight :
      RightSpine
        (temporarySnapshot comparison key comparisonRoot
          leftBoundary rightBoundary ordered)
        base.rightTree finalRightTree)
    (run :
      FocusedTranscript
        (temporarySnapshot comparison key comparisonRoot
          leftBoundary rightBoundary ordered)
        key leftBoundary rightBoundary base transcript.transcript initial
          (.atKey finalLeft finalRight))
    (identity :
      CreatedIdentity
        (before := before)
        (after := .node finalLeftTree finalRightTree)
        (temporarySnapshot comparison key comparisonRoot
          leftBoundary rightBoundary ordered))
    {stepBefore stepAfter : BST 0 n}
    (occurrence :
      FirstCreationAt
        (temporarySnapshot comparison key comparisonRoot
          leftBoundary rightBoundary ordered)
        identity.val transcript.transcript .zig
          stepBefore stepAfter none) :
    ∃ side,
      WholeSplayTemporaryFinalSpineAttachments.attachment
          finalLeft finalRight side =
        some identity := by
  obtain ⟨sourceFocused, headResult, ⟨suffix⟩⟩ :=
    run.exists_source_of_firstCreationAt occurrence
  have step := occurrence.zig_geometry
  cases step with
  | fromLeft a b c =>
      refine ⟨(⟨1, by omega⟩ : Fin 2), ?_⟩
      apply
        fixedRightBaseDelta_attachment_one
          comparison key comparisonRoot leftBoundary rightBoundary
            ordered finalLeft finalRight identity
      apply
          Splay.Accounting.WholeSplayTemporaryCreationPersistence.AutomaticCanonicalPersistence.zigFromLeft_created_subset_rightBaseDelta
              comparison key comparisonRoot leftBoundary rightBoundary
              ordered base rightBase_le_n
              a b c sourceFocused (Nat.le_refl n) none
      simpa only [bends] using occurrence.mem_local_sdiff
  | fromRight a b c =>
      refine ⟨(⟨0, by omega⟩ : Fin 2), ?_⟩
      apply
        fixedLeftBaseDelta_attachment_zero
          comparison key comparisonRoot leftBoundary rightBoundary
            ordered finalLeft finalRight identity
      apply
          Splay.Accounting.WholeSplayTemporaryCreationPersistence.AutomaticCanonicalPersistence.zigFromRight_created_subset_leftBaseDelta
              comparison key comparisonRoot leftBoundary rightBoundary
              ordered base a b c sourceFocused (Nat.le_refl n) none
      simpa only [bends] using occurrence.mem_local_sdiff

/--
Every endpoint identity whose first chronological source is a zig-zag is
one of the two canonical terminal base attachments.
-/
theorem zigZag_first_is_attachment
    {n : ℕ} (comparison : BST 0 n) (key : Fin n)
    (comparisonRoot : comparison.HasRoot key.val)
    (leftBoundary rightBoundary : External n)
    (ordered :
      leftBoundary < valuePos key ∧ valuePos key < rightBoundary)
    (base : SpineBase key leftBoundary rightBoundary)
    (rightBase_le_n : base.rightUpper ≤ n)
    {before : BST 0 n}
    {finalLeftTree : BST 0 key.val}
    {finalRightTree : BST (key.val + 1) n}
    {execution :
      SplayExecution key.val before
        (.node finalLeftTree finalRightTree)}
    (transcript : SplayExecutionTranscriptWitness execution)
    (initial :
      FocusedSpines
        (temporarySnapshot comparison key comparisonRoot
          leftBoundary rightBoundary ordered)
        key leftBoundary rightBoundary base before)
    (finalLeft :
      LeftSpine
        (temporarySnapshot comparison key comparisonRoot
          leftBoundary rightBoundary ordered)
        base.leftTree finalLeftTree)
    (finalRight :
      RightSpine
        (temporarySnapshot comparison key comparisonRoot
          leftBoundary rightBoundary ordered)
        base.rightTree finalRightTree)
    (run :
      FocusedTranscript
        (temporarySnapshot comparison key comparisonRoot
          leftBoundary rightBoundary ordered)
        key leftBoundary rightBoundary base transcript.transcript initial
          (.atKey finalLeft finalRight))
    (identity :
      CreatedIdentity
        (before := before)
        (after := .node finalLeftTree finalRightTree)
        (temporarySnapshot comparison key comparisonRoot
          leftBoundary rightBoundary ordered))
    {stepBefore stepAfter : BST 0 n} {depth : ℕ}
    (occurrence :
      FirstCreationAt
        (temporarySnapshot comparison key comparisonRoot
          leftBoundary rightBoundary ordered)
        identity.val transcript.transcript .zigZag
          stepBefore stepAfter (some depth)) :
    ∃ side,
      WholeSplayTemporaryFinalSpineAttachments.attachment
          finalLeft finalRight side =
        some identity := by
  obtain ⟨sourceFocused, headResult, ⟨suffix⟩⟩ :=
    run.exists_source_of_firstCreationAt occurrence
  have orientation := occurrence.zigZag_geometry.2
  have classified :=
    Splay.Accounting.WholeSplayTemporaryCreationPersistence.AutomaticCanonicalPersistence.zigZag_created_subset_baseDeltas
        comparison key comparisonRoot leftBoundary rightBoundary ordered
        base rightBase_le_n sourceFocused orientation
        (Nat.le_refl n) none
        (by simpa only [bends] using occurrence.mem_local_sdiff)
  rcases Finset.mem_union.mp classified with leftMember | rightMember
  · refine ⟨(⟨0, by omega⟩ : Fin 2), ?_⟩
    exact
      fixedLeftBaseDelta_attachment_zero
        comparison key comparisonRoot leftBoundary rightBoundary
          ordered finalLeft finalRight identity leftMember
  · refine ⟨(⟨1, by omega⟩ : Fin 2), ?_⟩
    exact
      fixedRightBaseDelta_attachment_one
        comparison key comparisonRoot leftBoundary rightBoundary
          ordered finalLeft finalRight identity rightMember

/--
The synchronized focused transcript now supplies all fields of the
proof-relevant persistence certificate.  In particular, no per-execution
geometric premise remains.
-/
noncomputable def finalSpinePersistence_of_focusedTranscript
    {n : ℕ} (comparison : BST 0 n) (key : Fin n)
    (comparisonRoot : comparison.HasRoot key.val)
    (leftBoundary rightBoundary : External n)
    (ordered :
      leftBoundary < valuePos key ∧ valuePos key < rightBoundary)
    (base : SpineBase key leftBoundary rightBoundary)
    (rightBase_le_n : base.rightUpper ≤ n)
    {before : BST 0 n}
    {finalLeftTree : BST 0 key.val}
    {finalRightTree : BST (key.val + 1) n}
    {execution :
      SplayExecution key.val before
        (.node finalLeftTree finalRightTree)}
    (transcript : SplayExecutionTranscriptWitness execution)
    (initial :
      FocusedSpines
        (temporarySnapshot comparison key comparisonRoot
          leftBoundary rightBoundary ordered)
        key leftBoundary rightBoundary base before)
    (finalLeft :
      LeftSpine
        (temporarySnapshot comparison key comparisonRoot
          leftBoundary rightBoundary ordered)
        base.leftTree finalLeftTree)
    (finalRight :
      RightSpine
        (temporarySnapshot comparison key comparisonRoot
          leftBoundary rightBoundary ordered)
        base.rightTree finalRightTree)
    (run :
      FocusedTranscript
        (temporarySnapshot comparison key comparisonRoot
          leftBoundary rightBoundary ordered)
        key leftBoundary rightBoundary base transcript.transcript initial
          (.atKey finalLeft finalRight)) :
    FinalSpinePersistence transcript
      (temporarySnapshot comparison key comparisonRoot
        leftBoundary rightBoundary ordered) := by
  let attachment :=
    WholeSplayTemporaryFinalSpineAttachments.attachment
      (before := before) finalLeft finalRight
  let provenance :
      ChronologicalProvenanceBridge.FirstSourceProvenance
        transcript
        (temporarySnapshot comparison key comparisonRoot
          leftBoundary rightBoundary ordered)
        attachment := {
    zig_first_is_attachment := by
      intro identity stepBefore stepAfter occurrence
      exact
        zig_first_is_attachment
          comparison key comparisonRoot leftBoundary rightBoundary
          ordered base rightBase_le_n transcript initial
          finalLeft finalRight run identity occurrence
    zigZag_first_is_attachment := by
      intro identity stepBefore stepAfter depth occurrence
      exact
        zigZag_first_is_attachment
          comparison key comparisonRoot leftBoundary rightBoundary
          ordered base rightBase_le_n transcript initial
          finalLeft finalRight run identity occurrence
    one_per_zigZig :=
      one_per_zigZig comparison key comparisonRoot
        leftBoundary rightBoundary ordered base rightBase_le_n
        transcript initial finalLeft finalRight run
  }
  exact
    provenance.toFinalSpinePersistence
      (WholeSplayTemporaryFinalSpineAttachments.attachment_side
        finalLeft finalRight)

/--
Automatic persistence for a complete execution whose terminal promoted-key
root decomposition is explicit.

The theorem chooses the canonical boundary minima, initializes the fixed
spine bases, synchronizes the complete chronological transcript, and then
applies `finalSpinePersistence_of_focusedTranscript`.
-/
theorem nonempty_canonicalFinalSpinePersistence_atRoot
    {n : ℕ} (comparison : BST 0 n) (key : Fin n)
    (comparisonRoot : comparison.HasRoot key.val)
    (before : BST 0 n)
    {finalLeftTree : BST 0 key.val}
    {finalRightTree : BST (key.val + 1) n}
    (execution :
      SplayExecution key.val before
        (.node finalLeftTree finalRightTree)) :
    let selection :=
      WholeSplayTemporaryBoundaryGeometry.KeyFocus.boundaryMinimumSelection
        (Snapshot.ofTree comparison) before key
    let transcript := splayExecutionTranscriptWitness execution
    Nonempty
      (FinalSpinePersistence transcript
        (temporarySnapshot comparison key comparisonRoot
          selection.left selection.right selection.ordered)) := by
  let selection :=
    WholeSplayTemporaryBoundaryGeometry.KeyFocus.boundaryMinimumSelection
      (Snapshot.ofTree comparison) before key
  let snapshot :=
    temporarySnapshot comparison key comparisonRoot
      selection.left selection.right selection.ordered
  let transcript := splayExecutionTranscriptWitness execution
  change Nonempty (FinalSpinePersistence transcript snapshot)
  have placement :
      BoundaryPlacementAt key selection.left selection.right before := by
    simpa only [selection] using
      Splay.Accounting.WholeSplayTemporaryCoreClassification.canonicalBoundaryPlacement
        (Snapshot.ofTree comparison) before key
  obtain ⟨initial⟩ :=
    FocusedSpines.nonempty_initial_ofBoundaryPlacement
      snapshot key selection.left selection.right placement
        (Nat.le_refl n)
  obtain ⟨finalLeft, finalRight, run⟩ :=
    exists_terminal_focusedTranscript
      comparison key comparisonRoot selection.left selection.right
        selection.ordered initial.base transcript.transcript initial.focused
  exact
    ⟨finalSpinePersistence_of_focusedTranscript
      comparison key comparisonRoot selection.left selection.right
      selection.ordered initial.base
      initial.baseFocus.rightUpper_le_upper transcript initial.focused
      finalLeft finalRight run⟩

/--
Every complete splay execution has the canonical temporary-snapshot
persistence certificate.  The final-root decomposition is obtained
automatically from `SplayExecution.hasRoot_after`.
-/
theorem nonempty_canonicalFinalSpinePersistence
    {n : ℕ} (comparison : BST 0 n) (key : Fin n)
    (comparisonRoot : comparison.HasRoot key.val)
    {before after : BST 0 n}
    (execution : SplayExecution key.val before after) :
    let selection :=
      WholeSplayTemporaryBoundaryGeometry.KeyFocus.boundaryMinimumSelection
        (Snapshot.ofTree comparison) before key
    let transcript := splayExecutionTranscriptWitness execution
    Nonempty
      (FinalSpinePersistence transcript
        (temporarySnapshot comparison key comparisonRoot
          selection.left selection.right selection.ordered)) := by
  obtain ⟨finalLeftTree, finalRightTree, rfl⟩ :=
    execution.hasRoot_after
  exact
    nonempty_canonicalFinalSpinePersistence_atRoot
      comparison key comparisonRoot before execution

/-- Chosen proof-relevant form of
`nonempty_canonicalFinalSpinePersistence`. -/
noncomputable def canonicalFinalSpinePersistence
    {n : ℕ} (comparison : BST 0 n) (key : Fin n)
    (comparisonRoot : comparison.HasRoot key.val)
    {before after : BST 0 n}
    (execution : SplayExecution key.val before after) :
    let selection :=
      WholeSplayTemporaryBoundaryGeometry.KeyFocus.boundaryMinimumSelection
        (Snapshot.ofTree comparison) before key
    let transcript := splayExecutionTranscriptWitness execution
    FinalSpinePersistence transcript
      (temporarySnapshot comparison key comparisonRoot
        selection.left selection.right selection.ordered) :=
  Classical.choice
    (nonempty_canonicalFinalSpinePersistence
      comparison key comparisonRoot execution)

end AutomaticCanonicalPersistence

end Splay.Accounting.WholeSplayTemporaryAutomaticPersistence
