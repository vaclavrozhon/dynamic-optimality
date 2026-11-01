import Splay.Accounting.WholeSplayTemporaryCreationPersistence
import Splay.Accounting.WholeSplayTemporaryFocusedTranscript
import Splay.Accounting.WholeSplayTemporaryTerminalBaseAttachments
import Splay.Accounting.WholeSplayTemporaryCreationOrdinal

namespace Splay.Accounting.WholeSplayTemporaryFocusedZigZigUniqueness

open Splay.Rank
open Splay.Tree.BST
open Splay.Accounting.LocalBendGeometry
open Splay.Accounting.WholeSplayTemporaryPriorityReduction
open Splay.Accounting.WholeSplayTemporaryCoreGeometry
open Splay.Accounting.WholeSplayTemporaryCreationGeometry
open Splay.Accounting.WholeSplayTemporarySpineGeometry
open Splay.Accounting.WholeSplayTemporaryFocusedSpines
open Splay.Accounting.WholeSplayTemporaryCreationSetDecomposition
open Splay.Accounting.WholeSplayTemporaryCreationPersistence.AutomaticCanonicalPersistence
open Splay.Accounting.WholeSplayTemporaryFocusedTranscript
open Splay.Accounting.WholeSplayTemporaryTerminalBaseAttachments

/--
After deleting the two canonical terminal attachments, one chronological
zig-zig ordinal has at most one endpoint-persistent winner.

The local LL/RR classifier supplies the one-element residual after deleting
the two fixed base deltas.  Endpoint persistence turns membership in either
fixed delta into one of the terminal attachment slots, so every
nonattachment winner lies in that local residual.
-/
theorem one_per_zigZig
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
    ∀ slot : Fin transcript.zigZig,
      (persistentCreatedAt transcript
          (temporarySnapshot comparison key comparisonRoot
            leftBoundary rightBoundary ordered)
          slot \
        attachmentSet
          (WholeSplayTemporaryFinalSpineAttachments.attachment
            (before := before) finalLeft finalRight)).card ≤ 1 := by
  classical
  intro slot
  apply Finset.card_le_one_iff.mpr
  intro first second firstMember secondMember
  have firstWinner :=
    mem_persistentCreatedAt_iff.mp
      (Finset.mem_sdiff.mp firstMember).1
  have secondWinner :=
    mem_persistentCreatedAt_iff.mp
      (Finset.mem_sdiff.mp secondMember).1
  rcases firstWinner with
    ⟨firstBefore, firstAfter, firstDepth,
      firstOccurrence, firstCreated⟩
  rcases secondWinner with
    ⟨secondBefore, secondAfter, secondDepth,
      secondOccurrence, secondCreated⟩
  obtain ⟨beforeEq, afterEq, depthEq⟩ :=
    Splay.Accounting.WholeSplayTemporaryCreationOrdinal.ZigZigOrdinalAt.source_unique
      firstOccurrence secondOccurrence
  subst secondBefore
  subst secondAfter
  subst secondDepth
  obtain ⟨sourceFocused, headResult, suffix⟩ :=
    run.exists_source_of_zigZigOrdinalAt firstOccurrence
  have residualCard :=
    zigZig_created_sdiff_fixedBaseDeltas_card_le_one
      comparison key comparisonRoot leftBoundary rightBoundary ordered
      base rightBase_le_n sourceFocused firstOccurrence.geometry.2
      (Nat.le_refl n) none
  have firstNotFixed :
      first.val ∉
        fixedBaseDeltas
          comparison key comparisonRoot leftBoundary rightBoundary
          ordered base rightBase_le_n := by
    intro fixedMember
    rcases Finset.mem_union.mp fixedMember with
      leftMember | rightMember
    · have attached :=
        fixedLeftBaseDelta_attachment_zero
          comparison key comparisonRoot leftBoundary rightBoundary ordered
          finalLeft finalRight first leftMember
      exact
        (Finset.mem_sdiff.mp firstMember).2
          (mem_attachmentSet_iff.mpr
            ⟨(⟨0, by omega⟩ : Fin 2), attached⟩)
    · have attached :=
        fixedRightBaseDelta_attachment_one
          comparison key comparisonRoot leftBoundary rightBoundary ordered
          finalLeft finalRight first rightMember
      exact
        (Finset.mem_sdiff.mp firstMember).2
          (mem_attachmentSet_iff.mpr
            ⟨(⟨1, by omega⟩ : Fin 2), attached⟩)
  have secondNotFixed :
      second.val ∉
        fixedBaseDeltas
          comparison key comparisonRoot leftBoundary rightBoundary
          ordered base rightBase_le_n := by
    intro fixedMember
    rcases Finset.mem_union.mp fixedMember with
      leftMember | rightMember
    · have attached :=
        fixedLeftBaseDelta_attachment_zero
          comparison key comparisonRoot leftBoundary rightBoundary ordered
          finalLeft finalRight second leftMember
      exact
        (Finset.mem_sdiff.mp secondMember).2
          (mem_attachmentSet_iff.mpr
            ⟨(⟨0, by omega⟩ : Fin 2), attached⟩)
    · have attached :=
        fixedRightBaseDelta_attachment_one
          comparison key comparisonRoot leftBoundary rightBoundary ordered
          finalLeft finalRight second rightMember
      exact
        (Finset.mem_sdiff.mp secondMember).2
          (mem_attachmentSet_iff.mpr
            ⟨(⟨1, by omega⟩ : Fin 2), attached⟩)
  have firstResidual :
      first.val ∈
        ((bendsFrom
            (temporarySnapshot comparison key comparisonRoot
              leftBoundary rightBoundary ordered)
            firstAfter (Nat.le_refl n) none \
          bendsFrom
            (temporarySnapshot comparison key comparisonRoot
              leftBoundary rightBoundary ordered)
            firstBefore (Nat.le_refl n) none) \
        fixedBaseDeltas
          comparison key comparisonRoot leftBoundary rightBoundary
          ordered base rightBase_le_n) :=
    Finset.mem_sdiff.mpr
      ⟨by simpa only [bends] using firstCreated, firstNotFixed⟩
  have secondResidual :
      second.val ∈
        ((bendsFrom
            (temporarySnapshot comparison key comparisonRoot
              leftBoundary rightBoundary ordered)
            firstAfter (Nat.le_refl n) none \
          bendsFrom
            (temporarySnapshot comparison key comparisonRoot
              leftBoundary rightBoundary ordered)
            firstBefore (Nat.le_refl n) none) \
        fixedBaseDeltas
          comparison key comparisonRoot leftBoundary rightBoundary
          ordered base rightBase_le_n) :=
    Finset.mem_sdiff.mpr
      ⟨by simpa only [bends] using secondCreated, secondNotFixed⟩
  apply Subtype.ext
  exact
    Finset.card_le_one_iff.mp residualCard
      firstResidual secondResidual

end Splay.Accounting.WholeSplayTemporaryFocusedZigZigUniqueness
