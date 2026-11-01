import Splay.Accounting.WholeSplayTemporaryFocusedSpines
import Splay.Accounting.WholeSplayTemporaryCreationChronology

namespace Splay.Accounting.WholeSplayTemporaryFocusedTranscript

open Splay.Rank
open Splay.Tree.BST
open Splay.Accounting.WholeSplayTemporaryCoreGeometry
open Splay.Accounting.WholeSplayTemporaryCreationGeometry
open Splay.Accounting.WholeSplayTemporaryCreationChronology
open Splay.Accounting.WholeSplayTemporarySpineGeometry
open Splay.Accounting.WholeSplayTemporaryFocusedSpines
open Splay.Accounting.WholeSplayTemporaryPriorityReduction

/--
A chronological splay transcript synchronized with the proof-relevant
focused-spine state before and after every step.

The relation lives in `Prop`, so it can follow the proof-valued
`SplayExecutionTranscript`.  Each nonterminal constructor nevertheless
retains the concrete `PrefixResult` for its head step.  This is the missing
causal link between a chronological creation occurrence and the exact pair
of spine objects present at that occurrence.
-/
inductive FocusedTranscript
    {n : ℕ} (snapshot : Snapshot n) (key : Fin n)
    (leftBoundary rightBoundary : External n)
    (base : SpineBase key leftBoundary rightBoundary) :
    {before after : BST 0 n} →
      {execution : SplayExecution key.val before after} →
        {kinds : List SplayStepKind} → {zig zigZig zigZag : ℕ} →
          (transcript :
            SplayExecutionTranscript key.val execution
              kinds zig zigZig zigZag) →
          FocusedSpines snapshot key leftBoundary rightBoundary base before →
          FocusedSpines snapshot key leftBoundary rightBoundary base after →
          Prop
  | done {tree : BST 0 n}
      (root : tree.HasRoot key.val)
      (focused :
        FocusedSpines snapshot key leftBoundary rightBoundary base tree) :
      FocusedTranscript snapshot key leftBoundary rightBoundary base
        (.done root) focused focused
  | zig {before middle after : BST 0 n}
      {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
      (head : Zig key.val before middle)
      (tail : SplayExecution key.val middle after)
      (tailTranscript :
        SplayExecutionTranscript key.val tail kinds zig zigZig zigZag)
      (focused :
        FocusedSpines snapshot key leftBoundary rightBoundary base before)
      (headResult : FocusedSpines.PrefixResult focused middle)
      {finalFocused :
        FocusedSpines snapshot key leftBoundary rightBoundary base after}
      (tailRun :
        FocusedTranscript snapshot key leftBoundary rightBoundary base
          tailTranscript headResult.focused finalFocused) :
      FocusedTranscript snapshot key leftBoundary rightBoundary base
        (.zig head tail tailTranscript) focused finalFocused
  | zigZig {before middle after : BST 0 n}
      {kinds : List SplayStepKind} {zig zigZig zigZag depth : ℕ}
      (head : DoubleRotationAt depth key.val before middle)
      (orientation :
        DoubleOrientationAt true
          (depth := depth) (key := key.val) before middle)
      (tail : SplayExecution key.val middle after)
      (tailTranscript :
        SplayExecutionTranscript key.val tail kinds zig zigZig zigZag)
      (focused :
        FocusedSpines snapshot key leftBoundary rightBoundary base before)
      (headResult : FocusedSpines.PrefixResult focused middle)
      {finalFocused :
        FocusedSpines snapshot key leftBoundary rightBoundary base after}
      (tailRun :
        FocusedTranscript snapshot key leftBoundary rightBoundary base
          tailTranscript headResult.focused finalFocused) :
      FocusedTranscript snapshot key leftBoundary rightBoundary base
        (.zigZig head orientation tail tailTranscript) focused finalFocused
  | zigZag {before middle after : BST 0 n}
      {kinds : List SplayStepKind} {zig zigZig zigZag depth : ℕ}
      (head : DoubleRotationAt depth key.val before middle)
      (orientation :
        DoubleOrientationAt false
          (depth := depth) (key := key.val) before middle)
      (tail : SplayExecution key.val middle after)
      (tailTranscript :
        SplayExecutionTranscript key.val tail kinds zig zigZig zigZag)
      (focused :
        FocusedSpines snapshot key leftBoundary rightBoundary base before)
      (headResult : FocusedSpines.PrefixResult focused middle)
      {finalFocused :
        FocusedSpines snapshot key leftBoundary rightBoundary base after}
      (tailRun :
        FocusedTranscript snapshot key leftBoundary rightBoundary base
          tailTranscript headResult.focused finalFocused) :
      FocusedTranscript snapshot key leftBoundary rightBoundary base
        (.zigZag head orientation tail tailTranscript) focused finalFocused

namespace FocusedTranscript

/-- The synchronized run composes all stored componentwise spine prefixes. -/
theorem nonempty_isPrefix
    {n : ℕ} {snapshot : Snapshot n} {key : Fin n}
    {leftBoundary rightBoundary : External n}
    {base : SpineBase key leftBoundary rightBoundary}
    {before after : BST 0 n}
    {execution : SplayExecution key.val before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    {transcript :
      SplayExecutionTranscript key.val execution kinds zig zigZig zigZag}
    {initial :
      FocusedSpines snapshot key leftBoundary rightBoundary base before}
    {finalFocused :
      FocusedSpines snapshot key leftBoundary rightBoundary base after}
    (run :
      FocusedTranscript snapshot key leftBoundary rightBoundary base
        transcript initial finalFocused) :
    Nonempty (FocusedSpines.IsPrefix initial finalFocused) := by
  induction run with
  | done =>
      exact ⟨FocusedSpines.IsPrefix.refl _⟩
  | zig _ _ _ _ headResult _ ih
  | zigZig _ _ _ _ _ headResult _ ih
  | zigZag _ _ _ _ _ headResult _ ih =>
      obtain ⟨tailPrefix⟩ := ih
      exact
        ⟨FocusedSpines.IsPrefix.trans
          headResult.isPrefix tailPrefix⟩

/--
Every zig-zig ordinal exposes the exact focused state before that step, the
stored head result after it, and a componentwise prefix from that result to
the terminal focused state.
-/
theorem exists_source_of_zigZigOrdinalAt
    {n : ℕ} {snapshot : Snapshot n} {key : Fin n}
    {leftBoundary rightBoundary : External n}
    {base : SpineBase key leftBoundary rightBoundary}
    {before after : BST 0 n}
    {execution : SplayExecution key.val before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag ordinal depth : ℕ}
    {transcript :
      SplayExecutionTranscript key.val execution kinds zig zigZig zigZag}
    {initial :
      FocusedSpines snapshot key leftBoundary rightBoundary base before}
    {finalFocused :
      FocusedSpines snapshot key leftBoundary rightBoundary base after}
    (run :
      FocusedTranscript snapshot key leftBoundary rightBoundary base
        transcript initial finalFocused)
    {stepBefore stepAfter : BST 0 n}
    (occurrence :
      ZigZigOrdinalAt transcript ordinal
        stepBefore stepAfter depth) :
    ∃ sourceFocused :
        FocusedSpines snapshot key leftBoundary rightBoundary
          base stepBefore,
      ∃ headResult : FocusedSpines.PrefixResult sourceFocused stepAfter,
        Nonempty
          (FocusedSpines.IsPrefix
            headResult.focused finalFocused) := by
  induction run generalizing ordinal depth stepBefore stepAfter with
  | done =>
      cases occurrence
  | zig head tail tailTranscript focused headResult tailRun ih =>
      cases occurrence with
      | afterZig occurrenceHead occurrenceTail
          occurrenceTranscript nested =>
          have middleEq := head.after_unique occurrenceHead
          cases middleEq
          have tailEq : occurrenceTail = tail :=
            Subsingleton.elim _ _
          subst occurrenceTail
          have transcriptEq :
              occurrenceTranscript = tailTranscript :=
            Subsingleton.elim _ _
          subst occurrenceTranscript
          exact ih nested
  | zigZig head orientation tail tailTranscript
      focused headResult tailRun ih =>
      cases occurrence with
      | here occurrenceHead =>
          have middleEq :=
            head.after_unique_any_depth occurrenceHead
          cases middleEq
          exact
            ⟨focused, headResult, tailRun.nonempty_isPrefix⟩
      | afterZigZig occurrenceHead _ occurrenceTail
          occurrenceTranscript nested =>
          have middleEq :=
            head.after_unique_any_depth occurrenceHead
          cases middleEq
          have tailEq : occurrenceTail = tail :=
            Subsingleton.elim _ _
          subst occurrenceTail
          have transcriptEq :
              occurrenceTranscript = tailTranscript :=
            Subsingleton.elim _ _
          subst occurrenceTranscript
          exact ih nested
  | zigZag head orientation tail tailTranscript
      focused headResult tailRun ih =>
      cases occurrence with
      | afterZigZag occurrenceHead _ occurrenceTail
          occurrenceTranscript nested =>
          have middleEq :=
            head.after_unique_any_depth occurrenceHead
          cases middleEq
          have tailEq : occurrenceTail = tail :=
            Subsingleton.elim _ _
          subst occurrenceTail
          have transcriptEq :
              occurrenceTranscript = tailTranscript :=
            Subsingleton.elim _ _
          subst occurrenceTranscript
          exact ih nested

/--
The analogous lookup for a first-creation occurrence of any source kind.
Its indices retain the exact local trees and source classification; this
lemma supplies the focused state and its suffix-to-final prefix.
-/
theorem exists_source_of_firstCreationAt
    {n : ℕ} {snapshot : Snapshot n} {key : Fin n}
    {leftBoundary rightBoundary : External n}
    {base : SpineBase key leftBoundary rightBoundary}
    {before after : BST 0 n}
    {execution : SplayExecution key.val before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    {transcript :
      SplayExecutionTranscript key.val execution kinds zig zigZig zigZag}
    {initial :
      FocusedSpines snapshot key leftBoundary rightBoundary base before}
    {finalFocused :
      FocusedSpines snapshot key leftBoundary rightBoundary base after}
    (run :
      FocusedTranscript snapshot key leftBoundary rightBoundary base
        transcript initial finalFocused)
    {identity : Fin n} {kind : SplayStepKind}
    {stepBefore stepAfter : BST 0 n} {depth : Option ℕ}
    (occurrence :
      FirstCreationAt snapshot identity transcript kind
        stepBefore stepAfter depth) :
    ∃ sourceFocused :
        FocusedSpines snapshot key leftBoundary rightBoundary
          base stepBefore,
      ∃ headResult : FocusedSpines.PrefixResult sourceFocused stepAfter,
        Nonempty
          (FocusedSpines.IsPrefix
            headResult.focused finalFocused) := by
  induction run generalizing kind depth stepBefore stepAfter with
  | done =>
      cases occurrence
  | zig head tail tailTranscript focused headResult tailRun ih =>
      cases occurrence with
      | hereZig occurrenceHead =>
          have middleEq := head.after_unique occurrenceHead
          cases middleEq
          exact
            ⟨focused, headResult, tailRun.nonempty_isPrefix⟩
      | afterZig occurrenceHead occurrenceTail
          occurrenceTranscript _ nested =>
          have middleEq := head.after_unique occurrenceHead
          cases middleEq
          have tailEq : occurrenceTail = tail :=
            Subsingleton.elim _ _
          subst occurrenceTail
          have transcriptEq :
              occurrenceTranscript = tailTranscript :=
            Subsingleton.elim _ _
          subst occurrenceTranscript
          exact ih nested
  | zigZig head orientation tail tailTranscript
      focused headResult tailRun ih =>
      cases occurrence with
      | hereZigZig occurrenceHead =>
          have middleEq :=
            head.after_unique_any_depth occurrenceHead
          cases middleEq
          exact
            ⟨focused, headResult, tailRun.nonempty_isPrefix⟩
      | afterZigZig occurrenceHead _ occurrenceTail
          occurrenceTranscript _ nested =>
          have middleEq :=
            head.after_unique_any_depth occurrenceHead
          cases middleEq
          have tailEq : occurrenceTail = tail :=
            Subsingleton.elim _ _
          subst occurrenceTail
          have transcriptEq :
              occurrenceTranscript = tailTranscript :=
            Subsingleton.elim _ _
          subst occurrenceTranscript
          exact ih nested
  | zigZag head orientation tail tailTranscript
      focused headResult tailRun ih =>
      cases occurrence with
      | hereZigZag occurrenceHead =>
          have middleEq :=
            head.after_unique_any_depth occurrenceHead
          cases middleEq
          exact
            ⟨focused, headResult, tailRun.nonempty_isPrefix⟩
      | afterZigZag occurrenceHead _ occurrenceTail
          occurrenceTranscript _ nested =>
          have middleEq :=
            head.after_unique_any_depth occurrenceHead
          cases middleEq
          have tailEq : occurrenceTail = tail :=
            Subsingleton.elim _ _
          subst occurrenceTail
          have transcriptEq :
              occurrenceTranscript = tailTranscript :=
            Subsingleton.elim _ _
          subst occurrenceTranscript
          exact ih nested

end FocusedTranscript

/--
The canonical temporary snapshot admits a synchronized focused run for
every classified complete execution.
-/
theorem nonempty_focusedTranscript
    {n : ℕ} (comparison : BST 0 n) (key : Fin n)
    (comparisonRoot : comparison.HasRoot key.val)
    (leftBoundary rightBoundary : External n)
    (ordered :
      leftBoundary < valuePos key ∧ valuePos key < rightBoundary)
    (base : SpineBase key leftBoundary rightBoundary)
    {before after : BST 0 n}
    {execution : SplayExecution key.val before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    (transcript :
      SplayExecutionTranscript key.val execution kinds zig zigZig zigZag)
    (initial :
      FocusedSpines
        (temporarySnapshot comparison key comparisonRoot
          leftBoundary rightBoundary ordered)
        key leftBoundary rightBoundary base before) :
    ∃ finalFocused :
        FocusedSpines
          (temporarySnapshot comparison key comparisonRoot
            leftBoundary rightBoundary ordered)
          key leftBoundary rightBoundary base after,
      FocusedTranscript
        (temporarySnapshot comparison key comparisonRoot
          leftBoundary rightBoundary ordered)
        key leftBoundary rightBoundary base
        transcript initial finalFocused := by
  cases transcript with
  | done root =>
      exact ⟨initial, .done root initial⟩
  | @zig lower upper before middle after kinds zig zigZig zigZag
      head tail tailTranscript =>
      obtain ⟨headResult⟩ :=
        FocusedSpines.nonempty_after_splayStep_withPrefix
          comparison key comparisonRoot leftBoundary rightBoundary
          ordered base initial (.zig head) (Nat.le_refl n)
      obtain ⟨finalFocused, tailRun⟩ :=
        nonempty_focusedTranscript
          comparison key comparisonRoot leftBoundary rightBoundary
          ordered base tailTranscript headResult.focused
      exact
        ⟨finalFocused,
          .zig head tail tailTranscript initial headResult tailRun⟩
  | @zigZig depth lower upper before middle after
      kinds zig zigZig zigZag head orientation tail tailTranscript =>
      obtain ⟨headResult⟩ :=
        FocusedSpines.nonempty_after_splayStep_withPrefix
          comparison key comparisonRoot leftBoundary rightBoundary
          ordered base initial (.double head) (Nat.le_refl n)
      obtain ⟨finalFocused, tailRun⟩ :=
        nonempty_focusedTranscript
          comparison key comparisonRoot leftBoundary rightBoundary
          ordered base tailTranscript headResult.focused
      exact
        ⟨finalFocused,
          .zigZig head orientation tail tailTranscript
            initial headResult tailRun⟩
  | @zigZag depth lower upper before middle after
      kinds zig zigZig zigZag head orientation tail tailTranscript =>
      obtain ⟨headResult⟩ :=
        FocusedSpines.nonempty_after_splayStep_withPrefix
          comparison key comparisonRoot leftBoundary rightBoundary
          ordered base initial (.double head) (Nat.le_refl n)
      obtain ⟨finalFocused, tailRun⟩ :=
        nonempty_focusedTranscript
          comparison key comparisonRoot leftBoundary rightBoundary
          ordered base tailTranscript headResult.focused
      exact
        ⟨finalFocused,
          .zigZag head orientation tail tailTranscript
            initial headResult tailRun⟩
termination_by kinds.length

/--
Terminal specialization of `nonempty_focusedTranscript`.

When the completed execution is already indexed by its promoted-key root
shape, the synchronized final focused object cannot retain an outer context.
The result therefore exposes the exact final left and right spines together
with the same chronological run.
-/
theorem exists_terminal_focusedTranscript
    {n : ℕ} (comparison : BST 0 n) (key : Fin n)
    (comparisonRoot : comparison.HasRoot key.val)
    (leftBoundary rightBoundary : External n)
    (ordered :
      leftBoundary < valuePos key ∧ valuePos key < rightBoundary)
    (base : SpineBase key leftBoundary rightBoundary)
    {before : BST 0 n}
    {finalLeftTree : BST 0 key.val}
    {finalRightTree : BST (key.val + 1) n}
    {execution :
      SplayExecution key.val before
        (.node finalLeftTree finalRightTree)}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    (transcript :
      SplayExecutionTranscript key.val execution
        kinds zig zigZig zigZag)
    (initial :
      FocusedSpines
        (temporarySnapshot comparison key comparisonRoot
          leftBoundary rightBoundary ordered)
        key leftBoundary rightBoundary base before) :
    ∃ finalLeft :
        LeftSpine
          (temporarySnapshot comparison key comparisonRoot
            leftBoundary rightBoundary ordered)
          base.leftTree finalLeftTree,
      ∃ finalRight :
          RightSpine
            (temporarySnapshot comparison key comparisonRoot
              leftBoundary rightBoundary ordered)
            base.rightTree finalRightTree,
        FocusedTranscript
          (temporarySnapshot comparison key comparisonRoot
            leftBoundary rightBoundary ordered)
          key leftBoundary rightBoundary base transcript initial
          (.atKey finalLeft finalRight) := by
  obtain ⟨finalFocused, run⟩ :=
    nonempty_focusedTranscript
      comparison key comparisonRoot leftBoundary rightBoundary
      ordered base transcript initial
  cases finalFocused with
  | atKey finalLeft finalRight =>
      exact ⟨finalLeft, finalRight, run⟩
  | leftContext innerFocused contextRight =>
      have bounds := FocusedSpines.key_bounds innerFocused
      omega
  | rightContext contextLeft innerFocused =>
      have bounds := FocusedSpines.key_bounds innerFocused
      omega

end Splay.Accounting.WholeSplayTemporaryFocusedTranscript
