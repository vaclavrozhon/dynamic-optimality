import Splay.Accounting.WholeSplayStepPairingLinks
import Splay.Accounting.WholeSplayTemporaryCreationOrdinal

namespace Splay.Accounting

open Splay.Rank Splay.Tree.BST
open WholeSplayTemporaryCreationGeometry
open WholeSplayTemporaryCreationOrdinal

/-- All actual phase links in a single request, with their chronological
occurrences retained in the membership predicate. -/
noncomputable def transcriptPairingLinks {n key lower upper : ℕ} (snapshot : Snapshot n)
    {before after : BST lower upper} {execution : SplayExecution key before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    (transcript : SplayExecutionTranscript key execution kinds zig zigZig zigZag) :
    Finset (External n × External n) := by
  classical
  exact Finset.univ.filter fun link => ∃ ordinal depth stepBefore stepAfter,
    ZigZigOrdinalAt transcript ordinal stepBefore stepAfter depth ∧
      link ∈ stepPairingLinks snapshot depth key stepBefore stepAfter

@[simp]
theorem mem_transcriptPairingLinks {n key lower upper : ℕ} (snapshot : Snapshot n)
    {before after : BST lower upper} {execution : SplayExecution key before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    (transcript : SplayExecutionTranscript key execution kinds zig zigZig zigZag)
    (link : External n × External n) :
    link ∈ transcriptPairingLinks snapshot transcript ↔ ∃ ordinal depth stepBefore stepAfter,
      ZigZigOrdinalAt transcript ordinal stepBefore stepAfter depth ∧
        link ∈ stepPairingLinks snapshot depth key stepBefore stepAfter := by
  classical
  simp only [transcriptPairingLinks, Finset.mem_filter, Finset.mem_univ, true_and]

@[simp]
theorem transcriptPairingLinks_done {n key lower upper : ℕ} (snapshot : Snapshot n)
    {tree : BST lower upper} (root : tree.HasRoot key) :
    transcriptPairingLinks snapshot (.done root) = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro link member
  obtain ⟨_, _, _, _, occurrence, _⟩ := (mem_transcriptPairingLinks _ _ _).mp member
  cases occurrence

@[simp]
theorem transcriptPairingLinks_zig {n key lower upper : ℕ} (snapshot : Snapshot n)
    {before middle after : BST lower upper} {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    (head : Zig key before middle) (tail : SplayExecution key middle after)
    (transcript : SplayExecutionTranscript key tail kinds zig zigZig zigZag) :
    transcriptPairingLinks snapshot (.zig head tail transcript) = transcriptPairingLinks snapshot transcript := by
  ext link
  simp only [mem_transcriptPairingLinks]
  constructor
  · rintro ⟨ordinal, depth, stepBefore, stepAfter, occurrence, member⟩
    cases occurrence with
    | afterZig otherHead otherTail otherTranscript nested =>
        have middleEq := head.after_unique otherHead
        cases middleEq
        exact ⟨ordinal, depth, stepBefore, stepAfter, nested, member⟩
  · rintro ⟨ordinal, depth, stepBefore, stepAfter, occurrence, member⟩
    exact ⟨ordinal, depth, stepBefore, stepAfter, .afterZig head tail transcript occurrence, member⟩

@[simp]
theorem transcriptPairingLinks_zigZig {n key lower upper depth : ℕ} (snapshot : Snapshot n)
    {before middle after : BST lower upper} {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    (head : DoubleRotationAt depth key before middle)
    (orientation : DoubleOrientationAt true (depth := depth) (key := key) before middle)
    (tail : SplayExecution key middle after)
    (transcript : SplayExecutionTranscript key tail kinds zig zigZig zigZag) :
    transcriptPairingLinks snapshot (.zigZig head orientation tail transcript) =
      stepPairingLinks snapshot depth key before middle ∪ transcriptPairingLinks snapshot transcript := by
  ext link
  rw [mem_transcriptPairingLinks, Finset.mem_union, mem_transcriptPairingLinks]
  constructor
  · rintro ⟨ordinal, otherDepth, stepBefore, stepAfter, occurrence, member⟩
    cases occurrence with
    | here otherHead =>
        have middleEq := head.after_unique_any_depth otherHead
        cases middleEq
        have depthEq : depth = otherDepth := by
          have := head.depth_before_eq
          have := otherHead.depth_before_eq
          omega
        subst otherDepth
        exact Or.inl member
    | afterZigZig otherHead _ otherTail otherTranscript nested =>
        have middleEq := head.after_unique_any_depth otherHead
        cases middleEq
        exact Or.inr ⟨_, otherDepth, stepBefore, stepAfter, nested, member⟩
  · rintro (member | ⟨ordinal, otherDepth, stepBefore, stepAfter, occurrence, member⟩)
    · exact ⟨0, depth, before, middle, .here head orientation tail transcript, member⟩
    · exact ⟨ordinal + 1, otherDepth, stepBefore, stepAfter,
        .afterZigZig head orientation tail transcript occurrence, member⟩

@[simp]
theorem transcriptPairingLinks_zigZag {n key lower upper depth : ℕ} (snapshot : Snapshot n)
    {before middle after : BST lower upper} {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    (head : DoubleRotationAt depth key before middle)
    (orientation : DoubleOrientationAt false (depth := depth) (key := key) before middle)
    (tail : SplayExecution key middle after)
    (transcript : SplayExecutionTranscript key tail kinds zig zigZig zigZag) :
    transcriptPairingLinks snapshot (.zigZag head orientation tail transcript) = transcriptPairingLinks snapshot transcript := by
  ext link
  simp only [mem_transcriptPairingLinks]
  constructor
  · rintro ⟨ordinal, depth, stepBefore, stepAfter, occurrence, member⟩
    cases occurrence with
    | afterZigZag otherHead _ otherTail otherTranscript nested =>
        have middleEq := head.after_unique_any_depth otherHead
        cases middleEq
        exact ⟨ordinal, depth, stepBefore, stepAfter, nested, member⟩
  · rintro ⟨ordinal, depth, stepBefore, stepAfter, occurrence, member⟩
    exact ⟨ordinal, depth, stepBefore, stepAfter, .afterZigZag head orientation tail transcript occurrence, member⟩

end Splay.Accounting
