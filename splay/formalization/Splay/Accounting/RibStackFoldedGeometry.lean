import Splay.Accounting.RibStackOperations
import Splay.Accounting.RibStackFoldingWord

namespace Splay.Accounting.OfflineNormalForm.RibStack

open Splay.Tree OfflineConnectedSupport FrontierFolding Digits

theorem StackShape.folded_root_zero {lower upper : ℕ} {digits : List Digit}
    {before after : BST lower upper} (stacked : StackShape 0 digits before)
    (selected : RootPrefix before) (positive : 0 < selected.card)
    (folded : Fold (foldingWord false digits) selected.frontier after) : after.HasRoot lower := by
  cases stacked with
  | empty => cases selected; simp [RootPrefix.card] at positive
  | one first rest =>
      cases first
      cases selected with
      | none => simp [RootPrefix.card] at positive
      | node left right =>
          cases left
          simp only [foldingWord_cons, Digit.value, List.replicate_succ, List.replicate_zero,
            List.cons_append, List.nil_append, RootPrefix.frontier, SupportFrontier.append] at folded
          exact folded.root_low
  | two first second rest =>
      cases first
      cases selected with
      | none => simp [RootPrefix.card] at positive
      | node left right =>
          cases left
          simp only [foldingWord_cons, Digit.value, List.replicate_succ, List.replicate_zero,
            List.cons_append, List.nil_append, RootPrefix.frontier, SupportFrontier.append] at folded
          exact folded.root_low
  | three first second third rest =>
      cases first
      cases selected with
      | none => simp [RootPrefix.card] at positive
      | node left right =>
          cases left
          simp only [foldingWord_cons, Digit.value, List.replicate_succ, List.replicate_zero,
            List.cons_append, List.nil_append, RootPrefix.frontier, SupportFrontier.append] at folded
          exact folded.root_low

/-- The selected unfolded spine has exactly one node per class-counter unit;
all payloads are the actual class trees of the stack. -/
theorem StackShape.exists_spine {lower upper level : ℕ} {digits : List Digit}
    {tree : BST lower upper} (stacked : StackShape level digits tree) :
    ∃ selected : RootPrefix tree,
      selected.card = spineNodes digits ∧
      selected.frontier.AllPayloads PayloadGeometry ∧
      selected.frontier.AllPayloads (fun payload => payload.height ≤ 2 * (level + digits.length)) := by
  induction stacked with
  | empty => exact ⟨.none _, rfl, ⟨trivial, by simp [leftBoundaryDepth], by simp [rightBoundaryDepth]⟩,
      by change 0 ≤ _; omega⟩
  | @one level lo x hi digits a tail first rest ih =>
      obtain ⟨selected, card, geometry, height⟩ := ih
      refine ⟨.node (.none a) selected, ?_, ?_, ?_⟩
      · simp [RootPrefix.card, spineNodes_cons, Digit.value, card]
      · exact ⟨first.geometry, geometry⟩
      · refine ⟨first.height_le.trans (by simp), ?_⟩
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using height
  | @two level lo x y hi digits a b tail first second rest ih =>
      obtain ⟨selected, card, geometry, height⟩ := ih
      refine ⟨.node (.none a) (.node (.none b) selected), ?_, ?_, ?_⟩
      · simp [RootPrefix.card, spineNodes_cons, Digit.value, card]; omega
      · exact ⟨first.geometry, second.geometry, geometry⟩
      · refine ⟨first.height_le.trans (by simp), second.height_le.trans (by simp), ?_⟩
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using height
  | @three level lo x y z hi digits a b c tail first second third rest ih =>
      obtain ⟨selected, card, geometry, height⟩ := ih
      refine ⟨.node (.none a) (.node (.none b) (.node (.none c) selected)), ?_, ?_, ?_⟩
      · simp [RootPrefix.card, spineNodes_cons, Digit.value, card]; omega
      · exact ⟨first.geometry, second.geometry, third.geometry, geometry⟩
      · refine ⟨first.height_le.trans (by simp), second.height_le.trans (by simp),
          third.height_le.trans (by simp), ?_⟩
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using height

/-- The folded endpoint preserves every hanging class tree, has uniformly
bounded proper ribs and outer spines, and retains logarithmic height. -/
theorem StackShape.exists_folded {lower upper level : ℕ} {digits : List Digit}
    {before : BST lower upper} (stacked : StackShape level digits before) :
    ∃ (a : RootPrefix before) (after : BST lower upper) (b : RootPrefix after),
      a.card = spineNodes digits ∧ b.frontier = a.frontier ∧
      Fold (foldingWord false digits) a.frontier after ∧
      HasBoundedMinorRibs after 7 ∧ leftBoundaryDepth after ≤ 6 ∧ rightBoundaryDepth after ≤ 6 ∧
      after.height ≤ 2 * level + 5 * digits.length := by
  obtain ⟨a, card, payloadGeometry, payloadHeight⟩ := stacked.exists_spine
  obtain ⟨after, folded⟩ := exists_fold a.frontier (foldingWord false digits)
    (by simp [length_foldingWord, card])
  obtain ⟨b, same, _⟩ := folded.exists_selected
  have bounded := foldingWord_boundedRuns false digits
  obtain ⟨ribs, left, right⟩ := folded.geometry payloadGeometry bounded
  have leftRun := bounded.initial_le true
  have rightRun := bounded.initial_le false
  have height := folded.height_le payloadHeight
  have nodes := spineNodes_le_length digits
  rw [length_foldingWord] at height
  exact ⟨a, after, b, card, same, folded, ribs, by omega, by omega, by omega⟩

theorem StackShape.exists_folded_logHeight {lower upper : ℕ} {digits : List Digit}
    {before : BST lower upper} (stacked : StackShape 0 digits before) :
    ∃ (a : RootPrefix before) (after : BST lower upper) (b : RootPrefix after),
      a.card ≤ 3 * Nat.clog 2 (before.size + 1) ∧ b.frontier = a.frontier ∧
      HasBoundedMinorRibs after 7 ∧ leftBoundaryDepth after ≤ 6 ∧ rightBoundaryDepth after ≤ 6 ∧
      after.height ≤ 5 * Nat.clog 2 (before.size + 1) := by
  obtain ⟨a, after, b, card, same, _, ribs, left, right, height⟩ := stacked.exists_folded
  have size := stacked.size
  simp only [pow_zero, one_mul] at size
  have levels := length_le_clog digits
  have nodes := spineNodes_le_length digits
  rw [← size] at levels
  exact ⟨a, after, b, by omega, same, ribs, left, right, by omega⟩

end Splay.Accounting.OfflineNormalForm.RibStack
