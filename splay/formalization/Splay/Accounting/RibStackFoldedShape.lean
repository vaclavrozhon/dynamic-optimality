import Splay.Accounting.RibStackFoldedPop

namespace Splay.Accounting.OfflineNormalForm.RibStack

open Splay.Tree OfflineConnectedSupport FrontierFolding Digits

theorem ClassFrontier.size {terminalLower lower upper level : ℕ} {terminal : BST terminalLower upper}
    {digits : List Digit} {frontier : SupportFrontier lower upper}
    (classes : ClassFrontier terminal level digits frontier) :
    frontier.tree.size = 2 ^ level * value digits + terminal.size := by
  induction classes with
  | empty => simp [SupportFrontier.tree, value]
  | one first rest ih =>
      have size := first.size_add_one
      simp only [SupportFrontier.tree, BST.size, value, Digit.value, pow_succ] at *
      nlinarith
  | two first second rest ih =>
      have sizeA := first.size_add_one
      have sizeB := second.size_add_one
      simp only [SupportFrontier.tree, BST.size, value, Digit.value, pow_succ] at *
      nlinarith
  | three first second third rest ih =>
      have sizeA := first.size_add_one
      have sizeB := second.size_add_one
      have sizeC := third.size_add_one
      simp only [SupportFrontier.tree, BST.size, value, Digit.value, pow_succ] at *
      nlinarith

theorem ClassFrontier.geometry {terminalLower lower upper level : ℕ} {terminal : BST terminalLower upper}
    {digits : List Digit} {frontier : SupportFrontier lower upper}
    (classes : ClassFrontier terminal level digits frontier) (last : PayloadGeometry terminal) :
    frontier.AllPayloads PayloadGeometry := by
  induction classes with
  | empty => exact last
  | one first rest ih => exact ⟨first.geometry, ih⟩
  | two first second rest ih => exact ⟨first.geometry, second.geometry, ih⟩
  | three first second third rest ih => exact ⟨first.geometry, second.geometry, third.geometry, ih⟩

theorem ClassFrontier.payloadHeight {terminalLower lower upper level : ℕ} {terminal : BST terminalLower upper}
    {digits : List Digit} {frontier : SupportFrontier lower upper}
    (classes : ClassFrontier terminal level digits frontier) (last : terminal.height = 0) :
    frontier.AllPayloads (fun payload => payload.height ≤ 2 * (level + digits.length)) := by
  induction classes with
  | empty => simp [SupportFrontier.AllPayloads, last]
  | one first rest ih => exact ⟨first.height_le.trans (by simp), by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih⟩
  | two first second rest ih => exact ⟨first.height_le.trans (by simp), second.height_le.trans (by simp),
      by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih⟩
  | three first second third rest ih => exact ⟨first.height_le.trans (by simp), second.height_le.trans (by simp),
      third.height_le.trans (by simp), by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih⟩

/-- The maintained virtual stack, with its actual folded class skeleton. -/
inductive FoldedStackShape : {lower upper : ℕ} → ℕ → List Digit → BST lower upper → Prop
  | intro {lower upper level : ℕ} {digits : List Digit} {frontier : SupportFrontier lower upper}
      {tree : BST lower upper}
      (classes : ClassFrontier (.empty upper) level digits frontier)
      (folded : Fold (stackWord false digits) frontier tree) : FoldedStackShape level digits tree

namespace FoldedStackShape

theorem empty (level boundary : ℕ) : FoldedStackShape level [] (.empty boundary) :=
  .intro (.empty level) (by simpa using Fold.last (.empty boundary))

theorem size {lower upper level : ℕ} {digits : List Digit} {tree : BST lower upper}
    (shaped : FoldedStackShape level digits tree) : tree.size = 2 ^ level * value digits := by
  cases shaped with
  | intro classes folded =>
      rename_i frontier
      have size := classes.size
      have bounds := tree.size_add_lower_eq_upper
      have sourceBounds := frontier.tree.size_add_lower_eq_upper
      simp only [BST.size] at size
      omega

theorem geometry {lower upper level : ℕ} {digits : List Digit} {tree : BST lower upper}
    (shaped : FoldedStackShape level digits tree) :
    HasBoundedMinorRibs tree 7 ∧ leftBoundaryDepth tree ≤ 6 ∧ rightBoundaryDepth tree ≤ 6 ∧
      tree.height ≤ 2 * level + 5 * digits.length := by
  cases shaped with
  | intro classes folded =>
      have payloads := classes.geometry (by exact ⟨trivial, by simp [leftBoundaryDepth], by simp [rightBoundaryDepth]⟩)
      have height := folded.height_le (classes.payloadHeight rfl)
      have bounded := foldingWord_boundedRuns false digits
      change BoundedRuns 3 (stackWord false digits) at bounded
      obtain ⟨ribs, left, right⟩ := folded.geometry payloads bounded
      have leftRun := bounded.initial_le true
      have rightRun := bounded.initial_le false
      have nodes := spineNodes_le_length digits
      rw [length_stackWord] at height
      exact ⟨ribs, by omega, by omega, by omega⟩

theorem exists_push {lower root upper level : ℕ} {digits : List Digit}
    {left : BST lower root} {tree : BST (root + 1) upper}
    (shaped : FoldedStackShape level digits tree) (newClass : ClassTree level left) :
    ∃ after : BST lower upper, FoldedStackShape level (Digits.push digits) after ∧
      HasSupportedPath (.node left tree) after (64 * pushCost level digits) (64 * pushCost level digits) := by
  cases shaped with
  | intro classes folded =>
      obtain ⟨result, after, shaped, finalFold, path⟩ := exists_push_folded false classes newClass folded
      exact ⟨after, .intro shaped finalFold, by simpa using path⟩

theorem exists_pop {lower upper level : ℕ} {digits : List Digit} {tree : BST lower upper}
    (shaped : FoldedStackShape level digits tree) (nonempty : digits ≠ []) :
    ∃ (root : ℕ) (left : BST lower root) (after : BST (root + 1) upper),
      ClassTree level left ∧ FoldedStackShape level (Digits.pop digits) after ∧
      HasSupportedPath tree (.node left after) (64 * popCost level digits) (64 * popCost level digits) := by
  cases shaped with
  | intro classes folded =>
      obtain ⟨root, left, result, after, first, shaped, finalFold, path⟩ := exists_pop_folded false classes folded nonempty
      exact ⟨root, left, after, first, .intro shaped finalFold, by simpa using path⟩

theorem height_le_log {lower upper : ℕ} {digits : List Digit} {tree : BST lower upper}
    (shaped : FoldedStackShape 0 digits tree) : tree.height ≤ 5 * Nat.clog 2 (tree.size + 1) := by
  have height := shaped.geometry.2.2.2
  have size := shaped.size
  have levels := length_le_clog digits
  simp only [pow_zero, one_mul] at size
  rw [← size] at levels
  omega

theorem root_zero {lower upper : ℕ} {digits : List Digit} {tree : BST lower upper}
    (shaped : FoldedStackShape 0 digits tree) (nonempty : digits ≠ []) : tree.HasRoot lower := by
  cases shaped with
  | intro classes folded =>
      cases classes with
      | empty => exact False.elim (nonempty rfl)
      | one first rest =>
          cases first
          simp only [stackWord_low, Digit.value, List.replicate_succ, List.replicate_zero,
            List.cons_append, List.nil_append] at folded
          exact folded.root_low
      | two first second rest =>
          cases first
          simp only [stackWord_low, Digit.value, List.replicate_succ, List.replicate_zero,
            List.cons_append, List.nil_append] at folded
          exact folded.root_low
      | three first second third rest =>
          cases first
          simp only [stackWord_low, Digit.value, List.replicate_succ, List.replicate_zero,
            List.cons_append, List.nil_append] at folded
          exact folded.root_low

theorem exists_pop_zero {lower upper : ℕ} {digits : List Digit} {tree : BST lower upper}
    (shaped : FoldedStackShape 0 digits tree) (nonempty : digits ≠ []) :
    ∃ after : BST (lower + 1) upper, FoldedStackShape 0 (Digits.pop digits) after ∧
      HasSupportedPath tree (.node (.empty lower) after) (64 * popCost 0 digits) (64 * popCost 0 digits) := by
  obtain ⟨root, left, after, first, shape, path⟩ := shaped.exists_pop nonempty
  cases first
  exact ⟨after, shape, path⟩

end FoldedStackShape

theorem StackShape.exists_classFrontier {lower upper level : ℕ} {digits : List Digit}
    {tree : BST lower upper} (shaped : StackShape level digits tree) :
    ∃ frontier : SupportFrontier lower upper,
      ClassFrontier (.empty upper) level digits frontier ∧ frontier.tree = tree := by
  induction shaped with
  | empty => exact ⟨.last _, .empty _, rfl⟩
  | one first rest ih =>
      obtain ⟨frontier, classes, same⟩ := ih
      exact ⟨.next _ frontier, .one first classes, by simp [SupportFrontier.tree, same]⟩
  | two first second rest ih =>
      obtain ⟨frontier, classes, same⟩ := ih
      exact ⟨.next _ (.next _ frontier), .two first second classes, by simp [SupportFrontier.tree, same]⟩
  | three first second third rest ih =>
      obtain ⟨frontier, classes, same⟩ := ih
      exact ⟨.next _ (.next _ (.next _ frontier)), .three first second third classes, by simp [SupportFrontier.tree, same]⟩

theorem StackShape.exists_foldedShape {lower upper level : ℕ} {digits : List Digit}
    {tree : BST lower upper} (shaped : StackShape level digits tree) :
    ∃ after : BST lower upper, FoldedStackShape level digits after := by
  obtain ⟨frontier, classes, _⟩ := shaped.exists_classFrontier
  obtain ⟨after, folded⟩ := exists_fold frontier (stackWord false digits) (by rw [length_stackWord, classes.card])
  exact ⟨after, .intro classes folded⟩

end Splay.Accounting.OfflineNormalForm.RibStack
