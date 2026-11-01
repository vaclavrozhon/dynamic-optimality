import Splay.Accounting.RibStackExecution
import Splay.Accounting.RibStackFoldedGeometry

namespace Splay.Accounting.OfflineNormalForm.RibStack

open Splay.Tree OfflineConnectedSupport Digits

theorem value_run_pushes (count : ℕ) (digits : List Digit) :
    value (run (List.replicate count Operation.push) digits) = value digits + count := by
  induction count generalizing digits with
  | zero => simp [run]
  | succ count ih =>
      simp only [List.replicate_succ, run, Operation.apply, ih, value_push]
      omega

/-- Every finite stack length has a represented class counter and a real
unfolded stack, obtained by the already verified push implementation. -/
theorem exists_initialized_stack_with_capacity (count capacity : ℕ) (fits : count ≤ capacity) :
    ∃ (digits : List Digit) (tree : BST (capacity - count) capacity) (support rotations : ℕ),
      StackShape 0 digits tree ∧ value digits = count ∧
      StackExecution (.empty capacity) (List.replicate count Operation.push) tree support rotations ∧
      support ≤ 112 * count ∧ rotations ≤ 112 * count := by
  obtain ⟨lowerAfter, support, rotations, tree, stacked, execution, supportBound, rotationBound⟩ :=
    exists_stackExecution_linear (StackShape.empty 0 capacity) (List.replicate count Operation.push) (by simpa using fits)
  have valueEq : value (run (List.replicate count Operation.push) []) = count := by
    simpa [value] using value_run_pushes count []
  have size := stacked.size
  have interval := tree.size_add_lower_eq_upper
  simp only [pow_zero, one_mul, valueEq] at size
  have lowerEq : lowerAfter = capacity - count := by omega
  subst lowerAfter
  exact ⟨_, tree, support, rotations, stacked, valueEq, execution,
    by simpa [BST.size] using supportBound, by simpa [BST.size] using rotationBound⟩

theorem exists_initialized_stack (count : ℕ) :
    ∃ (digits : List Digit) (tree : BST 0 count) (support rotations : ℕ),
      StackShape 0 digits tree ∧ value digits = count ∧
      StackExecution (.empty count) (List.replicate count Operation.push) tree support rotations ∧
      support ≤ 112 * count ∧ rotations ≤ 112 * count := by
  have initialized := exists_initialized_stack_with_capacity count count le_rfl
  rw [Nat.sub_self] at initialized
  exact initialized

theorem spineNodes_pos {digits : List Digit} (nonempty : digits ≠ []) : 0 < spineNodes digits := by
  cases digits with
  | nil => exact False.elim (nonempty rfl)
  | cons digit digits => cases digit <;> simp [Digit.value]

/-- A folded initial stack exists for every length. Its first key is exposed
when nonempty, as required by the actual stack interface. -/
theorem exists_initialized_folded_stack (count : ℕ) :
    ∃ (digits : List Digit) (before after : BST 0 count)
      (a : RootPrefix before) (b : RootPrefix after),
      StackShape 0 digits before ∧ value digits = count ∧
      a.card = spineNodes digits ∧ b.frontier = a.frontier ∧
      FrontierFolding.Fold (foldingWord false digits) a.frontier after ∧
      HasBoundedMinorRibs after 7 ∧ leftBoundaryDepth after ≤ 6 ∧ rightBoundaryDepth after ≤ 6 ∧
      after.height ≤ 5 * Nat.clog 2 (count + 1) ∧ (0 < count → after.HasRoot 0) := by
  obtain ⟨digits, before, _, _, stacked, valueEq, _, _, _⟩ := exists_initialized_stack count
  obtain ⟨a, after, b, card, same, folded, ribs, left, right, height⟩ := stacked.exists_folded
  have levels := length_le_clog digits
  rw [valueEq] at levels
  refine ⟨digits, before, after, a, b, stacked, valueEq, card, same, folded,
    ribs, left, right, by omega, ?_⟩
  intro positive
  have nonempty : digits ≠ [] := by intro empty; subst digits; simp [value] at valueEq; omega
  have nodes := spineNodes_pos nonempty
  exact stacked.folded_root_zero a (by omega) folded

end Splay.Accounting.OfflineNormalForm.RibStack
