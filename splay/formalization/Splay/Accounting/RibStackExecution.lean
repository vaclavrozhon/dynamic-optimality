import Splay.Accounting.RibStackOperations

namespace Splay.Accounting.OfflineNormalForm.RibStack

open Splay.Tree OfflineConnectedSupport Digits

theorem StackShape.exists_pop_zero {lower upper : ℕ} {digits : List Digit}
    {tree : BST lower upper} (stacked : StackShape 0 digits tree) (nonempty : digits ≠ []) :
    ∃ result : BST (lower + 1) upper, StackShape 0 (Digits.pop digits) result ∧
      HasSupportedPath tree (.node (.empty lower) result)
        (16 * popCost 0 digits) (16 * popCost 0 digits) := by
  obtain ⟨root, left, result, classed, shape, path⟩ := stacked.exists_pop nonempty
  cases classed
  exact ⟨result, shape, path⟩

/-- A transcript of actual stack rotations. Pushing inserts the next smaller
key above the old root; popping removes that key only once it is exposed.
The two costs sum actual support cardinalities and actual path lengths. -/
inductive StackExecution {upper : ℕ} :
    {lowerBefore lowerAfter : ℕ} → BST lowerBefore upper → List Operation →
      BST lowerAfter upper → ℕ → ℕ → Prop
  | done {lower : ℕ} (tree : BST lower upper) : StackExecution tree [] tree 0 0
  | push {lower lowerAfter support rotations : ℕ} {operations : List Operation}
      {before : BST (lower + 1) upper} {middle : BST lower upper} {after : BST lowerAfter upper}
      {a : RootPrefix (.node (.empty lower) before)} {b : RootPrefix middle}
      (path : SupportedPath a b) (tail : StackExecution middle operations after support rotations) :
      StackExecution before (.push :: operations) after (a.card + support) (path.length + rotations)
  | pop {lower lowerAfter support rotations : ℕ} {operations : List Operation}
      {before : BST lower upper} {middle : BST (lower + 1) upper} {after : BST lowerAfter upper}
      {a : RootPrefix before} {b : RootPrefix (.node (.empty lower) middle)}
      (path : SupportedPath a b) (tail : StackExecution middle operations after support rotations) :
      StackExecution before (.pop :: operations) after (a.card + support) (path.length + rotations)
  | popEmpty {lowerAfter support rotations : ℕ} {operations : List Operation}
      {after : BST lowerAfter upper}
      (tail : StackExecution (.empty upper) operations after support rotations) :
      StackExecution (.empty upper) (.pop :: operations) after support rotations

/-- Reserve sufficiently many smaller keys, then every mixed operation list
has a physically realized execution with the exact predicted final counter. -/
theorem exists_stackExecution {lower upper : ℕ} {digits : List Digit} {before : BST lower upper}
    (stacked : StackShape 0 digits before) (operations : List Operation)
    (room : operations.length ≤ lower) :
    ∃ (lowerAfter support rotations : ℕ) (after : BST lowerAfter upper),
      StackShape 0 (run operations digits) after ∧
      StackExecution before operations after support rotations ∧
      support ≤ 16 * runCost operations digits ∧ rotations ≤ 16 * runCost operations digits := by
  induction operations generalizing lower digits with
  | nil => exact ⟨lower, 0, 0, before, stacked, .done _, le_rfl, le_rfl⟩
  | cons operation operations ih =>
      cases operation with
      | push =>
          cases lower with
          | zero => simp at room
          | succ lower =>
              obtain ⟨middle, shape, a, b, path, card, cost⟩ :=
                stacked.exists_push (ClassTree.zero lower)
              obtain ⟨last, support, rotations, after, finalShape, rest, supportBound, rotationBound⟩ :=
                ih shape (by simpa using room)
              refine ⟨last, _, _, after, finalShape, .push path rest, ?_, ?_⟩ <;>
                simp only [runCost, Operation.cost, Operation.apply] <;> omega
      | pop =>
          by_cases empty : digits = []
          · subst digits
            cases stacked
            obtain ⟨last, support, rotations, after, finalShape, rest, supportBound, rotationBound⟩ :=
              ih (.empty _ _) (by simp only [List.length_cons] at room; omega)
            exact ⟨last, support, rotations, after, finalShape, .popEmpty rest,
              by simpa [runCost, Operation.cost, Operation.apply, popCost, Digits.pop] using supportBound,
              by simpa [runCost, Operation.cost, Operation.apply, popCost, Digits.pop] using rotationBound⟩
          · obtain ⟨middle, shape, a, b, path, card, cost⟩ := stacked.exists_pop_zero empty
            obtain ⟨last, support, rotations, after, finalShape, rest, supportBound, rotationBound⟩ :=
              ih shape (by simp only [List.length_cons] at room; omega)
            refine ⟨last, _, _, after, finalShape, .pop path rest, ?_, ?_⟩ <;>
              simp only [runCost, Operation.cost, Operation.apply] <;> omega

/-- The amortized counter bound applies to concrete BST stack transcripts,
including arbitrary alternations between pushes and pops. -/
theorem exists_stackExecution_linear {lower upper : ℕ} {digits : List Digit}
    {before : BST lower upper} (stacked : StackShape 0 digits before) (operations : List Operation)
    (room : operations.length ≤ lower) :
    ∃ (lowerAfter support rotations : ℕ) (after : BST lowerAfter upper),
      StackShape 0 (run operations digits) after ∧
      StackExecution before operations after support rotations ∧
      support ≤ 112 * operations.length + 64 * before.size ∧
      rotations ≤ 112 * operations.length + 64 * before.size := by
  obtain ⟨lowerAfter, support, rotations, after, shape, execution, supportBound, rotationBound⟩ :=
    exists_stackExecution stacked operations room
  have counter := runCost_le operations digits
  have size := stacked.size
  simp only [pow_zero, one_mul] at size
  exact ⟨lowerAfter, support, rotations, after, shape, execution, by omega, by omega⟩

end Splay.Accounting.OfflineNormalForm.RibStack
