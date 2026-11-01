import Splay.Accounting.RibStackFoldedInitialization
import Splay.Accounting.OfflineSkeletonSubstitution

namespace Splay.Accounting.OfflineNormalForm.RibStack

open Splay.Tree OfflineConnectedSupport Digits

/-- A folded minimum stack with arbitrary literal subtree payloads.
The fixed virtual capacity reserves ordinal keys for later pushes. -/
structure FoldedMinimumStack (capacity : ℕ) {lower upper : ℕ} (frontier : SupportFrontier lower upper) where
  virtualLower : ℕ
  template : BST virtualLower capacity
  digits : List Digit
  shaped : FoldedStackShape 0 digits template
  tree : BST lower upper
  filling : Substitution template tree
  frontier_eq : filling.selected.frontier = frontier

namespace FoldedMinimumStack

theorem value_eq_card {capacity lower upper : ℕ} {frontier : SupportFrontier lower upper}
    (stack : FoldedMinimumStack capacity frontier) : value stack.digits = frontier.card := by
  have size := stack.shaped.size
  have card := stack.filling.selected_card
  have same := congrArg SupportFrontier.card stack.frontier_eq
  simp only [pow_zero, one_mul, RootPrefix.frontier_card] at *
  omega

theorem virtualLower_add_card {capacity lower upper : ℕ} {frontier : SupportFrontier lower upper}
    (stack : FoldedMinimumStack capacity frontier) : stack.virtualLower + frontier.card = capacity := by
  have size := stack.template.size_add_lower_eq_upper
  have card := stack.filling.selected_card
  have same := congrArg SupportFrontier.card stack.frontier_eq
  simp only [RootPrefix.frontier_card] at same
  omega

def potential {capacity lower upper : ℕ} {frontier : SupportFrontier lower upper}
    (stack : FoldedMinimumStack capacity frontier) : ℕ := 64 * Digits.potential 0 stack.digits

theorem potential_le_card {capacity lower upper : ℕ} {frontier : SupportFrontier lower upper}
    (stack : FoldedMinimumStack capacity frontier) : stack.potential ≤ 256 * frontier.card := by
  have bound := potential_le_value 0 stack.digits
  have count := stack.value_eq_card
  simp only [potential]
  omega

theorem height_le {capacity lower upper height : ℕ} {frontier : SupportFrontier lower upper}
    (stack : FoldedMinimumStack capacity frontier)
    (payloads : frontier.AllPayloads (fun payload => payload.height ≤ height)) :
    stack.tree.height ≤ 5 * Nat.clog 2 (frontier.card + 1) + height := by
  have filled : stack.filling.AllPayloads (fun payload => payload.height ≤ height) := by
    rw [stack.filling.allPayloads_iff_frontier, stack.frontier_eq]
    exact payloads
  have bound := stack.filling.height_le filled
  have templateBound := stack.shaped.height_le_log
  have count := stack.value_eq_card
  have size := stack.shaped.size
  simp only [pow_zero, one_mul] at size
  rw [size, count] at templateBound
  omega

theorem exists_initial {lower upper : ℕ} (capacity : ℕ) (frontier : SupportFrontier lower upper)
    (fits : frontier.card ≤ capacity) : Nonempty (FoldedMinimumStack capacity frontier) := by
  obtain ⟨digits, template, shaped, valueEq⟩ :=
    exists_initialized_foldedShape frontier.card capacity fits
  have card : frontier.card = template.size := by
    have size := shaped.size
    simp only [pow_zero, one_mul] at size
    omega
  obtain ⟨tree, filling, same⟩ := Substitution.exists_of_frontier template frontier card
  exact ⟨⟨_, template, digits, shaped, tree, filling, same⟩⟩

/-- Push preserves the exact previous frontier and prepends precisely the
incoming key and its payload. The cost is the checked class-counter cost. -/
theorem exists_push {capacity lower root upper : ℕ} {frontier : SupportFrontier (root + 1) upper}
    (stack : FoldedMinimumStack capacity frontier) (payload : BST lower root)
    (fits : frontier.card + 1 ≤ capacity) :
    ∃ result : FoldedMinimumStack capacity (.next payload frontier),
      result.digits = Digits.push stack.digits ∧
      HasSupportedPath (.node payload stack.tree) result.tree
        (64 * pushCost 0 stack.digits) (64 * pushCost 0 stack.digits) ∧
      64 * pushCost 0 stack.digits + result.potential ≤ stack.potential + 448 := by
  obtain ⟨virtualLower, template, digits, shaped, tree, filling, frontierEq⟩ := stack
  have virtualSize := template.size_add_lower_eq_upper
  have selectedSize := filling.selected_card
  have frontierSize := congrArg SupportFrontier.card frontierEq
  simp only [RootPrefix.frontier_card] at frontierSize
  cases virtualLower with
  | zero => omega
  | succ virtualLower =>
      obtain ⟨target, targetShape, virtualPath⟩ := shaped.exists_push (ClassTree.zero virtualLower)
      let initialFilling : Substitution (.node (.empty virtualLower) template) (.node payload tree) :=
        .node (.leaf virtualLower payload) filling
      obtain ⟨actual, resultFilling, same, actualPath⟩ := virtualPath.substitute_exact initialFilling
      have resultFrontier : resultFilling.selected.frontier = .next payload frontier := by
        rw [same]
        simp only [initialFilling, Substitution.selected, RootPrefix.frontier, SupportFrontier.append, frontierEq]
      let result : FoldedMinimumStack capacity (.next payload frontier) :=
        ⟨virtualLower, target, Digits.push digits, targetShape, actual, resultFilling, resultFrontier⟩
      refine ⟨result, rfl, actualPath, ?_⟩
      have amortized := push_amortized 0 digits
      change 64 * pushCost 0 digits + 64 * Digits.potential 0 (Digits.push digits) ≤
        64 * Digits.potential 0 digits + 448
      change pushCost 0 digits + Digits.potential 0 (Digits.push digits) ≤
        Digits.potential 0 digits + 7 at amortized
      omega

/-- Pop returns the literal first payload and an updated stack for the
remaining frontier. It does not inspect or rotate inside that payload. -/
theorem exists_pop {capacity lower upper : ℕ} {frontier : SupportFrontier lower upper}
    (stack : FoldedMinimumStack capacity frontier) (positive : 0 < frontier.card) :
    ∃ (root : ℕ) (payload : BST lower root) (rest : SupportFrontier (root + 1) upper)
      (result : FoldedMinimumStack capacity rest),
      frontier = .next payload rest ∧ result.digits = Digits.pop stack.digits ∧
      HasSupportedPath stack.tree (.node payload result.tree)
        (64 * popCost 0 stack.digits) (64 * popCost 0 stack.digits) ∧
      64 * popCost 0 stack.digits + result.potential ≤ stack.potential + 448 := by
  have valueEq := stack.value_eq_card
  obtain ⟨virtualLower, template, digits, shaped, tree, filling, frontierEq⟩ := stack
  change value digits = frontier.card at valueEq
  have nonempty : digits ≠ [] := by intro empty; rw [empty] at valueEq; simp [value] at valueEq; omega
  obtain ⟨target, targetShape, virtualPath⟩ := shaped.exists_pop_zero nonempty
  obtain ⟨actual, resultFilling, same, actualPath⟩ := virtualPath.substitute_exact filling
  cases resultFilling with
  | node left right =>
      rename_i root payload actualRight
      cases left with
      | leaf =>
          let result : FoldedMinimumStack capacity right.selected.frontier :=
            ⟨_, target, Digits.pop digits, targetShape, _, right, rfl⟩
          refine ⟨_, payload, _, result, ?_, rfl, actualPath, ?_⟩
          · rw [← frontierEq, ← same]
            rfl
          · have amortized := pop_amortized 0 digits
            change 64 * popCost 0 digits + 64 * Digits.potential 0 (Digits.pop digits) ≤
              64 * Digits.potential 0 digits + 448
            change popCost 0 digits + Digits.potential 0 (Digits.pop digits) ≤
              Digits.potential 0 digits + 7 at amortized
            omega

end FoldedMinimumStack

end Splay.Accounting.OfflineNormalForm.RibStack
