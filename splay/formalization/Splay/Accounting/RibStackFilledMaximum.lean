import Splay.Accounting.RibStackFilled
import Splay.Accounting.OfflineReflection

namespace Splay.Accounting.OfflineNormalForm.RibStack

open Splay.Tree OfflineConnectedSupport Digits

/-- The maximum version shares the same class counter and cost proof.
Only the virtual template is reflected; actual payload trees stay intact. -/
structure MaximumStack (capacity : ℕ) {lower upper : ℕ} (frontier : SupportFrontier lower upper) where
  virtualLower : ℕ
  template : BST virtualLower capacity
  digits : List Digit
  shaped : StackShape 0 digits template
  imageUpper : ℕ
  image : BST 0 imageUpper
  reflection : Reflection template image
  tree : BST lower upper
  filling : Substitution image tree
  frontier_eq : filling.selected.frontier = frontier

namespace MaximumStack

theorem value_eq_card {capacity lower upper : ℕ} {frontier : SupportFrontier lower upper}
    (stack : MaximumStack capacity frontier) : value stack.digits = frontier.card := by
  have size := stack.shaped.size
  have reflected := stack.reflection.size_eq
  have card := stack.filling.selected_card
  have same := congrArg SupportFrontier.card stack.frontier_eq
  simp only [pow_zero, one_mul, RootPrefix.frontier_card] at *
  omega

theorem virtualLower_add_card {capacity lower upper : ℕ} {frontier : SupportFrontier lower upper}
    (stack : MaximumStack capacity frontier) : stack.virtualLower + frontier.card = capacity := by
  have size := stack.template.size_add_lower_eq_upper
  have shaped := stack.shaped.size
  have count := stack.value_eq_card
  simp only [pow_zero, one_mul] at shaped
  omega

def potential {capacity lower upper : ℕ} {frontier : SupportFrontier lower upper}
    (stack : MaximumStack capacity frontier) : ℕ := 16 * Digits.potential 0 stack.digits

theorem potential_le_card {capacity lower upper : ℕ} {frontier : SupportFrontier lower upper}
    (stack : MaximumStack capacity frontier) : stack.potential ≤ 64 * frontier.card := by
  have bound := potential_le_value 0 stack.digits
  have count := stack.value_eq_card
  simp only [potential]
  omega

theorem height_le {capacity lower upper height : ℕ} {frontier : SupportFrontier lower upper}
    (stack : MaximumStack capacity frontier)
    (payloads : frontier.AllPayloads (fun payload => payload.height ≤ height)) :
    stack.tree.height ≤ 5 * Nat.clog 2 (frontier.card + 1) + height := by
  have filled : stack.filling.AllPayloads (fun payload => payload.height ≤ height) := by
    rw [stack.filling.allPayloads_iff_frontier, stack.frontier_eq]
    exact payloads
  have bound := stack.filling.height_le filled
  have templateBound := stack.shaped.height_le_log
  have imageHeight := stack.reflection.height_eq
  have size := stack.shaped.size
  simp only [pow_zero, one_mul] at size
  rw [size, stack.value_eq_card] at templateBound
  omega

theorem exists_initial {lower upper : ℕ} (capacity : ℕ) (frontier : SupportFrontier lower upper)
    (fits : frontier.card ≤ capacity) : Nonempty (MaximumStack capacity frontier) := by
  obtain ⟨digits, template, _, _, shaped, valueEq, _, _, _⟩ :=
    exists_initialized_stack_with_capacity frontier.card capacity fits
  obtain ⟨imageUpper, image, ⟨reflection⟩, _⟩ := Reflection.exists_image template 0
  have card : frontier.card = image.size := by
    have size := shaped.size
    have reflected := reflection.size_eq
    simp only [pow_zero, one_mul] at size
    omega
  obtain ⟨tree, filling, same⟩ := Substitution.exists_of_frontier image frontier card
  exact ⟨⟨_, template, digits, shaped, imageUpper, image, reflection, tree, filling, same⟩⟩

theorem exists_push {capacity lower root upper : ℕ} {frontier : SupportFrontier lower root}
    (stack : MaximumStack capacity frontier) (payload : BST (root + 1) upper)
    (fits : frontier.card + 1 ≤ capacity) :
    ∃ result : MaximumStack capacity (frontier.append (.last payload)),
      result.digits = Digits.push stack.digits ∧
      HasSupportedPath (.node stack.tree payload) result.tree
        (16 * pushCost 0 stack.digits) (16 * pushCost 0 stack.digits) ∧
      16 * pushCost 0 stack.digits + result.potential ≤ stack.potential + 112 := by
  have room := stack.virtualLower_add_card
  obtain ⟨virtualLower, template, digits, shaped, imageUpper, image, reflection, tree, filling, frontierEq⟩ := stack
  change virtualLower + frontier.card = capacity at room
  cases virtualLower with
  | zero => omega
  | succ virtualLower =>
      obtain ⟨target, targetShape, virtualPath⟩ := shaped.exists_push (ClassTree.zero virtualLower)
      let initialReflection : Reflection (.node (.empty virtualLower) template) (.node image (.empty (imageUpper + 1))) :=
        .node (.leaf virtualLower (imageUpper + 1)) reflection
      obtain ⟨imageAfter, ⟨resultReflection⟩, imagePath⟩ := virtualPath.reflect initialReflection
      let initialFilling : Substitution (.node image (.empty (imageUpper + 1))) (.node tree payload) :=
        .node filling (.leaf (imageUpper + 1) payload)
      obtain ⟨actual, resultFilling, same, actualPath⟩ := imagePath.substitute_exact initialFilling
      have resultFrontier : resultFilling.selected.frontier = frontier.append (.last payload) := by
        rw [same]
        simp only [initialFilling, Substitution.selected, RootPrefix.frontier, frontierEq]
      let result : MaximumStack capacity (frontier.append (.last payload)) :=
        ⟨virtualLower, target, Digits.push digits, targetShape, imageUpper + 1, imageAfter,
          resultReflection, actual, resultFilling, resultFrontier⟩
      refine ⟨result, rfl, actualPath, ?_⟩
      have amortized := push_amortized 0 digits
      change 16 * pushCost 0 digits + 16 * Digits.potential 0 (Digits.push digits) ≤
        16 * Digits.potential 0 digits + 112
      change pushCost 0 digits + Digits.potential 0 (Digits.push digits) ≤
        Digits.potential 0 digits + 7 at amortized
      omega

theorem exists_pop {capacity lower upper : ℕ} {frontier : SupportFrontier lower upper}
    (stack : MaximumStack capacity frontier) (positive : 0 < frontier.card) :
    ∃ (root : ℕ) (rest : SupportFrontier lower root) (payload : BST (root + 1) upper)
      (result : MaximumStack capacity rest),
      frontier = rest.append (.last payload) ∧ result.digits = Digits.pop stack.digits ∧
      HasSupportedPath stack.tree (.node result.tree payload)
        (16 * popCost 0 stack.digits) (16 * popCost 0 stack.digits) ∧
      16 * popCost 0 stack.digits + result.potential ≤ stack.potential + 112 := by
  have valueEq := stack.value_eq_card
  obtain ⟨virtualLower, template, digits, shaped, imageUpper, image, reflection, tree, filling, frontierEq⟩ := stack
  change value digits = frontier.card at valueEq
  have nonempty : digits ≠ [] := by intro empty; rw [empty] at valueEq; simp [value] at valueEq; omega
  obtain ⟨target, targetShape, virtualPath⟩ := shaped.exists_pop_zero nonempty
  obtain ⟨imageAfter, ⟨resultReflection⟩, imagePath⟩ := virtualPath.reflect reflection
  cases resultReflection with
  | node left right =>
      cases left
      obtain ⟨actual, resultFilling, same, actualPath⟩ := imagePath.substitute_exact filling
      cases resultFilling with
      | node actualLeft actualRight =>
          rename_i key leftTree payload
          cases actualRight
          let result : MaximumStack capacity actualLeft.selected.frontier :=
            ⟨_, target, Digits.pop digits, targetShape, _, _, right, leftTree, actualLeft, rfl⟩
          refine ⟨key, _, payload, result, ?_, rfl, actualPath, ?_⟩
          · rw [← frontierEq, ← same]
            rfl
          · have amortized := pop_amortized 0 digits
            change 16 * popCost 0 digits + 16 * Digits.potential 0 (Digits.pop digits) ≤
              16 * Digits.potential 0 digits + 112
            change popCost 0 digits + Digits.potential 0 (Digits.pop digits) ≤
              Digits.potential 0 digits + 7 at amortized
            omega

end MaximumStack

end Splay.Accounting.OfflineNormalForm.RibStack
