import CutPath
import ForestLedger

/-!
# Signed cut cancellation

A crossing is positive when it goes from the left of the cut to the
right, and negative in the opposite direction. On the search path to a
cut these signs alternate, so their signed sum has absolute value at
most one. `cancelled_coverage` keeps cancellation before taking absolute
values; this is the distinction from the older quadratic ledger.
-/

namespace Greedy.SignedCuts

open GreedyForest GreedyForest.CutTree
open scoped BigOperators

def bit (side : Bool) : ℤ := if side then 1 else 0

def edgeSign (parentSide : Bool) : CutTree → ℤ
  | .empty => 0
  | .node side _ _ _ => bit side - bit parentSide

def signed : CutTree → ℤ
  | .empty => 0
  | .node side _ left right =>
      signed left + signed right + edgeSign side left + edgeSign side right

theorem edgeSign_same (side : Bool) (tree : CutTree) (same : AllSide side tree) :
    edgeSign side tree = 0 := by
  cases tree with
  | empty => rfl
  | node s q left right => simp [edgeSign, same.1]

theorem signed_same (side : Bool) (tree : CutTree) (same : AllSide side tree) :
    signed tree = 0 := by
  induction tree with
  | empty => rfl
  | node s q left right il ir =>
      obtain ⟨hs, hl, hr⟩ := same
      subst s
      simp [signed, il hl, ir hr, edgeSign_same side left hl, edgeSign_same side right hr]

theorem signed_root_bounds (tree : CutTree) (ordered : CutOrdered tree) :
    match tree with
    | .empty => signed tree = 0
    | .node side _ _ _ => 0 ≤ signed tree + bit side ∧ signed tree + bit side ≤ 1 := by
  induction tree with
  | empty => rfl
  | node side q left right il ir =>
      obtain ⟨ol, or, same⟩ := ordered
      cases side
      · simp only [Bool.false_eq_true, ↓reduceIte] at same
        have wz := signed_same false left same
        have ez := edgeSign_same false left same
        have eq : signed (.node false q left right) = signed right + edgeSign false right := by
          simp only [signed, wz, ez, zero_add, add_zero]
        change 0 ≤ signed (.node false q left right) + bit false ∧
          signed (.node false q left right) + bit false ≤ 1
        rw [eq]
        have bound := ir or
        cases right with
        | empty => simp [signed, edgeSign, bit]
        | node s r l rr =>
            change 0 ≤ signed (.node s r l rr) + (bit s - bit false) + bit false ∧
              signed (.node s r l rr) + (bit s - bit false) + bit false ≤ 1
            dsimp only at bound
            omega
      · simp only [↓reduceIte] at same
        have wz := signed_same true right same
        have ez := edgeSign_same true right same
        have eq : signed (.node true q left right) = signed left + edgeSign true left := by
          simp only [signed, wz, ez, add_zero]
        change 0 ≤ signed (.node true q left right) + bit true ∧
          signed (.node true q left right) + bit true ≤ 1
        rw [eq]
        have bound := il ol
        cases left with
        | empty => simp [signed, edgeSign, bit]
        | node s r ll rr =>
            change 0 ≤ signed (.node s r ll rr) + (bit s - bit true) + bit true ∧
              signed (.node s r ll rr) + (bit s - bit true) + bit true ≤ 1
            dsimp only at bound
            omega

theorem signed_abs_le_one (tree : CutTree) (ordered : CutOrdered tree) : |signed tree| ≤ 1 := by
  have bound := signed_root_bounds tree ordered
  cases tree with
  | empty => simp [signed]
  | node side q left right =>
      have bitBounds : 0 ≤ bit side ∧ bit side ≤ 1 := by cases side <;> decide
      rw [abs_le]
      omega

/-- For each label-change cell, first add the signed coefficients of
all covering historical intervals. Only their net coefficient is bounded. -/
theorem cancelled_coverage {Edge Time : Type*} [Fintype Edge] [Fintype Time]
    (coefficient : Edge → Time → ℤ) (delta : Time → ℤ) (M : ℤ)
    (bound : ∀ t, |∑ e, coefficient e t| ≤ M) :
    ∑ e, ∑ t, coefficient e t * delta t ≤ M * ∑ t, |delta t| := by
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro t _
  rw [← Finset.sum_mul]
  calc
    (∑ e, coefficient e t) * delta t ≤ |(∑ e, coefficient e t) * delta t| := le_abs_self _
    _ = |∑ e, coefficient e t| * |delta t| := abs_mul _ _
    _ ≤ M * |delta t| := mul_le_mul_of_nonneg_right (bound t) (abs_nonneg _)

end Greedy.SignedCuts
