import DynamicOptimality.GeometricOnlineSimulation.Dyadic

namespace DynamicOptimality.GeometricOnlineSimulation.Dyadic

/-- A path to one internal key of a perfect block. The final natural number
counts expanded internal nodes. Its sibling blocks remain intact; both
output lists are nonempty, even when the surviving BST has no keys. -/
inductive Cut : Nat → List Nat → List Nat → Nat → Prop
  | root (level : Nat) : Cut (level + 1) [level] [level] 1
  | left {level steps : Nat} {before after : List Nat} (rest : Cut level before after steps) :
      Cut (level + 1) before (after ++ [level]) (steps + 1)
  | right {level steps : Nat} {before after : List Nat} (rest : Cut level before after steps) :
      Cut (level + 1) (level :: before) after (steps + 1)

namespace Cut

theorem bounds {level steps : Nat} {before after : List Nat} (cut : Cut level before after steps) :
    (∀ value ∈ before, value < level) ∧ (∀ value ∈ after, value < level) := by
  induction cut with
  | root level => simp
  | @left level steps before after rest ih =>
      constructor
      · intro value member
        have := ih.1 value member
        omega
      · intro value member
        rcases List.mem_append.mp member with member | member
        · have := ih.2 value member
          omega
        · have equal : value = level := by simpa using member
          omega
  | right rest ih =>
      constructor
      · intro value member
        rcases List.mem_cons.mp member with rfl | member
        · omega
        · have := ih.1 value member
          omega
      · intro value member
        have := ih.2 value member
        omega

theorem ordered {level steps : Nat} {before after : List Nat} (cut : Cut level before after steps) :
    before.Pairwise (· > ·) ∧ after.Pairwise (· < ·) := by
  induction cut with
  | root level => simp
  | @left level steps before after rest ih =>
      refine ⟨ih.1, List.pairwise_append.mpr ⟨ih.2, by simp, ?_⟩⟩
      intro smaller member larger last
      have equal : larger = level := by simpa using last
      subst larger
      exact rest.bounds.2 smaller member
  | right rest ih => exact ⟨List.pairwise_cons.mpr ⟨rest.bounds.1, ih.1⟩, ih.2⟩

theorem weights {level steps : Nat} {before after : List Nat} (cut : Cut level before after steps) :
    weight before + weight after = 2 ^ level := by
  induction cut with
  | root level => simp [pow_succ]; omega
  | left rest ih => simp only [weight_append, weight_cons, weight_nil, pow_succ]; omega
  | right rest ih => simp only [weight_cons, pow_succ]; omega

theorem lengths {level steps : Nat} {before after : List Nat} (cut : Cut level before after steps) :
    before.length + after.length = steps + 1 := by
  induction cut with
  | root level => rfl
  | left rest ih => simp only [List.length_append, List.length_singleton]; omega
  | right rest ih => simp only [List.length_cons]; omega

/-- Exactly one credit is spent at each expanded internal block. -/
theorem credits {level steps : Nat} {before after : List Nat} (cut : Cut level before after steps) :
    credit before + credit after + steps = 2 ^ level - 1 := by
  have sizes := cut.weights
  have count := cut.lengths
  have first := credit_exact before
  have last := credit_exact after
  omega

/-- Every requested rank has such a cut, independently of future requests. -/
theorem exists_at (level position : Nat) (inside : position < 2 ^ level - 1) :
    ∃ before after steps, Cut level before after steps ∧ weight before = position + 1 := by
  induction level generalizing position with
  | zero => simp at inside
  | succ level ih =>
      have positive := Nat.two_pow_pos level
      by_cases left : position < 2 ^ level - 1
      · obtain ⟨before, after, steps, cut, size⟩ := ih position left
        exact ⟨before, after ++ [level], steps + 1, .left cut, size⟩
      · by_cases root : position = 2 ^ level - 1
        · refine ⟨[level], [level], 1, .root level, ?_⟩
          simp only [weight_cons, weight_nil]
          omega
        · have right : position - 2 ^ level < 2 ^ level - 1 := by
            simp only [pow_succ] at inside
            omega
          obtain ⟨before, after, steps, cut, size⟩ := ih (position - 2 ^ level) right
          refine ⟨level :: before, after, steps + 1, .right cut, ?_⟩
          simp only [weight_cons, size]
          omega

theorem components {level steps : Nat} {before after left right : List Nat}
    (mountain : Mountain (before ++ level :: after)) (cut : Cut level left right steps) :
    Mountain (before ++ left) ∧ Mountain (right ++ after) :=
  ⟨mountain.cut_left cut.ordered.1 cut.bounds.1,
    mountain.cut_right cut.ordered.2 cut.bounds.2⟩

theorem component_weights {level steps : Nat} {before after left right : List Nat}
    (cut : Cut level left right steps) :
    weight (before ++ left) + weight (right ++ after) =
      weight (before ++ level :: after) := by
  have localSize := cut.weights
  simp only [weight_append, weight_cons]
  omega

theorem component_credits {level steps : Nat} {before after left right : List Nat}
    (cut : Cut level left right steps) :
    credit (before ++ left) + credit (right ++ after) + steps =
      credit (before ++ level :: after) := by
  have localCredit := cut.credits
  simp only [credit_append, credit_cons]
  omega

/-- Whole blocks are transferred only from the side with fewer keys. -/
def transfers (before after left right : List Nat) : Nat :=
  if weight (before ++ left) ≤ weight (right ++ after) then before.length else after.length

theorem transfers_le {level : Nat} {before after left right : List Nat}
    (mountain : Mountain (before ++ level :: after)) :
    transfers before after left right ≤
      2 * (Nat.log 2 (min (weight (before ++ left)) (weight (right ++ after))) + 1) := by
  unfold transfers
  split
  · rename_i smaller
    rw [min_eq_left smaller]
    have count := mountain.left_segment.length_le_log
    have monotone : Nat.log 2 (weight before) ≤ Nat.log 2 (weight (before ++ left)) :=
      Nat.log_mono_right (by simp only [weight_append]; omega)
    omega
  · rename_i smaller
    rw [min_eq_right (by omega : weight (right ++ after) ≤ weight (before ++ left))]
    have count := mountain.right_segment.length_le_log
    have monotone : Nat.log 2 (weight after) ≤ Nat.log 2 (weight (right ++ after)) :=
      Nat.log_mono_right (by simp only [weight_append]; omega)
    omega

end Cut

end DynamicOptimality.GeometricOnlineSimulation.Dyadic
