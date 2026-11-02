import Mathlib.Data.Nat.Log
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
# Dyadic blocks used by split trees

A block of level `level` has `2^level` external gaps and `2^level - 1`
internal keys. Consecutive blocks are separated by one actual BST key, so
the sum of the gap counts is one more than the component's key count. It keeps a
sequence of such blocks whose levels first strictly increase and then
strictly decrease. There are therefore at most two blocks of each level.
Splitting one block produces a decreasing left fragment and an increasing
right fragment, each using smaller levels; both new components retain the
invariant.

Blocks are only expanded, never rebuilt. The credit `2^level - 1` pays
exactly one unit each time a block is replaced by its two halves. This
credit will be multiplied by the cost of the actual local BST operations.
-/

namespace DynamicOptimality.GeometricOnlineSimulation.Dyadic

def weight (levels : List Nat) : Nat := (levels.map fun level => 2 ^ level).sum

def credit (levels : List Nat) : Nat := (levels.map fun level => 2 ^ level - 1).sum

@[simp] theorem weight_nil : weight [] = 0 := rfl
@[simp] theorem weight_cons (level : Nat) (levels : List Nat) :
    weight (level :: levels) = 2 ^ level + weight levels := rfl
@[simp] theorem weight_append (first last : List Nat) :
    weight (first ++ last) = weight first + weight last := by simp [weight]

@[simp] theorem credit_nil : credit [] = 0 := rfl
@[simp] theorem credit_cons (level : Nat) (levels : List Nat) :
    credit (level :: levels) = (2 ^ level - 1) + credit levels := rfl
@[simp] theorem credit_append (first last : List Nat) :
    credit (first ++ last) = credit first + credit last := by simp [credit]

theorem credit_exact (levels : List Nat) : credit levels + levels.length = weight levels := by
  induction levels with
  | nil => rfl
  | cons level levels ih =>
      have positive := Nat.two_pow_pos level
      simp only [credit_cons, weight_cons, List.length_cons]
      omega

theorem expansion_credit (level : Nat) :
    2 * (2 ^ level - 1) + 1 = 2 ^ (level + 1) - 1 := by
  have positive := Nat.two_pow_pos level
  simp only [pow_succ]
  omega

theorem member_weight {level : Nat} {levels : List Nat} (member : level ∈ levels) :
    2 ^ level ≤ weight levels := by
  induction levels with
  | nil => simp at member
  | cons first rest ih =>
      rcases List.mem_cons.mp member with rfl | member
      · simp only [weight_cons]; omega
      · have bound := ih member
        exact bound.trans (Nat.le_add_left _ _)

/-- Strict growth followed by strict decrease; either half may be empty. -/
def Mountain (levels : List Nat) : Prop :=
  ∃ up down, levels = up ++ down ∧ up.Pairwise (· < ·) ∧ down.Pairwise (· > ·)

theorem Mountain.of_decreasing {levels : List Nat} (ordered : levels.Pairwise (· > ·)) :
    Mountain levels := ⟨[], levels, rfl, (by simp), ordered⟩

theorem Mountain.of_increasing {levels : List Nat} (ordered : levels.Pairwise (· < ·)) :
    Mountain levels := ⟨levels, [], by simp, ordered, (by simp)⟩

private theorem locate {α : Type*} (up down before after : List α) (pivot : α)
    (same : up ++ down = before ++ pivot :: after) :
    (∃ tail, up = before ++ pivot :: tail ∧ after = tail ++ down) ∨
      (∃ front, before = up ++ front ∧ down = front ++ pivot :: after) := by
  induction up generalizing before with
  | nil => exact Or.inr ⟨before, rfl, same⟩
  | cons first up ih =>
      cases before with
      | nil =>
          obtain ⟨rfl, rest⟩ := List.cons.inj same
          exact Or.inl ⟨up, rfl, rest.symm⟩
      | cons initial before =>
          obtain ⟨rfl, rest⟩ := List.cons.inj same
          rcases ih before rest with ⟨tail, upEq, afterEq⟩ | ⟨front, beforeEq, downEq⟩
          · exact Or.inl ⟨tail, by simp only [List.cons_append, upEq], afterEq⟩
          · exact Or.inr ⟨front, by simp only [List.cons_append, beforeEq], downEq⟩

/-- Replacing the selected block by its smaller decreasing left fragment
preserves the component invariant. -/
theorem Mountain.cut_left {before after fragment : List Nat} {pivot : Nat}
    (mountain : Mountain (before ++ pivot :: after))
    (descending : fragment.Pairwise (· > ·))
    (smaller : ∀ level ∈ fragment, level < pivot) : Mountain (before ++ fragment) := by
  obtain ⟨up, down, same, increasing, decreasing⟩ := mountain
  rcases locate up down before after pivot same.symm with
    ⟨tail, upEq, afterEq⟩ | ⟨front, beforeEq, downEq⟩
  · rw [upEq] at increasing
    exact ⟨before, fragment, rfl, (List.pairwise_append.mp increasing).1, descending⟩
  · rw [downEq] at decreasing
    obtain ⟨frontOrdered, tailOrdered, separated⟩ := List.pairwise_append.mp decreasing
    refine ⟨up, front ++ fragment, by simp [beforeEq, List.append_assoc], increasing, ?_⟩
    apply List.pairwise_append.mpr
    refine ⟨frontOrdered, descending, ?_⟩
    intro left memberLeft right memberRight
    have old := separated left memberLeft pivot (by simp)
    have new := smaller right memberRight
    omega

/-- The symmetric increasing fragment at the new left boundary. -/
theorem Mountain.cut_right {before after fragment : List Nat} {pivot : Nat}
    (mountain : Mountain (before ++ pivot :: after))
    (ascending : fragment.Pairwise (· < ·))
    (smaller : ∀ level ∈ fragment, level < pivot) : Mountain (fragment ++ after) := by
  obtain ⟨up, down, same, increasing, decreasing⟩ := mountain
  rcases locate up down before after pivot same.symm with
    ⟨tail, upEq, afterEq⟩ | ⟨front, beforeEq, downEq⟩
  · rw [upEq] at increasing
    have tailOrdered := (List.pairwise_append.mp increasing).2.1
    obtain ⟨separated, restOrdered⟩ := List.pairwise_cons.mp tailOrdered
    refine ⟨fragment ++ tail, down, by simp [afterEq, List.append_assoc], ?_, decreasing⟩
    apply List.pairwise_append.mpr
    refine ⟨ascending, restOrdered, ?_⟩
    intro left memberLeft right memberRight
    have old := separated right memberRight
    have new := smaller left memberLeft
    omega
  · rw [downEq] at decreasing
    have tailOrdered := (List.pairwise_append.mp decreasing).2.1
    exact ⟨fragment, after, rfl, ascending, (List.pairwise_cons.mp tailOrdered).2⟩

theorem Mountain.left_segment {before after : List Nat} {pivot : Nat}
    (mountain : Mountain (before ++ pivot :: after)) : Mountain before := by
  simpa using mountain.cut_left (fragment := []) (by simp) (by simp)

theorem Mountain.right_segment {before after : List Nat} {pivot : Nat}
    (mountain : Mountain (before ++ pivot :: after)) : Mountain after := by
  simpa using mountain.cut_right (fragment := []) (by simp) (by simp)

private theorem nodup_length {levels : List Nat} (distinct : levels.Nodup) (bound : Nat)
    (bounded : ∀ level ∈ levels, level ≤ bound) : levels.length ≤ bound + 1 := by
  have contained : levels.toFinset ⊆ Finset.range (bound + 1) := by
    intro level member
    exact Finset.mem_range.mpr (by have := bounded level (List.mem_toFinset.mp member); omega)
  have count := Finset.card_le_card contained
  simpa only [List.toFinset_card_of_nodup distinct, Finset.card_range] using count

/-- Only logarithmically many whole blocks can lie on the smaller side of
a split. The bound uses their own total number of keys. -/
theorem Mountain.length_le_log {levels : List Nat} (mountain : Mountain levels) :
    levels.length ≤ 2 * (Nat.log 2 (weight levels) + 1) := by
  obtain ⟨up, down, same, increasing, decreasing⟩ := mountain
  have bounded : ∀ level ∈ levels, level ≤ Nat.log 2 (weight levels) := by
    intro level member
    exact Nat.le_log_of_pow_le (by decide) (member_weight member)
  have upDistinct : up.Nodup := increasing.imp (by intros; omega)
  have downDistinct : down.Nodup := decreasing.imp (by intros; omega)
  have upLength := nodup_length upDistinct (Nat.log 2 (weight levels)) (by
    intro level member
    apply bounded
    rw [same]
    exact List.mem_append_left down member)
  have downLength := nodup_length downDistinct (Nat.log 2 (weight levels)) (by
    intro level member
    apply bounded
    rw [same]
    exact List.mem_append_right up member)
  have lengths := congrArg List.length same
  simp only [List.length_append] at lengths
  omega

end DynamicOptimality.GeometricOnlineSimulation.Dyadic
