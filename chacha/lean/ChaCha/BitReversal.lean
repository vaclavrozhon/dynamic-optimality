import ChaCha.CyclicCounts

/-!
# Bit reversal and its actual primary alternation count

This file proves the balanced-reference alternation count used by the
selected tertiary word in the research counterexample. It does not formalize
the primary Cartesian embedding, the secondary emission selection, or the
complete tertiary counterexample.
-/

namespace ChaCha
namespace BitReversal
open Primary

/-- Prepending the new leading bit alternately gives binary bit-reversal order. -/
def word : Nat → List Key
  | 0 => [[]]
  | h + 1 => (word h).flatMap (fun w => [false :: w, true :: w])

theorem length_flatMap_pairs {α β : Type*} (f g : α → β) (xs : List α) :
    (xs.flatMap (fun x => [f x, g x])).length = 2 * xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih]; omega

@[simp] theorem length_word (h : Nat) : (word h).length = 2 ^ h := by
  induction h with
  | zero => simp [word]
  | succ h ih =>
    rw [word, length_flatMap_pairs, ih, pow_succ]
    omega

theorem key_length {h : Nat} {x : Key} (hx : x ∈ word h) :
    x.length = h := by
  induction h generalizing x with
  | zero => simpa [word] using hx
  | succ h ih =>
    simp only [word, List.mem_flatMap] at hx
    obtain ⟨w, hw, hx⟩ := hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> simp [ih hw]

@[simp] theorem branch_same (b : Bool) (u x : Key) :
    branch (b :: u) (b :: x) = branch u x := by
  simp [branch]

@[simp] theorem branch_other (b : Bool) (u x : Key) :
    branch (b :: u) ((!b) :: x) = none := by
  cases b <;> simp [branch]

@[simp] theorem branch_false_true (u x : Key) :
    branch (false :: u) (true :: x) = none := by
  simp [branch]

@[simp] theorem branch_true_false (u x : Key) :
    branch (true :: u) (false :: x) = none := by
  simp [branch]

@[simp] theorem branch_root_cons (b : Bool) (x : Key) :
    branch [] (b :: x) = some b := by
  simp [branch]

/-- The root's direction word, with one left/right pair per tail word. -/
def pairs : Nat → List Bool
  | 0 => []
  | n + 1 => false :: true :: pairs n

theorem root_projection (xs : List Key) :
    (xs.flatMap (fun w => [false :: w, true :: w])).filterMap (branch []) =
      pairs xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [pairs, ih]

theorem child_projection (b : Bool) (u : Key) (xs : List Key) :
    (xs.flatMap (fun w => [false :: w, true :: w])).filterMap (branch (b :: u)) =
      xs.filterMap (branch u) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.filterMap_append]
    cases b <;> cases h : branch u x <;> simp [ih, h]

@[simp] theorem pairs_last (n : Nat) : (pairs n).getLastD true = true := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [pairs, List.getLastD_cons] using ih

@[simp] theorem changes_pairs (n : Nat) : changesFrom true (pairs n) = 2 * n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [pairs, changesFrom, edgeChange, ih]; omega

@[simp] theorem cyclic_pairs (n : Nat) :
    cyclicAlternations (pairs n) = 2 * n := by
  cases n with
  | zero => rfl
  | succ n =>
    simp only [pairs, cyclicAlternations, List.getLastD_cons, pairs_last]
    simpa only [pairs] using changes_pairs (n + 1)

theorem owners_sum_succ (h : Nat) (f : Key → Nat) :
    (∑ u ∈ owners (h + 1), f u) =
      f [] + (∑ u ∈ owners h, f (false :: u)) +
        (∑ u ∈ owners h, f (true :: u)) := by
  have hd : Disjoint ((owners h).image (false :: ·))
      ((owners h).image (true :: ·)) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨v, hv, he⟩ := Finset.mem_image.mp hy
    simp at he
  have hn : [] ∉ (owners h).image (false :: ·) ∪ (owners h).image (true :: ·) := by
    simp
  rw [owners, Finset.sum_insert hn, Finset.sum_union hd]
  rw [Finset.sum_image, Finset.sum_image]
  · simp [Nat.add_assoc]
  · intro x hx y hy hxy
    exact (List.cons.inj hxy).2
  · intro x hx y hy hxy
    exact (List.cons.inj hxy).2

theorem cyclicPrimary_step (h : Nat) :
    cyclicPrimary (h + 1) (word (h + 1)) =
      2 ^ (h + 1) + 2 * cyclicPrimary h (word h) := by
  unfold cyclicPrimary
  rw [owners_sum_succ]
  simp only [word, root_projection, cyclic_pairs, child_projection]
  rw [length_word, pow_succ]
  omega

/-- The full cyclic alternation bound on the actual complete Boolean reference. -/
theorem cyclicPrimary_word (h : Nat) :
    cyclicPrimary h (word h) = h * 2 ^ h := by
  induction h with
  | zero => simp [cyclicPrimary, owners]
  | succ h ih =>
    rw [cyclicPrimary_step, ih, pow_succ]
    calc
      2 ^ h * 2 + 2 * (h * 2 ^ h) =
          (h * 2 ^ h) * 2 + 2 ^ h * 2 := by omega
      _ = (h + 1) * (2 ^ h * 2) := by
        rw [Nat.add_mul, Nat.one_mul, Nat.mul_assoc]

end BitReversal
end ChaCha
