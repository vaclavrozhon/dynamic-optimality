import Mathlib.Data.List.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Alternations in finite words

The first symbol is free: an alternation is a pair of unequal adjacent symbols.
The alphabet is arbitrary.  In particular these lemmas apply to every owner-filtered
left/right projection used in the primary count.
-/

namespace TangoSquared

variable {α β : Type*} [DecidableEq α]

/-- The cost of the edge between two consecutive symbols. -/
def edgeChange (a b : α) : Nat := if a = b then 0 else 1

@[simp] theorem edgeChange_self (a : α) : edgeChange a a = 0 := by
  simp [edgeChange]

@[simp] theorem edgeChange_of_ne {a b : α} (h : a ≠ b) : edgeChange a b = 1 := by
  simp [edgeChange, h]

theorem edgeChange_comm (a b : α) : edgeChange a b = edgeChange b a := by
  simp [edgeChange, eq_comm]

theorem edgeChange_triangle (a b c : α) :
    edgeChange a c ≤ edgeChange a b + edgeChange b c := by
  by_cases hab : a = b
  · subst b
    simp
  · by_cases hbc : b = c
    · subst c
      simp
    · simp [edgeChange, hab, hbc]
      split_ifs <;> omega

/-- The alternations in a word, starting with a prescribed previous symbol. -/
def changesFrom (a : α) : List α → Nat
  | [] => 0
  | b :: bs => edgeChange a b + changesFrom b bs

/-- The number of unequal adjacent pairs, without an initial-symbol charge. -/
def alternations : List α → Nat
  | [] => 0
  | a :: as => changesFrom a as

@[simp] theorem changesFrom_nil (a : α) : changesFrom a [] = 0 := rfl

@[simp] theorem changesFrom_cons (a b : α) (xs : List α) :
    changesFrom a (b :: xs) = edgeChange a b + changesFrom b xs := rfl

@[simp] theorem alternations_nil : alternations ([] : List α) = 0 := rfl

@[simp] theorem alternations_singleton (a : α) : alternations [a] = 0 := rfl

@[simp] theorem alternations_cons_cons (a b : α) (xs : List α) :
    alternations (a :: b :: xs) = edgeChange a b + alternations (b :: xs) := rfl

/-- Deleting the first symbol can only decrease alternations. -/
theorem alternations_le_cons (a : α) (xs : List α) :
    alternations xs ≤ alternations (a :: xs) := by
  cases xs with
  | nil => simp
  | cons b bs => simp

/-- Inserting a symbol between a prescribed start and its continuation is harmless. -/
theorem changesFrom_le_cons (a b : α) (xs : List α) :
    changesFrom a xs ≤ changesFrom a (b :: xs) := by
  cases xs with
  | nil => simp
  | cons c cs =>
    simp only [changesFrom_cons]
    have h := edgeChange_triangle a b c
    omega

/-- Subsequence monotonicity also holds with a fixed starting symbol. -/
theorem changesFrom_sublist {xs ys : List α} (h : xs.Sublist ys) (a : α) :
    changesFrom a xs ≤ changesFrom a ys := by
  induction h generalizing a with
  | slnil => rfl
  | @cons xs ys b h ih =>
    exact (ih a).trans (changesFrom_le_cons a b ys)
  | @cons_cons xs ys b h ih =>
    simp only [changesFrom_cons]
    exact Nat.add_le_add_left (ih b) _

/-- The ordinary alternation count is monotone under taking a subsequence. -/
theorem alternations_sublist {xs ys : List α} (h : xs.Sublist ys) :
    alternations xs ≤ alternations ys := by
  induction h with
  | slnil => rfl
  | @cons xs ys b h ih => exact ih.trans (alternations_le_cons b ys)
  | @cons_cons xs ys b h ih => exact changesFrom_sublist h b

/-- Split a walk immediately after a designated boundary symbol. -/
theorem changesFrom_append_cons (a : α) (xs : List α) (b : α) (ys : List α) :
    changesFrom a (xs ++ b :: ys) =
      changesFrom a (xs ++ [b]) + changesFrom b ys := by
  induction xs generalizing a with
  | nil => simp
  | cons c cs ih => simp [ih, Nat.add_assoc]

/-- Split a nonempty word at a designated boundary symbol. -/
theorem alternations_append_cons (xs : List α) (a : α) (ys : List α) :
    alternations (xs ++ a :: ys) =
      alternations (xs ++ [a]) + changesFrom a ys := by
  cases xs with
  | nil => simp [alternations]
  | cons b bs =>
    simpa only [List.cons_append, alternations] using
      changesFrom_append_cons b bs a ys

/-- Concatenating two nonempty words adds exactly their boundary edge. -/
theorem alternations_append_nonempty (xs ys : List α) (a b : α) :
    alternations ((xs ++ [a]) ++ (b :: ys)) =
      alternations (xs ++ [a]) + edgeChange a b + alternations (b :: ys) := by
  rw [List.append_assoc]
  simpa [alternations, Nat.add_assoc] using alternations_append_cons xs a (b :: ys)

/-- Exact local deletion accounting, with arbitrary surrounding context. -/
theorem alternations_delete_middle (xs ys : List α) (a b c : α) :
    alternations (xs ++ a :: b :: c :: ys) + edgeChange a c =
      alternations (xs ++ a :: c :: ys) + edgeChange a b + edgeChange b c := by
  rw [alternations_append_cons xs a (b :: c :: ys),
    alternations_append_cons xs a (c :: ys)]
  simp only [changesFrom_cons]
  omega

/-- Deleting a different singleton between two equal symbols loses exactly two. -/
theorem alternations_delete_singleton (xs ys : List α) {a b : α} (h : a ≠ b) :
    alternations (xs ++ a :: b :: a :: ys) =
      alternations (xs ++ a :: a :: ys) + 2 := by
  have h' := alternations_delete_middle xs ys a b a
  simp [h, Ne.symm h] at h'
  omega

omit [DecidableEq α] in
/-- Applying an owner-filtered projection preserves the sublist relation. -/
theorem projected_alternations_sublist [DecidableEq β] (f : α → Option β)
    {xs ys : List α} (h : xs.Sublist ys) :
    alternations (xs.filterMap f) ≤ alternations (ys.filterMap f) :=
  alternations_sublist (h.filterMap f)

/-- A finite family of owner-filtered projections, such as primary BST nodes. -/
def primaryAlternations {ι : Type*} (owners : Finset ι) (project : ι → α → Option Bool)
    (xs : List α) : Nat :=
  ∑ i ∈ owners, alternations (xs.filterMap (project i))

omit [DecidableEq α] in
/-- The primary alternation count is monotone under deleting arbitrary queries. -/
theorem primaryAlternations_sublist {ι : Type*} (owners : Finset ι)
    (project : ι → α → Option Bool) {xs ys : List α} (h : xs.Sublist ys) :
    primaryAlternations owners project xs ≤ primaryAlternations owners project ys := by
  unfold primaryAlternations
  exact Finset.sum_le_sum fun i _ => projected_alternations_sublist (project i) h

omit [DecidableEq α] in
/-- Distinct selected primary projections losing two alternations each give an
additive global loss, while all other projections are subsequence-monotone. -/
theorem primaryAlternations_charge {ι : Type*} [DecidableEq ι]
    (owners selected : Finset ι) (project : ι → α → Option Bool)
    {xs ys : List α} (hsub : xs.Sublist ys) (hselected : selected ⊆ owners)
    (hloss : ∀ i ∈ selected,
      alternations (xs.filterMap (project i)) + 2 ≤
        alternations (ys.filterMap (project i))) :
    primaryAlternations owners project xs + 2 * selected.card ≤
      primaryAlternations owners project ys := by
  have hsum :
      (∑ i ∈ owners, (alternations (xs.filterMap (project i)) +
        if i ∈ selected then 2 else 0)) ≤
      ∑ i ∈ owners, alternations (ys.filterMap (project i)) := by
    apply Finset.sum_le_sum
    intro i hi
    by_cases his : i ∈ selected
    · simpa [his] using hloss i his
    · simpa [his] using projected_alternations_sublist (project i) hsub
  have hindicator : (∑ i ∈ owners, if i ∈ selected then 2 else 0) = 2 * selected.card := by
    rw [← Finset.sum_filter]
    rw [Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hselected]
    simp [Nat.mul_comm]
  simpa only [Finset.sum_add_distrib, hindicator, primaryAlternations] using hsum

end TangoSquared
