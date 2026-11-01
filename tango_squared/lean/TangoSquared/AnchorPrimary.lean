import TangoSquared.ColoredMerge
import TangoSquared.Monotonicity

/-!
# Fixed-anchor augmentation of the first-free primary count

Deleting every occurrence of one fixed key leaves a base word. Restoring
arbitrarily many copies of that anchor adds at most twice the base length
to the actual complete-reference primary alternation count. This is a
word-level theorem; it has no initialization allowance and does not use
the cyclic convention.

The secondary-demand augmentation theorem remains a separate hand proof.
-/

namespace TangoSquared.AnchorPrimary

open Primary

def eraseAnchor (z : Key) (xs : List Key) : List Key :=
  xs.filter (fun x => x != z)

def rootWord (xs : List Key) : List Bool :=
  xs.filterMap (branch [])

def child (d : Bool) (xs : List Key) : List Key :=
  xs.filterMap (fun x => match x with
    | [] => none
    | b :: tail => if b = d then some tail else none)

theorem child_direction (d : Bool) (u : Key) (xs : List Key) :
    xs.filterMap (branch (d :: u)) = (child d xs).filterMap (branch u) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases x with
    | nil => simp_all [child, branch]
    | cons b tail =>
      cases he : branch u tail <;> cases d <;> cases b <;>
        simp_all [child]

theorem primary_succ (h : Nat) (xs : List Key) :
    primaryCount (h + 1) xs =
      alternations (rootWord xs) +
        primaryCount h (child false xs) + primaryCount h (child true xs) := by
  unfold primaryCount primaryAlternations
  rw [BitReversal.owners_sum_succ]
  simp only [child_direction, rootWord]

theorem edgeChange_le_one {α : Type*} [DecidableEq α] (a b : α) :
    edgeChange a b ≤ 1 := by
  unfold edgeChange
  split_ifs <;> omega

theorem changesFrom_le_anchor {α : Type*} [DecidableEq α]
    (z a : α) (xs : List α) :
    changesFrom a xs ≤ edgeChange a z +
      2 * (xs.filter (fun x => x != z)).length := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih =>
    have ht := ih x
    have he := edgeChange_triangle a z x
    rw [edgeChange_comm z x] at he
    by_cases hx : x = z
    · subst x
      simp only [List.filter_cons, bne_self_eq_false, Bool.false_eq_true,
        ↓reduceIte, changesFrom_cons, edgeChange_self] at *
      omega
    · have heq : edgeChange x z = 1 := edgeChange_of_ne hx
      have hf : (x != z) = true := by simp [hx]
      simp only [List.filter_cons, hf, ↓reduceIte, List.length_cons,
        changesFrom_cons]
      omega

theorem alternations_le_twice_nonanchor {α : Type*} [DecidableEq α]
    (z : α) (xs : List α) :
    alternations xs ≤ 2 * (xs.filter (fun x => x != z)).length := by
  cases xs with
  | nil => simp
  | cons x xs =>
    have ht := changesFrom_le_anchor z x xs
    by_cases hx : x = z
    · subst x
      simpa [alternations] using ht
    · have he := edgeChange_le_one x z
      have hf : (x != z) = true := by simp [hx]
      simp only [List.filter_cons, hf, ↓reduceIte, List.length_cons]
      change changesFrom x xs ≤ _
      omega

theorem root_opposite_length (d : Bool) (xs : List Key) :
    ((rootWord xs).filter (fun x => x != d)).length = (child (!d) xs).length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases x with
    | nil => simp_all [rootWord, child, branch]
    | cons b tail =>
      cases d <;> cases b <;>
        simp_all [rootWord, child, BitReversal.branch_root_cons]

theorem root_bound (d : Bool) (xs : List Key) :
    alternations (rootWord xs) ≤ 2 * (child (!d) xs).length := by
  simpa only [root_opposite_length] using
    alternations_le_twice_nonanchor d (rootWord xs)

theorem child_erase_same (d : Bool) (z : Key) (xs : List Key) :
    child d (eraseAnchor (d :: z) xs) = eraseAnchor z (child d xs) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases x with
    | nil => simp_all [eraseAnchor, child]
    | cons b tail =>
      cases d <;> cases b <;> by_cases ht : tail = z <;>
        simp_all [eraseAnchor, child]

theorem child_erase_opposite (d : Bool) (z : Key) (xs : List Key) :
    child (!d) (eraseAnchor (d :: z) xs) = child (!d) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases x with
    | nil => simp_all [eraseAnchor, child]
    | cons b tail =>
      cases d <;> cases b <;> by_cases ht : tail = z <;>
        simp_all [eraseAnchor, child]

theorem erased_children_length (d : Bool) (z : Key) (xs : List Key) :
    (child (!d) xs).length + (eraseAnchor z (child d xs)).length ≤
      (eraseAnchor (d :: z) xs).length := by
  induction xs with
  | nil => simp [child, eraseAnchor]
  | cons x xs ih =>
    cases x with
    | nil => simp [child, eraseAnchor] at *; omega
    | cons b tail =>
      cases d <;> cases b <;> by_cases ht : tail = z <;>
        simp_all [eraseAnchor, child] <;> omega

theorem branch_erase_nil (u : Key) (xs : List Key) :
    (eraseAnchor [] xs).filterMap (branch u) = xs.filterMap (branch u) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases x with
    | nil => cases u <;> simp_all [eraseAnchor, branch]
    | cons b tail =>
      cases he : branch u (b :: tail) <;> simp_all [eraseAnchor]

/-- Arbitrary copies of an anchor add at most two primary alternations
per nonanchor request. No initialization or cyclic term is present. -/
theorem primaryCount_erase_anchor (h : Nat) (z : Key) (xs : List Key) :
    primaryCount h xs ≤ primaryCount h (eraseAnchor z xs) +
      2 * (eraseAnchor z xs).length := by
  induction h generalizing z xs with
  | zero => simp [primaryCount, primaryAlternations, owners]
  | succ h ih =>
    cases z with
    | nil =>
      have he : primaryCount (h + 1) (eraseAnchor [] xs) =
          primaryCount (h + 1) xs := by
        simp only [primaryCount, primaryAlternations, branch_erase_nil]
      rw [he]
      omega
    | cons d z =>
      have ht := ih z (child d xs)
      have hr := root_bound d xs
      have hl := erased_children_length d z xs
      have ho := child_erase_opposite d z xs
      have he := child_erase_same d z xs
      rw [primary_succ, primary_succ]
      cases d <;>
        simp only [Bool.not_false, Bool.not_true] at * <;>
        rw [ho, he] <;> omega

/-- The anchor-free words agree, so either word can have arbitrary
additional anchor occurrences in arbitrary positions. -/
theorem primaryCount_anchor_equiv (h : Nat) (z : Key) (xs ys : List Key)
    (he : eraseAnchor z xs = eraseAnchor z ys) :
    primaryCount h ys ≤ primaryCount h xs + 2 * xs.length := by
  have hb := primaryCount_erase_anchor h z ys
  rw [← he] at hb
  have hs : (eraseAnchor z xs).Sublist xs := List.filter_sublist
  have hp := primaryCount_sublist h hs
  have hl := hs.length_le
  omega

end TangoSquared.AnchorPrimary
