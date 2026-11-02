import ChaCha.Words

/-!
# Filtered neighbors around a deleted occurrence

A query's nearest neighbors inside a larger owner remain its nearest neighbors
inside a smaller owner whenever all three queries belong to the smaller owner.
The same statement is provided for partial projections, so it applies directly
to the branch-word of a primary reference node.
-/

namespace ChaCha

variable {α β : Type*}

/-- Filtering by a stronger predicate already enforces the weaker predicate. -/
theorem filter_filter_of_imp (P Q : α → Bool)
    (hQP : ∀ a, Q a = true → P a = true) (xs : List α) :
    (xs.filter P).filter Q = xs.filter Q := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
    by_cases hq : Q a = true
    · have hp := hQP a hq
      simp [hq, hp, ih]
    · by_cases hp : P a = true <;> simp [hq, hp, ih]

/-- A retained last owner-local query remains last under a stronger filter. -/
theorem filter_last_of_imp (P Q : α → Bool)
    (hQP : ∀ a, Q a = true → P a = true)
    (pre before : List α) (p : α)
    (hpre : pre.filter P = before ++ [p]) (hp : Q p = true) :
    pre.filter Q = before.filter Q ++ [p] := by
  rw [← filter_filter_of_imp P Q hQP pre, hpre]
  simp [hp]

/-- A retained first owner-local query remains first under a stronger filter. -/
theorem filter_first_of_imp (P Q : α → Bool)
    (hQP : ∀ a, Q a = true → P a = true)
    (post after : List α) (z : α)
    (hpost : post.filter P = z :: after) (hz : Q z = true) :
    post.filter Q = z :: after.filter Q := by
  rw [← filter_filter_of_imp P Q hQP post, hpost]
  simp [hz]

/-- The last retained query is uniquely determined, independently of a larger owner. -/
theorem filtered_last_unique (Q : α → Bool) (pre left right : List α) (p q : α)
    (hp : pre.filter Q = left ++ [p]) (hq : pre.filter Q = right ++ [q]) : p = q := by
  have h := List.append_inj_right' (hp.symm.trans hq) (by simp)
  simpa using h

/-- The first retained query is uniquely determined, independently of a larger owner. -/
theorem filtered_first_unique (Q : α → Bool) (post left right : List α) (p q : α)
    (hp : post.filter Q = p :: left) (hq : post.filter Q = q :: right) : p = q := by
  exact (List.cons.inj (hp.symm.trans hq)).1

/-- A partial projection supported inside an owner ignores removal of queries outside it. -/
theorem filterMap_filter_of_support (P : α → Bool) (project : α → Option β)
    (hsupport : ∀ a, P a = false → project a = none) (xs : List α) :
    (xs.filter P).filterMap project = xs.filterMap project := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
    cases hp : P a with
    | false => simp [hp, hsupport a hp, ih]
    | true => simp [hp, List.filterMap_cons, ih]

/-- The last owner's neighbor survives as the last letter of a supported projection. -/
theorem filterMap_last_of_support (P : α → Bool) (project : α → Option β)
    (hsupport : ∀ a, P a = false → project a = none)
    (pre before : List α) (p : α) (b : β)
    (hpre : pre.filter P = before ++ [p]) (hp : project p = some b) :
    pre.filterMap project = before.filterMap project ++ [b] := by
  rw [← filterMap_filter_of_support P project hsupport pre, hpre]
  simp [hp]

/-- The first owner's neighbor survives as the first letter of a supported projection. -/
theorem filterMap_first_of_support (P : α → Bool) (project : α → Option β)
    (hsupport : ∀ a, P a = false → project a = none)
    (post after : List α) (z : α) (b : β)
    (hpost : post.filter P = z :: after) (hz : project z = some b) :
    post.filterMap project = b :: after.filterMap project := by
  rw [← filterMap_filter_of_support P project hsupport post, hpost]
  simp [hz]

/-- Deleting a query between equal projected neighbors of the opposite label removes
exactly two primary alternations, even when intervening global queries are filtered out. -/
theorem projected_alternations_delete_singleton [DecidableEq β]
    (P : α → Bool) (project : α → Option β)
    (hsupport : ∀ a, P a = false → project a = none)
    (pre before post after : List α) (p x z : α) (a b : β)
    (hpre : pre.filter P = before ++ [p]) (hpost : post.filter P = z :: after)
    (hp : project p = some a) (hx : project x = some b) (hz : project z = some a)
    (hab : a ≠ b) :
    alternations ((pre ++ x :: post).filterMap project) =
      alternations ((pre ++ post).filterMap project) + 2 := by
  have hleft := filterMap_last_of_support P project hsupport pre before p a hpre hp
  have hright := filterMap_first_of_support P project hsupport post after z a hpost hz
  simpa [List.filterMap_append, hx, hleft, hright, List.append_assoc] using
    alternations_delete_singleton (before.filterMap project) (after.filterMap project) hab

end ChaCha
