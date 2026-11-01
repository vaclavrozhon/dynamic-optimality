import TangoSquared.MTR

/-!
# Interval recency for actual move-to-root searches

This module proves that an interval representative is updated precisely by
accesses inside that interval. Consequently, the most recent access in an
interval is visited by the next search into the interval. These are statements
about `Tree.moveToRoot` and actual `Tree.searchPath`, not abstract charging
assumptions.
-/

namespace TangoSquared.MTR.Tree

variable {α : Type*} [LinearOrder α]

def InInterval (lo hi x : α) : Prop := lo ≤ x ∧ x ≤ hi

instance (lo hi x : α) : Decidable (InInterval lo hi x) := inferInstanceAs
  (Decidable (lo ≤ x ∧ x ≤ hi))

theorem representative_rotateRight_target (lo hi x a : α) (L R C : Tree α)
    (hxa : x < a) :
    representative lo hi (.node L x (.node R a C)) =
      if InInterval lo hi x then some x else
        representative lo hi (.node (.node L x R) a C) := by
  by_cases hxl : x < lo
  · have hnot : ¬ InInterval lo hi x := fun h => (not_lt_of_ge h.1) hxl
    simp only [hnot, ↓reduceIte, representative, hxl]
  · by_cases hhx : hi < x
    · have hha : hi < a := lt_trans hhx hxa
      have hnot : ¬ InInterval lo hi x := fun h => (not_lt_of_ge h.2) hhx
      have hal : ¬ a < lo := not_lt_of_ge (le_trans (le_of_not_gt hxl) (le_of_lt hxa))
      simp [hnot, representative, hxl, hhx, hha, hal]
    · have hin : InInterval lo hi x := ⟨le_of_not_gt hxl, le_of_not_gt hhx⟩
      simp [hin, representative, hxl, hhx]

theorem representative_rotateLeft_target (lo hi a x : α) (L R C : Tree α)
    (hax : a < x) :
    representative lo hi (.node (.node L a R) x C) =
      if InInterval lo hi x then some x else
        representative lo hi (.node L a (.node R x C)) := by
  by_cases hhx : hi < x
  · have hnot : ¬ InInterval lo hi x := fun h => (not_lt_of_ge h.2) hhx
    by_cases hxl : x < lo
    · have hal : a < lo := lt_trans hax hxl
      simp [hnot, representative, hxl, hal]
    · simp only [hnot, ↓reduceIte, representative, hxl, hhx]
  · by_cases hxl : x < lo
    · have hal : a < lo := lt_trans hax hxl
      have hnot : ¬ InInterval lo hi x := fun h => (not_lt_of_ge h.1) hxl
      simp [hnot, representative, hxl, hal]
    · have hin : InInterval lo hi x := ⟨le_of_not_gt hxl, le_of_not_gt hhx⟩
      simp [hin, representative, hxl, hhx]

/-- A successful actual MTR search changes an interval's representative exactly
when its requested key lies in that interval. Even the BST ordering invariant is
unnecessary here: success enforces the comparisons along the rotated path. -/
theorem representative_moveToRoot (lo hi x : α) (t : Tree α) (d : ℕ)
    (success : searchDepth x t = some d) :
    representative lo hi (moveToRoot x t) =
      if InInterval lo hi x then some x else representative lo hi t := by
  induction t generalizing d with
  | empty => simp [searchDepth] at success
  | node l a r ihl ihr =>
    by_cases hxa : x < a
    · simp only [searchDepth, hxa, ↓reduceIte] at success
      cases hs : searchDepth x l with
      | none => simp [hs] at success
      | some e =>
        have hroot := rootKey_moveToRoot_of_searchDepth x l e hs
        have hrep := ihl e hs
        cases hm : moveToRoot x l with
        | empty => simp [hm, rootKey] at hroot
        | node L y R =>
          simp only [hm, rootKey, Option.some.injEq] at hroot
          subst y
          simp only [moveToRoot, hxa, ↓reduceIte, hm, rotateRight]
          rw [representative_rotateRight_target lo hi x a L R r hxa]
          by_cases hin : InInterval lo hi x
          · simp [hin]
          · simp only [hin, ↓reduceIte] at hrep ⊢
            simp only [hm] at hrep
            simp only [representative]
            by_cases hal : a < lo
            · simp [hal]
            · by_cases hha : hi < a <;> simp [hal, hha, ← hrep, representative]
    · by_cases hax : a < x
      · simp only [searchDepth, hxa, hax, ↓reduceIte] at success
        cases hs : searchDepth x r with
        | none => simp [hs] at success
        | some e =>
          have hroot := rootKey_moveToRoot_of_searchDepth x r e hs
          have hrep := ihr e hs
          cases hm : moveToRoot x r with
          | empty => simp [hm, rootKey] at hroot
          | node L y R =>
            simp only [hm, rootKey, Option.some.injEq] at hroot
            subst y
            simp only [moveToRoot, hxa, hax, ↓reduceIte, hm, rotateLeft]
            rw [representative_rotateLeft_target lo hi a x l L R hax]
            by_cases hin : InInterval lo hi x
            · simp [hin]
            · simp only [hin, ↓reduceIte] at hrep ⊢
              simp only [hm] at hrep
              simp only [representative]
              by_cases hal : a < lo
              · simp [hal, ← hrep, representative]
              · by_cases hha : hi < a <;> simp [hal, hha]
      · have heq : x = a := le_antisymm (le_of_not_gt hax) (le_of_not_gt hxa)
        subst a
        simp only [moveToRoot_root]
        by_cases hin : InInterval lo hi x
        · simp [hin, representative, not_lt_of_ge hin.1, not_lt_of_ge hin.2]
        · simp [hin]

/-- Every requested key is successfully found in the actual intermediate tree. -/
def Successful : Tree α → List α → Prop
  | _, [] => True
  | t, x :: xs => (∃ d, searchDepth x t = some d) ∧ Successful (moveToRoot x t) xs

/-- Recency restricted to one interval, including its initial representative. -/
def intervalHistory (lo hi : α) (initial : Option α) (qs : List α) : Option α :=
  qs.foldl (fun previous x => if InInterval lo hi x then some x else previous) initial

/-- Exact interval-recency invariant for an arbitrary actual MTR execution. -/
theorem representative_run (lo hi : α) (t : Tree α) (qs : List α)
    (success : Successful t qs) :
    representative lo hi (MTR.run t qs) =
      intervalHistory lo hi (representative lo hi t) qs := by
  induction qs generalizing t with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨⟨d, hd⟩, hs⟩ := success
    simp only [MTR.run, List.foldl_cons, intervalHistory]
    change representative lo hi (MTR.run (moveToRoot x t) xs) = _
    rw [ih (moveToRoot x t) hs, representative_moveToRoot lo hi x t d hd]
    rfl

theorem intervalHistory_outside (lo hi : α) (initial : Option α) (qs : List α)
    (outside : ∀ z ∈ qs, ¬ InInterval lo hi z) :
    intervalHistory lo hi initial qs = initial := by
  induction qs generalizing initial with
  | nil => rfl
  | cons x xs ih =>
    have hx := outside x (by simp)
    have hxs : ∀ z ∈ xs, ¬ InInterval lo hi z := fun z hz => outside z (by simp [hz])
    simp only [intervalHistory, List.foldl_cons, hx, ↓reduceIte]
    exact ih initial hxs

theorem representative_run_outside (lo hi : α) (t : Tree α) (qs : List α)
    (success : Successful t qs) (outside : ∀ z ∈ qs, ¬ InInterval lo hi z) :
    representative lo hi (MTR.run t qs) = representative lo hi t := by
  rw [representative_run lo hi t qs success]
  exact intervalHistory_outside lo hi _ qs outside

/-- Concrete last-in-interval witness theorem. After a successful query to `y`,
any number of successful queries outside `[lo,hi]` preserve `y` on every future
search path into that interval. This includes arbitrary excursions on both sides. -/
theorem last_interval_query_visited (lo hi x y : α) (t : Tree α) (between : List α)
    (success : Successful t (y :: between))
    (hy : InInterval lo hi y) (hx : InInterval lo hi x)
    (outside : ∀ z ∈ between, ¬ InInterval lo hi z) :
    y ∈ searchPath x (MTR.run t (y :: between)) := by
  obtain ⟨⟨d, hd⟩, hs⟩ := success
  have hrep : representative lo hi (MTR.run t (y :: between)) = some y := by
    change representative lo hi (MTR.run (moveToRoot y t) between) = some y
    rw [representative_run_outside lo hi _ between hs outside,
      representative_moveToRoot lo hi y t d hd]
    simp [hy]
  exact representative_on_searchPath lo hi x y _ hx.1 hx.2 hrep

/-- The usual Cartesian-tree consequence, stated directly for the interval
between the new query and the old witness. -/
theorem last_between_query_visited (x y : α) (t : Tree α) (between : List α)
    (success : Successful t (y :: between))
    (outside : ∀ z ∈ between, z < min x y ∨ max x y < z) :
    y ∈ searchPath x (MTR.run t (y :: between)) := by
  apply last_interval_query_visited (min x y) (max x y) x y t between success
  · exact ⟨min_le_right _ _, le_max_right _ _⟩
  · exact ⟨min_le_left _ _, le_max_left _ _⟩
  · intro z hz hin
    obtain h | h := outside z hz
    · exact (not_lt_of_ge hin.1) h
    · exact (not_lt_of_ge hin.2) h

theorem rootKey_run_cons (t : Tree α) (x : α) (xs : List α)
    (success : Successful t (x :: xs)) :
    rootKey (MTR.run t (x :: xs)) = some (xs.getLastD x) := by
  induction xs generalizing t x with
  | nil =>
    obtain ⟨⟨d, hd⟩, _⟩ := success
    exact rootKey_moveToRoot_of_searchDepth x t d hd
  | cons z zs ih =>
    obtain ⟨_, hs⟩ := success
    simpa only [MTR.run, List.foldl_cons, List.getLastD_cons] using
      ih (moveToRoot x t) z hs

theorem searchPath_head (x : α) (t : Tree α) :
    (searchPath x t).head? = rootKey t := by
  cases t <;> rfl

theorem searchPath_last_of_success (x : α) (t : Tree α) (d : ℕ)
    (success : searchDepth x t = some d) :
    (searchPath x t).getLast? = some x := by
  induction t generalizing d with
  | empty => simp [searchDepth] at success
  | node l a r ihl ihr =>
    by_cases hxa : x < a
    · simp only [searchDepth, hxa, ↓reduceIte] at success
      cases hs : searchDepth x l with
      | none => simp [hs] at success
      | some e =>
        have hi := ihl e hs
        have hn : searchPath x l ≠ [] := by intro h; simp [h] at hi
        simpa only [searchPath, hxa, ↓reduceIte,
          List.getLast?_cons_of_ne_nil hn] using hi
    · by_cases hax : a < x
      · simp only [searchDepth, hxa, hax, ↓reduceIte] at success
        cases hs : searchDepth x r with
        | none => simp [hs] at success
        | some e =>
          have hi := ihr e hs
          have hn : searchPath x r ≠ [] := by intro h; simp [h] at hi
          simpa only [searchPath, hxa, hax, ↓reduceIte,
            List.getLast?_cons_of_ne_nil hn] using hi
      · have heq : x = a := le_antisymm (le_of_not_gt hax) (le_of_not_gt hxa)
        simp [searchPath, heq]

theorem searchPath_length_of_success (x : α) (t : Tree α) (d : ℕ)
    (success : searchDepth x t = some d) : (searchPath x t).length = d + 1 := by
  induction t generalizing d with
  | empty => simp [searchDepth] at success
  | node l a r ihl ihr =>
    by_cases hxa : x < a
    · simp only [searchDepth, hxa, ↓reduceIte] at success
      cases hs : searchDepth x l with
      | none => simp [hs] at success
      | some e =>
        have hi := ihl e hs
        simp only [hs, Option.map_some, Option.some.injEq] at success
        simp [searchPath, hxa, hi, ← success]
    · by_cases hax : a < x
      · simp only [searchDepth, hxa, hax, ↓reduceIte] at success
        cases hs : searchDepth x r with
        | none => simp [hs] at success
        | some e =>
          have hi := ihr e hs
          simp only [hs, Option.map_some, Option.some.injEq] at success
          simp [searchPath, hxa, hax, hi, ← success]
      · simp only [searchDepth, hxa, hax, ↓reduceIte, Option.some.injEq] at success
        simp [searchPath, hxa, hax, ← success]

/-- The visited nodes excluding the root and the requested key. -/
def internalSearchPath (x : α) (t : Tree α) : List α := (searchPath x t).tail.dropLast

theorem internalSearchPath_length (x : α) (t : Tree α) (d : ℕ)
    (success : searchDepth x t = some d) : (internalSearchPath x t).length = d - 1 := by
  simp [internalSearchPath, searchPath_length_of_success x t d success]

omit [LinearOrder α] in
private theorem mem_dropLast_of_ne_last {xs : List α} {y : α}
    (member : y ∈ xs) (not_last : xs.getLast? ≠ some y) : y ∈ xs.dropLast := by
  induction xs with
  | nil => simp at member
  | cons a as ih =>
    cases as with
    | nil => simp_all
    | cons b bs =>
      simp only [List.mem_cons] at member
      simp only [List.dropLast_cons_cons, List.mem_cons]
      rcases member with h | h
      · exact Or.inl h
      · exact Or.inr (ih (List.mem_cons.mpr h) (by simpa only [List.getLast?_cons_cons] using not_last))

omit [LinearOrder α] in
private theorem mem_internal_of_ne_ends {xs : List α} {y : α}
    (member : y ∈ xs) (not_head : xs.head? ≠ some y)
    (not_last : xs.getLast? ≠ some y) : y ∈ xs.tail.dropLast := by
  cases xs with
  | nil => simp at member
  | cons a as =>
    have hya : y ≠ a := by intro h; apply not_head; simp [h]
    have hm : y ∈ as := (List.mem_cons.mp member).resolve_left hya
    cases as with
    | nil => simp at hm
    | cons b bs =>
      exact mem_dropLast_of_ne_last hm (by simpa only [List.getLast?_cons_cons, List.tail_cons] using not_last)

/-- Strengthened witness theorem: if at least one intervening request exists,
the old interval representative occupies an internal path slot, excluding both
the current root and the target. -/
theorem last_interval_query_internal (lo hi x y p : α) (t : Tree α) (later : List α)
    (success : Successful t (y :: p :: later))
    (target_success : ∃ d, searchDepth x (MTR.run t (y :: p :: later)) = some d)
    (hy : InInterval lo hi y) (hx : InInterval lo hi x) (different : x ≠ y)
    (outside : ∀ z ∈ p :: later, ¬ InInterval lo hi z) :
    y ∈ internalSearchPath x (MTR.run t (y :: p :: later)) := by
  have hv := last_interval_query_visited lo hi x y t (p :: later) success hy hx outside
  have hroot := rootKey_run_cons (moveToRoot y t) p later success.2
  have hlast : later.getLastD p ≠ y := by
    intro heq
    have hmem := List.getLastD_mem_cons (l := later) (a := p)
    exact outside _ hmem (heq ▸ hy)
  apply mem_internal_of_ne_ends hv
  · rw [searchPath_head]
    change rootKey (MTR.run (moveToRoot y t) (p :: later)) ≠ some y
    rw [hroot]
    exact fun h => hlast (Option.some.inj h)
  · obtain ⟨d, hd⟩ := target_success
    rw [searchPath_last_of_success x _ d hd]
    exact fun h => different (Option.some.inj h)

/-- Concrete left-trigger delayed-record corollary. Inside its owner, the record
allows queries in the new fine cell or to the right of the coarse cell. Queries
outside the owner are harmless on either side. The hypotheses are precisely the
order facts supplied by record retention and the first-opposite-side rule. -/
theorem delayed_left_witness (ownerLo ownerHi fineLo fineHi coarseHi x y p : α)
    (t : Tree α) (later : List α)
    (success : Successful t (y :: p :: later))
    (target_success : ∃ d, searchDepth x (MTR.run t (y :: p :: later)) = some d)
    (owner_left : ownerLo ≤ x) (owner_right : y ≤ ownerHi)
    (trigger_left : x < y) (micro_right : y < fineLo) (old_in_coarse : y ≤ coarseHi)
    (record_valid : ∀ z ∈ p :: later,
      z < ownerLo ∨ ownerHi < z ∨ (fineLo ≤ z ∧ z ≤ fineHi) ∨ coarseHi < z) :
    y ∈ internalSearchPath x (MTR.run t (y :: p :: later)) := by
  apply last_interval_query_internal x y x y p t later success target_success
  · exact ⟨le_of_lt trigger_left, le_rfl⟩
  · exact ⟨le_rfl, le_of_lt trigger_left⟩
  · exact ne_of_lt trigger_left
  · intro z hz hin
    rcases record_valid z hz with h | h | h | h
    · exact (not_lt_of_ge hin.1) (lt_of_lt_of_le h owner_left)
    · exact (not_lt_of_ge hin.2) (lt_of_le_of_lt owner_right h)
    · exact (not_lt_of_ge hin.2) (lt_of_lt_of_le micro_right h.1)
    · exact (not_lt_of_ge hin.2) (lt_of_le_of_lt old_in_coarse h)

/-- The reflected delayed-record corollary. -/
theorem delayed_right_witness (ownerLo ownerHi fineLo fineHi coarseLo x y p : α)
    (t : Tree α) (later : List α)
    (success : Successful t (y :: p :: later))
    (target_success : ∃ d, searchDepth x (MTR.run t (y :: p :: later)) = some d)
    (owner_left : ownerLo ≤ y) (owner_right : x ≤ ownerHi)
    (trigger_right : y < x) (micro_left : fineHi < y) (old_in_coarse : coarseLo ≤ y)
    (record_valid : ∀ z ∈ p :: later,
      z < ownerLo ∨ ownerHi < z ∨ (fineLo ≤ z ∧ z ≤ fineHi) ∨ z < coarseLo) :
    y ∈ internalSearchPath x (MTR.run t (y :: p :: later)) := by
  apply last_interval_query_internal y x x y p t later success target_success
  · exact ⟨le_rfl, le_of_lt trigger_right⟩
  · exact ⟨le_of_lt trigger_right, le_rfl⟩
  · exact ne_of_gt trigger_right
  · intro z hz hin
    rcases record_valid z hz with h | h | h | h
    · exact (not_lt_of_ge hin.1) (lt_of_lt_of_le h owner_left)
    · exact (not_lt_of_ge hin.2) (lt_of_le_of_lt owner_right h)
    · exact (not_lt_of_ge hin.1) (lt_of_le_of_lt h.2 micro_left)
    · exact (not_lt_of_ge hin.1) (lt_of_lt_of_le h old_in_coarse)

/-- An entry from the left followed by a first micro step back to the left.
Before that step, all owner-local queries are still in a fine cell strictly to
the right of the target. The coarse-entry query `y` is an actual internal witness. -/
theorem entry_from_left_witness (ownerLo ownerHi fineLo fineHi x y p : α)
    (t : Tree α) (later : List α)
    (success : Successful t (y :: p :: later))
    (target_success : ∃ d, searchDepth x (MTR.run t (y :: p :: later)) = some d)
    (owner_left : ownerLo ≤ y) (owner_right : x ≤ ownerHi)
    (entry_right : y < x) (micro_left : x < fineLo)
    (first_fine_cell : ∀ z ∈ p :: later,
      z < ownerLo ∨ ownerHi < z ∨ (fineLo ≤ z ∧ z ≤ fineHi)) :
    y ∈ internalSearchPath x (MTR.run t (y :: p :: later)) := by
  apply last_interval_query_internal y x x y p t later success target_success
  · exact ⟨le_rfl, le_of_lt entry_right⟩
  · exact ⟨le_of_lt entry_right, le_rfl⟩
  · exact ne_of_gt entry_right
  · intro z hz hin
    rcases first_fine_cell z hz with h | h | h
    · exact (not_lt_of_ge hin.1) (lt_of_lt_of_le h owner_left)
    · exact (not_lt_of_ge hin.2) (lt_of_le_of_lt owner_right h)
    · exact (not_lt_of_ge hin.2) (lt_of_lt_of_le micro_left h.1)

/-- The reflected entry-turn corollary. -/
theorem entry_from_right_witness (ownerLo ownerHi fineLo fineHi x y p : α)
    (t : Tree α) (later : List α)
    (success : Successful t (y :: p :: later))
    (target_success : ∃ d, searchDepth x (MTR.run t (y :: p :: later)) = some d)
    (owner_left : ownerLo ≤ x) (owner_right : y ≤ ownerHi)
    (entry_left : x < y) (micro_right : fineHi < x)
    (first_fine_cell : ∀ z ∈ p :: later,
      z < ownerLo ∨ ownerHi < z ∨ (fineLo ≤ z ∧ z ≤ fineHi)) :
    y ∈ internalSearchPath x (MTR.run t (y :: p :: later)) := by
  apply last_interval_query_internal x y x y p t later success target_success
  · exact ⟨le_of_lt entry_left, le_rfl⟩
  · exact ⟨le_rfl, le_of_lt entry_left⟩
  · exact ne_of_lt entry_left
  · intro z hz hin
    rcases first_fine_cell z hz with h | h | h
    · exact (not_lt_of_ge hin.1) (lt_of_lt_of_le h owner_left)
    · exact (not_lt_of_ge hin.2) (lt_of_le_of_lt owner_right h)
    · exact (not_lt_of_ge hin.1) (lt_of_le_of_lt h.2 micro_right)

end TangoSquared.MTR.Tree
