import TangoSquared.GapIntervals
import TangoSquared.GapRecords

/-!
# Fine-change occurrences inside concrete coarse runs

These lemmas locate the first and last micro changes as actual adjacent query
occurrences. They retain the prefix/suffix decomposition needed to construct
entry and delayed records in the original global history.
-/

namespace TangoSquared.RunOccurrences

open CyclicRuns

variable {α : Type*} [LinearOrder α]

theorem edgeDirection_eq_nil_iff (a b : α) : edgeDirection a b = [] ↔ a = b := by
  by_cases h : a = b <;> simp [edgeDirection, h]

/-- A word has no micro step exactly when all its fine labels repeat the start. -/
theorem directionsFrom_eq_nil_iff (a : α) (xs : List α) :
    directionsFrom a xs = [] ↔ ∀ x ∈ xs, x = a := by
  induction xs generalizing a with
  | nil => simp [directionsFrom]
  | cons b bs ih =>
    simp only [directionsFrom, List.append_eq_nil_iff, edgeDirection_eq_nil_iff, ih]
    constructor
    · rintro ⟨rfl, h⟩ x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · rfl
      · exact h x hx
    · intro h
      have hb := h b (by simp)
      refine ⟨hb.symm, ?_⟩
      intro x hx
      exact (h x (by simp [hx])).trans hb.symm

theorem block_micro_eq_nil_iff (b : Block α) :
    b.micro = [] ↔ ∀ x ∈ b.word, x = b.first := by
  change directionsFrom b.first b.rest = [] ↔ _
  rw [directionsFrom_eq_nil_iff]
  simp only [Block.word, List.mem_cons, forall_eq_or_imp, true_and]

/-- The last micro step has an exact adjacent source pair; all later fine labels
inside that run repeat the pair's new label. -/
theorem exists_last_micro (a : α) (xs : List α) (nontrivial : directionsFrom a xs ≠ []) :
    ∃ before y p after,
      a :: xs = before ++ y :: p :: after ∧ y ≠ p ∧ (∀ z ∈ after, z = p) := by
  induction xs generalizing a with
  | nil => exact False.elim (nontrivial rfl)
  | cons b bs ih =>
    by_cases htail : directionsFrom b bs = []
    · have hab : a ≠ b := by
        intro heq
        apply nontrivial
        simp [directionsFrom, heq, htail]
      exact ⟨[], a, b, bs, rfl, hab, (directionsFrom_eq_nil_iff b bs).mp htail⟩
    · obtain ⟨before, y, p, after, hword, hyp, hafter⟩ := ih b htail
      exact ⟨a :: before, y, p, after, by simpa using congrArg (List.cons a) hword,
        hyp, hafter⟩

/-- The first micro step departs the initial fine label after a precise positive
number of copies. This records its source and target occurrence positions. -/
theorem exists_first_micro (a : α) (xs : List α) (nontrivial : directionsFrom a xs ≠ []) :
    ∃ k x after, a :: xs = List.replicate (k + 1) a ++ x :: after ∧ a ≠ x := by
  induction xs generalizing a with
  | nil => exact False.elim (nontrivial rfl)
  | cons b bs ih =>
    by_cases hab : a = b
    · subst b
      have ht : directionsFrom a bs ≠ [] := by
        simpa only [directionsFrom_cons_self] using nontrivial
      obtain ⟨k, x, after, hword, hne⟩ := ih a ht
      refine ⟨k + 1, x, after, ?_, hne⟩
      simpa only [List.replicate_succ, List.cons_append] using congrArg (List.cons a) hword
    · exact ⟨0, b, bs, rfl, hab⟩

omit [LinearOrder α] in
/-- A block's last fine label is the target of its last micro step. -/
theorem last_label_of_last_micro (b : Block α) (before : List α) (y p : α) (after : List α)
    (split : b.word = before ++ y :: p :: after) (constant_after : ∀ z ∈ after, z = p) :
    b.last = p := by
  have hlast : b.word.getLastD p = (before ++ y :: p :: after).getLastD p := congrArg (fun xs => xs.getLastD p) split
  have hp : after.getLastD p = p := by
    clear hlast split
    induction after with
    | nil => rfl
    | cons z zs ih =>
      have hz := constant_after z (by simp)
      have hzs : ∀ w ∈ zs, w = p := fun w hw => constant_after w (by simp [hw])
      simpa only [List.getLastD_cons, hz] using ih hzs
  simpa only [Block.word, Block.last, List.getLastD_cons, lastD_append, hp] using hlast

/-- An entire trivial run is exactly its single fine cell, including its last
endpoint. This is the part of retained-record validity supplied by trivial runs. -/
theorem trivial_block_all_last (b : Block α) (trivial : b.micro = []) :
    ∀ x ∈ b.word, x = b.last := by
  have h := (block_micro_eq_nil_iff b).mp trivial
  have hl : b.last = b.first := h _ List.getLastD_mem_cons
  intro x hx
  exact (h x hx).trans hl.symm

theorem directions_append_cons (before : List α) (a : α) (after : List α) :
    directions (before ++ a :: after) =
      directions (before ++ [a]) ++ directionsFrom a after := by
  cases before with
  | nil => simp [directions, directionsFrom]
  | cons b bs =>
    simp only [List.cons_append, directions]
    rw [directionsFrom_append b bs (a :: after), directionsFrom_append b bs [a]]
    simp [directionsFrom, List.append_assoc]

/-- The last edge in the actual micro direction word is exactly the last
adjacent fine-change pair's order direction. -/
theorem last_micro_direction (b : Block α) (before : List α) (y p : α) (after : List α)
    (split : b.word = before ++ y :: p :: after) (different : y ≠ p)
    (constant_after : ∀ z ∈ after, z = p) (fallback : Bool) :
    b.micro.getLastD fallback = decide (y < p) := by
  have hafter := (directionsFrom_eq_nil_iff p after).mpr constant_after
  have hword : b.micro = directions (before ++ [y]) ++ [decide (y < p)] := by
    change directions b.word = _
    rw [split, directions_append_cons]
    simp [directionsFrom, edgeDirection, different, hafter]
  rw [hword, lastD_append]
  rfl

theorem directionsFrom_replicate (a : α) (k : ℕ) (after : List α) :
    directionsFrom a (List.replicate k a ++ after) = directionsFrom a after := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simpa only [List.replicate_succ, List.cons_append, directionsFrom_cons_self] using ih

/-- The first edge in the actual micro direction word is exactly the first
adjacent fine-change pair's order direction. -/
theorem first_micro_direction (b : Block α) (k : ℕ) (x : α) (after : List α)
    (split : b.word = List.replicate (k + 1) b.first ++ x :: after)
    (different : b.first ≠ x) : b.micro.head? = some (decide (b.first < x)) := by
  change (directions b.word).head? = _
  rw [split]
  simp only [List.replicate_succ, List.cons_append, directions, directionsFrom_replicate]
  simp [directionsFrom, edgeDirection, different]

/-- An actual chain of run endpoints, retaining both the preceding and following
fine label. This form is convenient for a gap's intervening trivial runs. -/
def Follows : α → α → List (Block α) → Prop
  | previous, closing, [] => previous = closing
  | previous, closing, b :: bs => previous = b.first ∧ Follows b.last closing bs

omit [LinearOrder α] in
theorem matching_iff_follows (b : Block α) (bs : List (Block α)) (closing : α) :
    MatchingBoundaries closing (b :: bs) ↔ Follows b.last closing bs := by
  induction bs generalizing b with
  | nil => simp [MatchingBoundaries, Follows]
  | cons c cs ih =>
    change (b.last = c.first ∧ MatchingBoundaries closing (c :: cs)) ↔
      (b.last = c.first ∧ Follows c.last closing cs)
    rw [ih]

/-- Trivial same-cell runs preserve the retained fine label throughout an
excursion, not merely at its two endpoints. -/
theorem follows_trivial_constant (previous closing : α) (blocks : List (Block α))
    (links : Follows previous closing blocks)
    (trivial : ∀ b ∈ blocks, b.micro = []) :
    previous = closing ∧ ∀ x ∈ (blocks.map Block.word).flatten, x = previous := by
  induction blocks generalizing previous with
  | nil => exact ⟨links, by simp⟩
  | cons b bs ih =>
    have hb := (block_micro_eq_nil_iff b).mp (trivial b (by simp))
    have hlast : b.last = previous := (hb _ List.getLastD_mem_cons).trans links.1.symm
    have htail := ih b.last links.2 (fun c hc => trivial c (by simp [hc]))
    refine ⟨hlast.symm.trans htail.1, ?_⟩
    intro x hx
    simp only [List.map_cons, List.flatten_cons, List.mem_append] at hx
    rcases hx with hx | hx
    · exact (hb x hx).trans links.1.symm
    · exact (htail.2 x hx).trans hlast

/-- All retained fine-label queries in the source run's tail, intervening
trivial same-cell runs, and the next run's initial plateau agree. -/
theorem retained_segment_constant (p next : α) (sourceTail nextPrefix : List α)
    (middle : List (Block α))
    (source_constant : ∀ z ∈ sourceTail, z = p)
    (links : Follows p next middle)
    (trivial : ∀ b ∈ middle, b.micro = [])
    (next_constant : ∀ z ∈ nextPrefix, z = next) :
    next = p ∧ ∀ z ∈ sourceTail ++ (middle.map Block.word).flatten ++ nextPrefix, z = p := by
  obtain ⟨hend, hmiddle⟩ := follows_trivial_constant p next middle links trivial
  refine ⟨hend.symm, ?_⟩
  intro z hz
  simp only [List.mem_append] at hz
  rcases hz with (hz | hz) | hz
  · exact source_constant z hz
  · exact hmiddle z hz
  · exact (next_constant z hz).trans hend.symm

end TangoSquared.RunOccurrences
