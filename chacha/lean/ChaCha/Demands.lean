import ChaCha.Words

/-!
# Completed coarse-run demands

`transitionLabel` emits `false` at a coarse-cell change, `true` at a fine-cell
change within a coarse cell, and no letter otherwise.  A demand is an adjacent
`true,false` pair in this filtered word.  Thus the final coarse run is not charged.
-/

namespace ChaCha

/-- The charge of one adjacent `R,L` pair (`R = true`, `L = false`). -/
def rlCharge : Bool → Bool → Nat
  | true, false => 1
  | _, _ => 0

/-- Count `R,L` pairs, retaining the last emitted letter as state. -/
def rlFrom (previous : Bool) : List Bool → Nat
  | [] => 0
  | b :: bs => rlCharge previous b + rlFrom b bs

/-- Count `R,L` pairs in a finite word, with no charge for the first letter. -/
def rlCount (word : List Bool) : Nat := rlFrom false word

@[simp] theorem rlFrom_nil (b : Bool) : rlFrom b [] = 0 := rfl

@[simp] theorem rlFrom_cons (a b : Bool) (xs : List Bool) :
    rlFrom a (b :: xs) = rlCharge a b + rlFrom b xs := rfl

theorem rlFrom_false_le_true (xs : List Bool) :
    rlFrom false xs ≤ rlFrom true xs := by
  cases xs with
  | nil => simp
  | cons b bs => cases b <;> simp [rlFrom, rlCharge]

theorem rlFrom_true_le_false_add_one (xs : List Bool) :
    rlFrom true xs ≤ rlFrom false xs + 1 := by
  cases xs with
  | nil => simp
  | cons b bs => cases b <;> simp [rlFrom, rlCharge, Nat.add_comm]

/-- An inequality uniform over both initial states can be placed after any prefix. -/
theorem rlFrom_prefix_le {xs ys : List Bool} {k : Nat}
    (h : ∀ state, rlFrom state xs ≤ rlFrom state ys + k)
    (pre : List Bool) (state : Bool) :
    rlFrom state (pre ++ xs) ≤ rlFrom state (pre ++ ys) + k := by
  induction pre generalizing state with
  | nil => exact h state
  | cons a as ih =>
    simp only [List.cons_append, rlFrom_cons]
    have h' := ih a
    omega

/-- Directed binary alternation satisfies the same shortcut inequality. -/
theorem rlCharge_triangle (a b c : Bool) :
    rlCharge a c ≤ rlCharge a b + rlCharge b c := by
  cases a <;> cases b <;> cases c <;> decide

/-- Inserting one letter into the stateful directed-alternation scan is monotone. -/
theorem rlFrom_le_cons (a b : Bool) (xs : List Bool) :
    rlFrom a xs ≤ rlFrom a (b :: xs) := by
  cases xs with
  | nil => simp
  | cons c cs =>
    simp only [rlFrom_cons]
    have h := rlCharge_triangle a b c
    omega

/-- Directed binary alternations are monotone under arbitrary subsequences. -/
theorem rlFrom_sublist {xs ys : List Bool} (h : xs.Sublist ys) (state : Bool) :
    rlFrom state xs ≤ rlFrom state ys := by
  induction h generalizing state with
  | slnil => rfl
  | @cons xs ys b h ih => exact (ih state).trans (rlFrom_le_cons state b ys)
  | @cons_cons xs ys b h ih =>
    simp only [rlFrom_cons]
    exact Nat.add_le_add_left (ih b) _

theorem rlCount_sublist {xs ys : List Bool} (h : xs.Sublist ys) :
    rlCount xs ≤ rlCount ys := rlFrom_sublist h false

variable {α C F : Type*} [DecidableEq C] [DecidableEq F]

/-- Fine cells refine coarse cells. -/
def FineRefinesCoarse (coarse : α → C) (fine : α → F) : Prop :=
  ∀ x y, fine x = fine y → coarse x = coarse y

/-- The filtered secondary letter produced by one consecutive pair. -/
def transitionLabel (coarse : α → C) (fine : α → F) (x y : α) : Option Bool :=
  if coarse x = coarse y then
    if fine x = fine y then none else some true
  else some false

/-- The transition word following a prescribed first query. -/
def transitionsFrom (coarse : α → C) (fine : α → F) (x : α) : List α → List Bool
  | [] => []
  | y :: ys => (transitionLabel coarse fine x y).toList ++ transitionsFrom coarse fine y ys

/-- The filtered transition word of an owner-local query sequence. -/
def transitionWord (coarse : α → C) (fine : α → F) : List α → List Bool
  | [] => []
  | x :: xs => transitionsFrom coarse fine x xs

/-- The number of completed coarse runs visiting at least two fine cells. -/
def demands (coarse : α → C) (fine : α → F) (xs : List α) : Nat :=
  rlCount (transitionWord coarse fine xs)

/-- Split a transition word at an explicitly retained query. -/
theorem transitionsFrom_append_cons (coarse : α → C) (fine : α → F)
    (a : α) (xs : List α) (b : α) (ys : List α) :
    transitionsFrom coarse fine a (xs ++ b :: ys) =
      transitionsFrom coarse fine a (xs ++ [b]) ++ transitionsFrom coarse fine b ys := by
  induction xs generalizing a with
  | nil => simp [transitionsFrom]
  | cons c cs ih => simp [transitionsFrom, ih, List.append_assoc]

/-- A prefix ending at the retained left neighbor is common to both deletion words. -/
theorem transitionWord_append_cons (coarse : α → C) (fine : α → F)
    (xs : List α) (a : α) (ys : List α) :
    transitionWord coarse fine (xs ++ a :: ys) =
      transitionWord coarse fine (xs ++ [a]) ++ transitionsFrom coarse fine a ys := by
  cases xs with
  | nil => simp [transitionWord, transitionsFrom]
  | cons b bs =>
    simpa only [List.cons_append, transitionWord] using
      transitionsFrom_append_cons coarse fine b bs a ys

/-- The only configuration in which deleting the middle query can create a demand. -/
def DemandCreation (coarse : α → C) (fine : α → F) (p x z : α) : Prop :=
  coarse p = coarse z ∧ coarse p ≠ coarse x ∧ fine p ≠ fine z

instance demandCreationDecidable (coarse : α → C) (fine : α → F) (p x z : α) :
    Decidable (DemandCreation coarse fine p x z) := inferInstanceAs
      (Decidable (coarse p = coarse z ∧ coarse p ≠ coarse x ∧ fine p ≠ fine z))

/-- Local transition accounting, uniformly over the previous letter and future word. -/
theorem rlFrom_transition_delete (coarse : α → C) (fine : α → F)
    (p x z : α) (suffix : List Bool) (state : Bool) :
    rlFrom state ((transitionLabel coarse fine p z).toList ++ suffix) ≤
      rlFrom state ((transitionLabel coarse fine p x).toList ++
        (transitionLabel coarse fine x z).toList ++ suffix) +
        if DemandCreation coarse fine p x z then 1 else 0 := by
  have hmon := rlFrom_false_le_true suffix
  have hbound := rlFrom_true_le_false_add_one suffix
  by_cases hpx : coarse p = coarse x <;>
    by_cases hxz : coarse x = coarse z <;>
    by_cases hpz : coarse p = coarse z <;>
    by_cases fpx : fine p = fine x <;>
    by_cases fxz : fine x = fine z <;>
    by_cases fpz : fine p = fine z <;>
    cases state <;>
    simp_all [transitionLabel, DemandCreation, rlFrom, rlCharge] <;> omega

/-- Deleting one internal occurrence creates at most one demand, and only in the
same-coarse/different-fine configuration specified by `DemandCreation`. -/
theorem demands_delete_middle (coarse : α → C) (fine : α → F)
    (pre post : List α) (p x z : α) :
    demands coarse fine (pre ++ p :: z :: post) ≤
      demands coarse fine (pre ++ p :: x :: z :: post) +
        if DemandCreation coarse fine p x z then 1 else 0 := by
  unfold demands rlCount
  rw [transitionWord_append_cons coarse fine pre p (z :: post),
    transitionWord_append_cons coarse fine pre p (x :: z :: post)]
  simpa only [transitionsFrom, List.append_assoc] using
    rlFrom_prefix_le
      (fun state => rlFrom_transition_delete coarse fine p x z
        (transitionsFrom coarse fine z post) state)
      (transitionWord coarse fine (pre ++ [p])) false

/-- The unconditional one-demand deletion bound. -/
theorem demands_delete_middle_le_add_one (coarse : α → C) (fine : α → F)
    (pre post : List α) (p x z : α) :
    demands coarse fine (pre ++ p :: z :: post) ≤
      demands coarse fine (pre ++ p :: x :: z :: post) + 1 := by
  have h := demands_delete_middle coarse fine pre post p x z
  split_ifs at h <;> omega

/-- A strict increase identifies the precise local coarse/fine configuration. -/
theorem demand_creation_of_delete_increase (coarse : α → C) (fine : α → F)
    (pre post : List α) (p x z : α)
    (hincrease : demands coarse fine (pre ++ p :: x :: z :: post) <
      demands coarse fine (pre ++ p :: z :: post)) :
    DemandCreation coarse fine p x z := by
  by_contra hnot
  have h := demands_delete_middle coarse fine pre post p x z
  simp only [if_neg hnot, Nat.add_zero] at h
  omega

/-- A continuation entirely inside one coarse cell cannot complete a demand. -/
theorem rlFrom_transitionsFrom_of_same_coarse (coarse : α → C) (fine : α → F)
    (x : α) (xs : List α) (state : Bool)
    (h : ∀ y ∈ xs, coarse y = coarse x) :
    rlFrom state (transitionsFrom coarse fine x xs) = 0 := by
  induction xs generalizing x state with
  | nil => rfl
  | cons y ys ih =>
    have hxy : coarse x = coarse y := (h y (by simp)).symm
    have hys : ∀ z ∈ ys, coarse z = coarse y := by
      intro z hz
      exact (h z (by simp [hz])).trans hxy
    have htail := ih y true hys
    have htail' := ih y state hys
    by_cases hfine : fine x = fine y
    · simpa [transitionsFrom, transitionLabel, hxy, hfine] using htail'
    · cases state <;>
        simpa [transitionsFrom, transitionLabel, hxy, hfine, rlFrom, rlCharge] using htail

/-- A newly created demand must have a later departure from its surviving coarse cell. -/
theorem later_departure_of_delete_increase (coarse : α → C) (fine : α → F)
    (pre post : List α) (p x z : α)
    (hincrease : demands coarse fine (pre ++ p :: x :: z :: post) <
      demands coarse fine (pre ++ p :: z :: post)) :
    ∃ y ∈ post, coarse y ≠ coarse p := by
  have hcreation := demand_creation_of_delete_increase coarse fine pre post p x z hincrease
  have hpz : coarse p = coarse z := hcreation.1
  by_contra hn
  have hall : ∀ y ∈ post, coarse y = coarse p := by
    intro y hy
    by_contra hne
    exact hn ⟨y, hy, hne⟩
  have hall' : ∀ y ∈ z :: post, coarse y = coarse p := by
    intro y hy
    rcases List.mem_cons.mp hy with heq | hpost
    · subst y
      exact hpz.symm
    · exact hall y hpost
  have hzero := fun state =>
    rlFrom_transitionsFrom_of_same_coarse coarse fine p (z :: post) state hall'
  have hle : ∀ state,
      rlFrom state (transitionsFrom coarse fine p (z :: post)) ≤
        rlFrom state (transitionsFrom coarse fine p (x :: z :: post)) + 0 := by
    intro state
    rw [hzero state]
    exact Nat.zero_le _
  have hfull := rlFrom_prefix_le hle (transitionWord coarse fine (pre ++ [p])) false
  have hbound : demands coarse fine (pre ++ p :: z :: post) ≤
      demands coarse fine (pre ++ p :: x :: z :: post) := by
    unfold demands rlCount
    rw [transitionWord_append_cons coarse fine pre p (z :: post),
      transitionWord_append_cons coarse fine pre p (x :: z :: post)]
    simpa using hfull
  omega

/-- Removing the first query cannot create a demand. -/
theorem demands_le_cons (coarse : α → C) (fine : α → F) (x : α) (xs : List α) :
    demands coarse fine xs ≤ demands coarse fine (x :: xs) := by
  cases xs with
  | nil => exact Nat.zero_le _
  | cons y ys =>
    exact rlCount_sublist (List.sublist_append_right _ _)

/-- Extending a continuation preserves all previous transition letters. -/
theorem transitionsFrom_sublist_append (coarse : α → C) (fine : α → F)
    (x : α) (xs ys : List α) :
    (transitionsFrom coarse fine x xs).Sublist
      (transitionsFrom coarse fine x (xs ++ ys)) := by
  induction xs generalizing x with
  | nil => exact List.nil_sublist _
  | cons a as ih =>
    exact (ih a).append_left _

/-- Removing a suffix cannot create a demand. -/
theorem demands_le_append (coarse : α → C) (fine : α → F) (xs ys : List α) :
    demands coarse fine xs ≤ demands coarse fine (xs ++ ys) := by
  cases xs with
  | nil => exact Nat.zero_le _
  | cons x xs => exact rlCount_sublist (transitionsFrom_sublist_append coarse fine x xs ys)

/-- Deleting any one occurrence increases the demand count by at most one. -/
theorem demands_delete_le_add_one (coarse : α → C) (fine : α → F)
    (pre post : List α) (x : α) :
    demands coarse fine (pre ++ post) ≤ demands coarse fine (pre ++ x :: post) + 1 := by
  induction pre using List.reverseRecOn with
  | nil =>
    have h := demands_le_cons coarse fine x post
    simpa using h.trans (Nat.le_succ _)
  | append_singleton pre p ih =>
    cases post with
    | nil =>
      have h := demands_le_append coarse fine (pre ++ [p]) [x]
      simpa using h.trans (Nat.le_succ _)
    | cons z post =>
      simpa only [List.append_assoc, List.singleton_append] using
        demands_delete_middle_le_add_one coarse fine pre post p x z

/-- If deleting a query creates a demand, both immediate owner-local neighbors
exist; they lie in the same coarse cell but different fine cells, the deleted
query lies in another coarse cell, and the surviving run eventually departs. -/
theorem demand_neighbors_of_delete_increase (coarse : α → C) (fine : α → F)
    (pre post : List α) (x : α)
    (hincrease : demands coarse fine (pre ++ x :: post) <
      demands coarse fine (pre ++ post)) :
    ∃ before p z after, pre = before ++ [p] ∧ post = z :: after ∧
      DemandCreation coarse fine p x z ∧ ∃ y ∈ after, coarse y ≠ coarse p := by
  induction pre using List.reverseRecOn with
  | nil =>
    have h := demands_le_cons coarse fine x post
    simp only [List.nil_append] at hincrease
    omega
  | append_singleton before p ih =>
    cases post with
    | nil =>
      have h := demands_le_append coarse fine (before ++ [p]) [x]
      simp only [List.append_nil] at hincrease
      omega
    | cons z after =>
      have hinc : demands coarse fine (before ++ p :: x :: z :: after) <
          demands coarse fine (before ++ p :: z :: after) := by
        simpa only [List.append_assoc, List.singleton_append] using hincrease
      exact ⟨before, p, z, after, rfl, rfl,
        demand_creation_of_delete_increase coarse fine before after p x z hinc,
        later_departure_of_delete_increase coarse fine before after p x z hinc⟩

/-- Every strictly increased gadget increases by exactly one. -/
theorem demands_eq_add_one_of_delete_increase (coarse : α → C) (fine : α → F)
    (pre post : List α) (x : α)
    (hincrease : demands coarse fine (pre ++ x :: post) <
      demands coarse fine (pre ++ post)) :
    demands coarse fine (pre ++ post) = demands coarse fine (pre ++ x :: post) + 1 := by
  have hbound := demands_delete_le_add_one coarse fine pre post x
  omega

end ChaCha
