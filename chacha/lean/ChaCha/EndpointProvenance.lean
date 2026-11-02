import ChaCha.Witnesses

/-!
# Actual last-endpoint departure records

These records keep the actual last occurrence in a primary subtree.  Their
LCA, visibility, increasing-lifetime, and normalized-predecessor properties
are derived from concrete Boolean prefixes and chronological words.

They do not assert a lower bound for sums of independent endpoint caches;
that candidate is refuted in the research notes by the broadcast example.
-/

namespace ChaCha.EndpointProvenance

open Primary NormalizedWords

/-- The access to `x` changes the child of `u` last selected by the actual
occurrence of `y` shown in the history factorization. -/
structure Departure (history : List Key) (x u y : Key) where
  before : List Key
  later : List Key
  history_eq : history = before ++ y :: later
  oldSide : Bool
  newSide : Bool
  old_branch : branch u y = some oldSide
  new_branch : branch u x = some newSide
  changed : oldSide ≠ newSide
  latest : ∀ z ∈ later, ¬ u.IsPrefix z

variable {history : List Key} {x u y : Key}

theorem Departure.source_prefix (e : Departure history x u y) :
    u.IsPrefix y := prefix_of_branch_some e.old_branch

theorem Departure.target_prefix (e : Departure history x u y) :
    u.IsPrefix x := prefix_of_branch_some e.new_branch

theorem Departure.owner_lca (e : Departure history x u y) :
    u = lcaNode y x :=
  owner_eq_lcaNode_of_branch_ne e.old_branch e.new_branch e.changed

theorem Departure.source_ne_target (e : Departure history x u y) : y ≠ x := by
  intro h
  have he : some e.oldSide = some e.newSide :=
    e.old_branch.symm.trans ((congrArg (branch u) h).trans e.new_branch)
  exact e.changed (Option.some.inj he)

/-- These are actual preference changes for every initial preference state. -/
theorem Departure.flips (e : Departure history x u y) (initial : Key → Bool) :
    Flips initial history x u := by
  have hs : ∀ z ∈ e.later, branch u z = none := by
    intro z hz
    simp [branch, e.latest z hz]
  have hp := preference_append_silent initial (e.before ++ [y]) e.later u hs
  rw [preference_append_last initial e.before y u e.oldSide e.old_branch] at hp
  refine ⟨e.newSide, e.new_branch, ?_⟩
  have hh : preference initial history u = e.oldSide :=
    (congrArg (fun w => preference initial w u) e.history_eq).trans
      (by simpa only [List.append_assoc, List.singleton_append] using hp)
  exact fun h => e.changed (hh.symm.trans h)

theorem last_owner_factorization (history : List Key) (u : Key)
    (hseen : ∃ y ∈ history, u.IsPrefix y) :
    ∃ before y later, history = before ++ y :: later ∧ u.IsPrefix y ∧
      ∀ z ∈ later, ¬ u.IsPrefix z := by
  induction history using List.reverseRecOn with
  | nil => simp at hseen
  | append_singleton history x ih =>
    by_cases hx : u.IsPrefix x
    · exact ⟨history, x, [], by simp, hx, by simp⟩
    · have hs : ∃ y ∈ history, u.IsPrefix y := by
        obtain ⟨y, hy, hp⟩ := hseen
        simp only [List.mem_append, List.mem_singleton] at hy
        rcases hy with hy | rfl
        · exact ⟨y, hy, hp⟩
        · exact (hx hp).elim
      obtain ⟨before, y, later, he, hp, hn⟩ := ih hs
      refine ⟨before, y, later ++ [x], by simp [he, List.append_assoc], hp, ?_⟩
      intro z hz
      simp only [List.mem_append, List.mem_singleton] at hz
      rcases hz with hz | rfl
      · exact hn z hz
      · exact hx

/-- Every actual flip at a previously visited internal owner has a departure
record. First-visit initialization flips are deliberately excluded. -/
theorem departure_of_flip {H : Nat} (initial : Key → Bool)
    (hu : u ∈ owners H) (hleaves : ∀ y ∈ history, y.length = H)
    (hseen : ∃ y ∈ history, u.IsPrefix y)
    (hflip : Flips initial history x u) :
    ∃ y, Nonempty (Departure history x u y) := by
  obtain ⟨before, y, later, he, hy, hn⟩ := last_owner_factorization history u hseen
  have hyH : y.length = H := hleaves y (by rw [he]; simp)
  have hul : u.length < y.length := by rw [hyH]; exact (mem_owners u H).mp hu
  let old := y[u.length]
  have hold : branch u y = some old := by
    simp [branch, hy, List.getElem?_eq_getElem hul, old]
  obtain ⟨new, hnew, hneq⟩ := hflip
  have hs : ∀ z ∈ later, branch u z = none := by
    intro z hz
    simp [branch, hn z hz]
  have hp := preference_append_silent initial (before ++ [y]) later u hs
  rw [preference_append_last initial before y u old hold] at hp
  have hp' : preference initial history u = old := by
    rw [he]
    simpa only [List.append_assoc, List.singleton_append] using hp
  refine ⟨y, ⟨⟨before, later, he, old, new, hold, hnew, ?_, hn⟩⟩⟩
  exact fun h => hneq (hp'.trans h)

/-- No intervening original access lies in the key interval of the record. -/
theorem Departure.empty_rectangle (e : Departure history x u y) :
    ∀ z ∈ e.later, ¬ MTR.Tree.InInterval (min y x) (max y x) z := by
  intro z hz
  exact Witnesses.outside_owner_interval e.source_prefix e.target_prefix (e.latest z hz)

/-- Time reversal exchanges the two actual endpoints of this departure. -/
def Departure.reverse (e : Departure history x u y) (future : List Key) :
    Departure (future.reverse ++ x :: e.later.reverse) y u x where
  before := future.reverse
  later := e.later.reverse
  history_eq := rfl
  oldSide := e.newSide
  newSide := e.oldSide
  old_branch := e.new_branch
  new_branch := e.old_branch
  changed := Ne.symm e.changed
  latest := by
    intro z hz
    exact e.latest z (by simpa using hz)

theorem Departure.reverse_word (e : Departure history x u y) (future : List Key) :
    (history ++ x :: future).reverse =
      (future.reverse ++ x :: e.later.reverse) ++ y :: e.before.reverse := by
  simp [e.history_eq, List.reverse_append, List.reverse_cons, List.append_assoc]

/-- One query cannot charge the same endpoint at two different primary nodes. -/
theorem Departure.recipient_unique {v : Key}
    (e : Departure history x u y) (f : Departure history x v y) : u = v :=
  e.owner_lca.trans f.owner_lca.symm

/-- A later record charged to the same occurrence must be strictly deeper.
The explicit suffix equality fixes the chronological occurrence, not only
the value of its key. -/
theorem Departure.lifetime_increases {history' middle : List Key} {z v : Key}
    (e : Departure history x u y) (f : Departure history' z v y)
    (hsuffix : f.later = e.later ++ x :: middle) : u.length < v.length := by
  by_contra hn
  have hle : v.length ≤ u.length := Nat.le_of_not_gt hn
  have hvu : v.IsPrefix u :=
    List.prefix_of_prefix_length_le f.source_prefix e.source_prefix hle
  have hmem : x ∈ f.later := by rw [hsuffix]; simp
  exact f.latest x hmem (hvu.trans e.target_prefix)

/-- In a normalized word, every departure is charged to the immediately
preceding global query, not to an independently chosen older endpoint. -/
theorem Departure.normalized_predecessor {H : Nat} {future : List Key}
    (e : Departure history x u y) (initial : Key → Bool)
    (hleaves : ∀ z ∈ history ++ x :: future, z.length = H)
    (hnormal : Normalized initial H (history ++ x :: future)) : e.later = [] := by
  have hy : y.length = H := hleaves y (by rw [e.history_eq]; simp)
  have hx : x.length = H := hleaves x (by simp)
  have hl : ∀ z ∈ e.later, z.length = H := by
    intro z hz
    apply hleaves z
    rw [e.history_eq]
    simp [hz]
  have hn : Normalized initial H ((e.before ++ [y]) ++ e.later ++ x :: future) := by
    simpa only [e.history_eq, List.append_assoc, List.singleton_append] using hnormal
  exact local_change_is_global_step initial H e.before e.later future u y x
    hy hx hl e.source_prefix e.target_prefix e.latest hn e.source_ne_target

end ChaCha.EndpointProvenance
