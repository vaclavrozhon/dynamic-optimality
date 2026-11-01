import TangoSquared.HistoryCoherence
import TangoSquared.Words
import TangoSquared.CyclicCounts

/-!
# The actual primary budget of a closed normalized MTR execution

A positive-depth request has budget one. A root request has budget zero.
Primary preference changes are counted from the actual initial representatives.
-/

namespace TangoSquared.Primary

open MTR MTR.Tree

/-- Initialized primary changes, using the analytical initial physical representatives. -/
def initializedPrimary (H : Nat) (t : Tree Key) (xs : List Key) : Nat :=
  ∑ u ∈ owners H, changesFrom (initialPreference H t u) (xs.filterMap (branch u))

/-- Number of changed Boolean primary preferences on one actual request. -/
def primaryStepCost (H : Nat) (t : Tree Key) (x : Key) : Nat :=
  ∑ u ∈ owners H, edgeChange (initialPreference H t u)
    (initialPreference H (moveToRoot x t) u)

/-- Number of non-root searches in the actual MTR execution. -/
def positiveDepthQueries : Tree Key → List Key → Nat
  | _, [] => 0
  | t, x :: xs => (if (searchDepth x t).getD 0 = 0 then 0 else 1) +
      positiveDepthQueries (moveToRoot x t) xs

/-- The initialized owner-local count has an exact per-query decomposition. -/
theorem changesFrom_branch_cons {H : Nat} {t : Tree Key} {x u : Key}
    (xs : List Key) (hu : u ∈ owners H) (hx : x.length = H)
    (hs : ∃ d, searchDepth x t = some d) :
    changesFrom (initialPreference H t u) ((x :: xs).filterMap (branch u)) =
      edgeChange (initialPreference H t u) (initialPreference H (moveToRoot x t) u) +
        changesFrom (initialPreference H (moveToRoot x t) u) (xs.filterMap (branch u)) := by
  by_cases hp : u.IsPrefix x
  · have hlen : u.length < x.length := by rw [hx]; exact (mem_owners u H).1 hu
    obtain ⟨b, hb⟩ := branch_some_of_prefix hp hlen
    simp [initialPreference, bstPreference_step hx hs, hp, hb]
  · have hb : branch u x = none := by simp [branch, hp]
    simp [initialPreference, bstPreference_step hx hs, hp, hb]

theorem initializedPrimary_cons {H : Nat} {t : Tree Key} {x : Key}
    (xs : List Key) (hx : x.length = H) (hs : ∃ d, searchDepth x t = some d) :
    initializedPrimary H t (x :: xs) = primaryStepCost H t x +
      initializedPrimary H (moveToRoot x t) xs := by
  unfold initializedPrimary primaryStepCost
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro u hu
  exact changesFrom_branch_cons xs hu hx hs

/-- Pointwise ambient normalization bounds the actual sum of Boolean changes. -/
theorem primaryStepCost_le_one {H : Nat} {t : Tree Key} {x : Key}
    (hn : NormalizedAt H t x) : primaryStepCost H t x ≤ 1 := by
  let changed := (owners H).filter (fun u => initialPreference H t u ≠
    initialPreference H (moveToRoot x t) u)
  have heq : primaryStepCost H t x = changed.card := by
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    unfold primaryStepCost
    apply Finset.sum_congr rfl
    intro u hu
    by_cases h : initialPreference H t u = initialPreference H (moveToRoot x t) u
    · simp [edgeChange, h]
    · simp [edgeChange, h]
  rw [heq]
  apply Finset.card_le_one.mpr
  intro u hu v hv
  obtain ⟨hu, hfu⟩ := Finset.mem_filter.mp hu
  obtain ⟨hv, hfv⟩ := Finset.mem_filter.mp hv
  apply hn u hu v hv
  · intro he
    exact hfu (congrArg (fun z : Option Bool => z.getD false) he.symm)
  · intro he
    exact hfv (congrArg (fun z : Option Bool => z.getD false) he.symm)

/-- A successful zero-depth query leaves the physical tree unchanged. -/
theorem moveToRoot_of_searchDepth_zero {α : Type*} [LinearOrder α]
    (x : α) (t : Tree α) (h : searchDepth x t = some 0) : moveToRoot x t = t := by
  cases t with
  | empty => simp [searchDepth] at h
  | node l y r =>
    by_cases hxy : x < y
    · simp only [searchDepth, hxy, ↓reduceIte] at h
      obtain ⟨d, hd, heq⟩ := Option.map_eq_some_iff.mp h
      omega
    · by_cases hyx : y < x
      · simp only [searchDepth, hxy, hyx, ↓reduceIte] at h
        obtain ⟨d, hd, heq⟩ := Option.map_eq_some_iff.mp h
        omega
      · simp [moveToRoot, hxy, hyx]

theorem primaryStepCost_zero_depth {H : Nat} {t : Tree Key} {x : Key}
    (hs : searchDepth x t = some 0) : primaryStepCost H t x = 0 := by
  simp [primaryStepCost, moveToRoot_of_searchDepth_zero x t hs]

/-- Each normalized request spends at most its positive-depth indicator. -/
theorem primaryStepCost_le_positive {H : Nat} {t : Tree Key} {x : Key}
    (hn : NormalizedAt H t x) (hs : ∃ d, searchDepth x t = some d) :
    primaryStepCost H t x ≤ if (searchDepth x t).getD 0 = 0 then 0 else 1 := by
  obtain ⟨d, hd⟩ := hs
  by_cases hz : d = 0
  · subst d
    simp [hd, primaryStepCost_zero_depth hd]
  · simp only [hd, Option.getD_some, if_neg hz]
    exact primaryStepCost_le_one hn

/-- The complete initialized primary count fits in the non-root-search budget. -/
theorem initializedPrimary_le_positiveDepthQueries {H : Nat} {t : Tree Key} {xs : List Key}
    (hn : AmbientNormalized H t xs) (hs : Successful t xs)
    (hheight : ∀ x ∈ xs, x.length = H) :
    initializedPrimary H t xs ≤ positiveDepthQueries t xs := by
  induction xs generalizing t with
  | nil => simp [initializedPrimary, positiveDepthQueries]
  | cons x xs ih =>
    have hx := hheight x (by simp)
    rw [initializedPrimary_cons xs hx hs.1]
    exact Nat.add_le_add (primaryStepCost_le_positive hn.1 hs.1)
      (ih hn.2 hs.2 (fun y hy => hheight y (by simp [hy])))


/-- Closure identifies each analytical initial preference with the last cyclic bit. -/
theorem cyclicPrimary_eq_initialized {H : Nat} {t : Tree Key} {xs : List Key}
    (hs : Successful t xs) (hheight : ∀ x ∈ xs, x.length = H) (hclosed : run t xs = t) :
    cyclicPrimary H xs = initializedPrimary H t xs := by
  unfold cyclicPrimary initializedPrimary
  apply Finset.sum_congr rfl
  intro u hu
  have hlast : (xs.filterMap (branch u)).getLastD (initialPreference H t u) =
      initialPreference H t u := by
    have h := bstPreference_history hu hs hheight
    rw [hclosed] at h
    exact h.symm
  cases hw : xs.filterMap (branch u) with
  | nil => rfl
  | cons a as =>
    have hl : as.getLastD a = initialPreference H t u := by
      simpa only [hw, List.getLastD_cons] using hlast
    simp only [cyclicAlternations, hl]

/-- The actual cyclic primary count is paid by the non-root searches. -/
theorem cyclicPrimary_le_positiveDepthQueries {H : Nat} {t : Tree Key} {xs : List Key}
    (hn : AmbientNormalized H t xs) (hs : Successful t xs)
    (hheight : ∀ x ∈ xs, x.length = H) (hclosed : run t xs = t) :
    cyclicPrimary H xs ≤ positiveDepthQueries t xs := by
  rw [cyclicPrimary_eq_initialized hs hheight hclosed]
  exact initializedPrimary_le_positiveDepthQueries hn hs hheight

/-- Actual MTR rotations: one for each edge traversed by the successful search. -/
def rotationCount : Tree Key → List Key → Nat
  | _, [] => 0
  | t, x :: xs => (searchDepth x t).getD 0 + rotationCount (moveToRoot x t) xs

/-- Search-path nodes excluding the old root and the requested node. -/
def internalSearchVisits : Tree Key → List Key → Nat
  | _, [] => 0
  | t, x :: xs => ((searchDepth x t).getD 0 - 1) + internalSearchVisits (moveToRoot x t) xs

/-- Non-root queries and internal visits partition the rotation budget exactly. -/
theorem positiveDepthQueries_add_internalSearchVisits (t : Tree Key) (xs : List Key) :
    positiveDepthQueries t xs + internalSearchVisits t xs = rotationCount t xs := by
  induction xs generalizing t with
  | nil => rfl
  | cons x xs ih =>
    simp only [positiveDepthQueries, internalSearchVisits, rotationCount]
    have hit := ih (moveToRoot x t)
    by_cases hz : (searchDepth x t).getD 0 = 0
    · simp only [if_pos hz]
      omega
    · simp only [if_neg hz]
      omega

theorem runCost_eq_length_add_rotationCount (t : Tree Key) (xs : List Key) :
    runCost t xs = xs.length + rotationCount t xs := by
  induction xs generalizing t with
  | nil => rfl
  | cons x xs ih =>
    simp only [runCost, rotationCount, List.length_cons]
    rw [ih]
    omega

/-- A closed normalized execution can pay its primary count together with every
internal visited-node witness, without double charging its old roots. -/
theorem cyclicPrimary_add_internalSearchVisits_le_rotations {H : Nat}
    {t : Tree Key} {xs : List Key} (hn : AmbientNormalized H t xs)
    (hs : Successful t xs) (hheight : ∀ x ∈ xs, x.length = H) (hclosed : run t xs = t) :
    cyclicPrimary H xs + internalSearchVisits t xs ≤ rotationCount t xs := by
  calc
    cyclicPrimary H xs + internalSearchVisits t xs ≤
        positiveDepthQueries t xs + internalSearchVisits t xs :=
      Nat.add_le_add_right (cyclicPrimary_le_positiveDepthQueries hn hs hheight hclosed) _
    _ = rotationCount t xs := positiveDepthQueries_add_internalSearchVisits t xs

end TangoSquared.Primary
