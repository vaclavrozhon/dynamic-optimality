import TangoSquared.Paper20261030.PrimaryRecency

/-!
# Persistent primary-subtree histories

A primary owner is addressed by a root-to-vertex word of child choices.
Accesses preserve this address, and the state at that owner is exactly
the run on requests inside its subtree. This supplies local recency for
secondary memories even while their preferred-path component changes.
-/

namespace TangoSquared.PreferredProjection.PrefRouter

variable {α : Type*} [DecidableEq α]

def atPath : PrefRouter α → List Bool → Option (PrefRouter α)
  | t, [] => some t
  | .leaf _, _ :: _ => none
  | .fork _ l r, b :: bs => atPath (if b then r else l) bs

theorem atPath_access (t : PrefRouter α) (hn : t.leaves.Nodup) (x : α) (u : List Bool) :
    (t.access x).atPath u = (t.atPath u).map (fun s => s.access x) := by
  induction t generalizing u with
  | leaf a => cases u <;> rfl
  | fork b l r ihl ihr =>
    cases u with
    | nil => rfl
    | cons dir u =>
      obtain ⟨hnl,hnr,hdis⟩ := List.nodup_append.mp hn
      by_cases hl : x ∈ l.leaves
      · have hr : x ∉ r.leaves := fun h => hdis _ hl _ h rfl
        have har := r.access_absent x hr
        cases dir
        · simpa only [access,if_pos hl,atPath,Bool.false_eq_true,↓reduceIte] using ihl hnl u
        · simp only [access,if_pos hl,atPath,↓reduceIte]
          rw [← ihr hnr u,har]
      · have hal := l.access_absent x hl
        by_cases hr : x ∈ r.leaves
        · cases dir
          · simp only [access,if_neg hl,if_pos hr,atPath,Bool.false_eq_true,↓reduceIte]
            rw [← ihl hnl u,hal]
          · simpa only [access,if_neg hl,if_pos hr,atPath,↓reduceIte] using ihr hnr u
        · have har := r.access_absent x hr
          cases dir
          · simp only [access,if_neg hl,if_neg hr,atPath,Bool.false_eq_true,↓reduceIte]
            rw [← ihl hnl u,hal]
          · simp only [access,if_neg hl,if_neg hr,atPath,↓reduceIte]
            rw [← ihr hnr u,har]

theorem run_leaves (t : PrefRouter α) (xs : List α) : (t.run xs).leaves = t.leaves := by
  induction xs generalizing t with
  | nil => rfl
  | cons x xs ih => simp only [run,ih,access_leaves]

theorem atPath_run (t : PrefRouter α) (hn : t.leaves.Nodup) (xs : List α) (u : List Bool) :
    (t.run xs).atPath u = (t.atPath u).map (fun s => s.run xs) := by
  induction xs generalizing t with
  | nil => simp [run]
  | cons x xs ih =>
    have hn' : (t.access x).leaves.Nodup := by simpa only [access_leaves] using hn
    rw [run,ih _ hn',atPath_access t hn x u,Option.map_map]
    rfl

theorem run_filter (t : PrefRouter α) (xs : List α) :
    t.run xs = t.run (xs.filter (fun x => decide (x ∈ t.leaves))) := by
  induction xs generalizing t with
  | nil => rfl
  | cons x xs ih =>
    by_cases hx : x ∈ t.leaves
    · simp only [List.filter_cons,decide_eq_true hx,↓reduceIte,run]
      rw [ih]
      simp only [access_leaves]
    · simp only [List.filter_cons,decide_eq_false hx,↓reduceIte,run,access_absent x t hx]
      exact ih t

/-- Local preferred state depends precisely on the owner-filtered access
word, regardless of changes above that owner. -/
theorem owner_history {t s : PrefRouter α} (hn : t.leaves.Nodup)
    (u : List Bool) (hu : t.atPath u = some s) (xs : List α) :
    (t.run xs).atPath u = some (s.run (xs.filter (fun x => decide (x ∈ s.leaves)))) := by
  rw [atPath_run t hn xs u,hu,Option.map_some,run_filter]

theorem atPath_leaves {t s : PrefRouter α} {u : List Bool} (hu : t.atPath u = some s) :
    ∀ x ∈ s.leaves, x ∈ t.leaves := by
  induction u generalizing t with
  | nil => cases Option.some.inj hu; exact fun x hx => hx
  | cons b u ih =>
    cases t with
    | leaf a => contradiction
    | fork dir l r =>
      cases b
      · have h := ih (t := l) hu
        intro x hx
        exact List.mem_append_left _ (h x hx)
      · have h := ih (t := r) hu
        intro x hx
        exact List.mem_append_right _ (h x hx)

theorem atPath_nodup {t s : PrefRouter α} {u : List Bool} (hn : t.leaves.Nodup)
    (hu : t.atPath u = some s) : s.leaves.Nodup := by
  induction u generalizing t with
  | nil => cases Option.some.inj hu; exact hn
  | cons b u ih =>
    cases t with
    | leaf a => contradiction
    | fork dir l r =>
      obtain ⟨hnl,hnr,_⟩ := List.nodup_append.mp hn
      cases b
      · exact ih hnl hu
      · exact ih hnr hu

theorem filter_succ_depths (ds : List Nat) (k : Nat) :
    (ds.map Nat.succ).filter (fun d => decide (k + 1 ≤ d)) =
      (ds.filter (fun d => decide (k ≤ d))).map Nat.succ := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    by_cases h : k ≤ d
    · have hp : k + 1 ≤ d + 1 := by omega
      simp [List.filter_cons,h,hp,ih]
    · have hp : ¬ k + 1 ≤ d + 1 := by omega
      simp [List.filter_cons,h,hp,ih]

/-- The actual global exit depths below an owner are precisely its local
exit depths, shifted by the owner's depth. -/
theorem atPath_exitDepths {t s : PrefRouter α} {u : List Bool} (hn : t.leaves.Nodup)
    (hu : t.atPath u = some s) {x : α} (hx : x ∈ s.leaves) :
    (t.exitDepths x).filter (fun d => decide (u.length ≤ d)) =
      (s.exitDepths x).map (fun d => u.length + d) := by
  induction u generalizing t with
  | nil =>
    cases Option.some.inj hu
    simp
  | cons b u ih =>
    cases t with
    | leaf a => contradiction
    | fork dir l r =>
      obtain ⟨hnl,hnr,hdis⟩ := List.nodup_append.mp hn
      cases b
      · have hxl : x ∈ l.leaves := atPath_leaves (t := l) (u := u) hu x hx
        have hi := ih hnl hu
        cases dir <;>
          simp only [exitDepths,if_pos hxl,Bool.false_eq_true,↓reduceIte,List.nil_append,
            List.singleton_append,List.length_cons,List.filter_cons,
            show ¬ u.length + 1 ≤ 0 by omega,decide_false,Bool.false_eq_true,↓reduceIte,
            filter_succ_depths,hi,List.map_map]
        all_goals
          congr 1
          funext d
          simp only [Function.comp_apply]
          omega
      · have hxr : x ∈ r.leaves := atPath_leaves (t := r) (u := u) hu x hx
        have hxl : x ∉ l.leaves := fun h => hdis _ h _ hxr rfl
        have hi := ih hnr hu
        cases dir <;>
          simp only [exitDepths,if_neg hxl,if_pos hxr,Bool.false_eq_true,↓reduceIte,List.nil_append,
            List.singleton_append,List.length_cons,List.filter_cons,
            show ¬ u.length + 1 ≤ 0 by omega,decide_false,Bool.false_eq_true,↓reduceIte,
            filter_succ_depths,hi,List.map_map]
        all_goals
          congr 1
          funext d
          simp only [Function.comp_apply]
          omega

theorem atPath_perfect {t s : PrefRouter α} {u : List Bool} {h : Nat}
    (hp : Perfect (u.length + h) t) (hu : t.atPath u = some s) : Perfect h s := by
  induction u generalizing t with
  | nil => cases Option.some.inj hu; simpa using hp
  | cons b u ih =>
    cases t with
    | leaf a => simp [Perfect] at hp
    | fork dir l r =>
      have hp' : Perfect (u.length + h + 1) (.fork dir l r) := by
        convert hp using 1 <;> simp only [List.length_cons] <;> omega
      cases b
      · exact ih hp'.1 hu
      · exact ih hp'.2 hu

theorem perfect_run {H : Nat} {t : PrefRouter α} (hp : Perfect H t) (xs : List α) :
    Perfect H (t.run xs) := by
  induction xs generalizing t with
  | nil => exact hp
  | cons x xs ih => exact ih (perfect_access hp x)

theorem run_append (t : PrefRouter α) (xs ys : List α) :
    t.run (xs ++ ys) = (t.run xs).run ys := by
  induction xs generalizing t with
  | nil => rfl
  | cons x xs ih => exact ih (t.access x)

theorem referenceLCA_run (t : PrefRouter α) (xs : List α) (x y : α) :
    (t.run xs).referenceLCA x y = t.referenceLCA x y := by
  induction xs generalizing t with
  | nil => rfl
  | cons z xs ih => rw [run,ih,referenceLCA_access]

/-- After any intervening requests outside this owner, its next first exit
is still the LCA with its last local request. -/
theorem owner_last_request {t s : PrefRouter α} {u : List Bool} {h : Nat}
    (hp : Perfect (u.length + h) t) (hn : t.leaves.Nodup) (hu : t.atPath u = some s)
    (xs ys : List α) {p x : α} (hpkey : p ∈ s.leaves) (hx : x ∈ s.leaves)
    (hlast : xs.filter (fun x => decide (x ∈ s.leaves)) = ys ++ [p]) :
    ∃ s', (t.run xs).atPath u = some s' ∧
      (s'.exitDepths x).headD h = s.referenceLCA p x := by
  have hstate := owner_history hn u hu xs
  rw [hlast,run_append] at hstate
  refine ⟨(s.run ys).access p,hstate,?_⟩
  have hps := atPath_perfect hp hu
  have hns := atPath_nodup hn hu
  have hns' : (s.run ys).leaves.Nodup := by simpa only [run_leaves] using hns
  have hpm : p ∈ (s.run ys).leaves := by simpa only [run_leaves] using hpkey
  have hxm : x ∈ (s.run ys).leaves := by simpa only [run_leaves] using hx
  rw [next_first_exit_lca (perfect_run hps ys) hns' hpm hxm,referenceLCA_run]

end TangoSquared.PreferredProjection.PrefRouter
