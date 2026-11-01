import TangoSquared.Paper20261030.AbstractTango

/-!
# Restriction preserves actual abstract Tango accesses

The participating set is explicit. `Legal` requires the preferred child
to be the participating child whenever only one child participates. Thus
unary suppression removes no independent preference bit.
-/

namespace TangoSquared.PreferredProjection.PrefRouter

open RouterProjection
variable {α : Type*} [DecidableEq α]

theorem prune_some_leaves (keep : α → Bool) {t u : PrefRouter α}
    (hp : t.prune keep = some u) : u.leaves = t.leaves.filter keep := by
  have he := congrArg Router.leaves (erase_prune keep t)
  rw [hp] at he
  simpa only [eraseOption,leaves_erase,Router.leaves_prune] using he

theorem prune_none_leaves (keep : α → Bool) {t : PrefRouter α}
    (hp : t.prune keep = none) : t.leaves.filter keep = [] := by
  have he := congrArg Router.leaves (erase_prune keep t)
  rw [hp] at he
  simpa only [eraseOption,Router.leaves,Router.leaves_prune,leaves_erase] using he.symm

theorem prune_exists_of_retained (keep : α → Bool) {t : PrefRouter α} {x : α}
    (hx : x ∈ t.leaves) (hk : keep x = true) :
    ∃ u, t.prune keep = some u ∧ x ∈ u.leaves := by
  cases hp : t.prune keep with
  | none =>
    have he := prune_none_leaves keep hp
    have hm : x ∈ t.leaves.filter keep := List.mem_filter.mpr ⟨hx,hk⟩
    rw [he] at hm
    contradiction
  | some u =>
    refine ⟨u,rfl,?_⟩
    rw [prune_some_leaves keep hp]
    exact List.mem_filter.mpr ⟨hx,hk⟩

def Legal (keep : α → Bool) : PrefRouter α → Prop
  | .leaf _ => True
  | .fork b l r => Legal keep l ∧ Legal keep r ∧
      (l.prune keep = none → r.prune keep ≠ none → b = true) ∧
      (r.prune keep = none → l.prune keep ≠ none → b = false)

/-- Commuting state update and exact flip count, proved by actual pruning. -/
theorem access_prune (keep : α → Bool) (x : α) {t u : PrefRouter α}
    (hlegal : Legal keep t) (hx : x ∈ t.leaves) (hk : keep x = true)
    (hp : t.prune keep = some u) :
    (t.access x).prune keep = some (u.access x) ∧ t.accessFlips x = u.accessFlips x := by
  induction t generalizing u with
  | leaf y =>
    have hxy : x = y := List.mem_singleton.mp hx
    subst x
    have hu : u = .leaf y := by simpa only [prune,hk,↓reduceIte,Option.some.injEq] using hp.symm
    subst u
    simp [access,accessFlips,prune,hk]
  | fork b l r ihl ihr =>
    obtain ⟨hll,hlr,hforceR,hforceL⟩ := hlegal
    have hxLR : x ∈ l.leaves ∨ x ∈ r.leaves := List.mem_append.mp hx
    cases hpl : l.prune keep with
    | none =>
      have hnL : x ∉ l.leaves := by
        intro hxl
        obtain ⟨v,hv,_⟩ := prune_exists_of_retained keep hxl hk
        rw [hpl] at hv
        contradiction
      have hxr := hxLR.resolve_left hnL
      obtain ⟨r',hpr,hxr'⟩ := prune_exists_of_retained keep hxr hk
      have hb := hforceR hpl (by rw [hpr]; simp)
      subst b
      have hu : u = r' := by simpa only [prune,hpl,hpr,combine,Option.some.injEq] using hp.symm
      subst u
      obtain ⟨hstate,hflips⟩ := ihr hlr hxr hpr
      simp only [access,if_neg hnL,if_pos hxr,prune,hpl,hstate,combine,
        accessFlips,edgeChange_self,Nat.zero_add,hflips]
      trivial
    | some l' =>
      cases hpr : r.prune keep with
      | none =>
        have hnR : x ∉ r.leaves := by
          intro hxr
          obtain ⟨v,hv,_⟩ := prune_exists_of_retained keep hxr hk
          rw [hpr] at hv
          contradiction
        have hxl := hxLR.resolve_right hnR
        have hb := hforceL hpr (by rw [hpl]; simp)
        subst b
        have hu : u = l' := by simpa only [prune,hpl,hpr,combine,Option.some.injEq] using hp.symm
        subst u
        obtain ⟨hstate,hflips⟩ := ihl hll hxl hpl
        simp only [access,if_pos hxl,prune,hpr,hstate,combine,
          accessFlips,edgeChange_self,Nat.zero_add,hflips]
        trivial
      | some r' =>
        have hu : u = .fork b l' r' := by
          simpa only [prune,hpl,hpr,combine,Option.some.injEq] using hp.symm
        subst u
        have hxleaves : x ∈ l'.leaves ↔ x ∈ l.leaves := by
          rw [prune_some_leaves keep hpl]
          simp only [List.mem_filter,hk,and_true]
        have hxrleaves : x ∈ r'.leaves ↔ x ∈ r.leaves := by
          rw [prune_some_leaves keep hpr]
          simp only [List.mem_filter,hk,and_true]
        by_cases hxl : x ∈ l.leaves
        · have hxl' := hxleaves.mpr hxl
          obtain ⟨hstate,hflips⟩ := ihl hll hxl hpl
          simp only [access,if_pos hxl,if_pos hxl',prune,hstate,hpr,combine,
            accessFlips,hflips]
          trivial
        · have hxl' : x ∉ l'.leaves := fun h => hxl (hxleaves.mp h)
          have hxr := hxLR.resolve_left hxl
          have hxr' := hxrleaves.mpr hxr
          obtain ⟨hstate,hflips⟩ := ihr hlr hxr hpr
          simp only [access,if_neg hxl,if_neg hxl',if_pos hxr,if_pos hxr',
            prune,hpl,hstate,combine,accessFlips,hflips]
          trivial

theorem prune_none_iff_filtered_empty (keep : α → Bool) (t : PrefRouter α) :
    t.prune keep = none ↔ t.leaves.filter keep = [] := by
  constructor
  · exact prune_none_leaves keep
  · intro he
    cases hp : t.prune keep with
    | none => rfl
    | some u =>
      have hu := prune_some_leaves keep hp
      have hm := u.terminal_mem
      rw [hu,he] at hm
      contradiction

theorem prune_none_access_iff (keep : α → Bool) (x : α) (t : PrefRouter α) :
    (t.access x).prune keep = none ↔ t.prune keep = none := by
  rw [prune_none_iff_filtered_empty,prune_none_iff_filtered_empty,access_leaves]

theorem legal_access (keep : α → Bool) (x : α) {t : PrefRouter α}
    (hlegal : Legal keep t) (hx : x ∈ t.leaves) (hk : keep x = true) :
    Legal keep (t.access x) := by
  induction t with
  | leaf y => trivial
  | fork b l r ihl ihr =>
    obtain ⟨hll,hlr,hforceR,hforceL⟩ := hlegal
    have hxLR : x ∈ l.leaves ∨ x ∈ r.leaves := List.mem_append.mp hx
    by_cases hxl : x ∈ l.leaves
    · obtain ⟨v,hv,_⟩ := prune_exists_of_retained keep hxl hk
      rw [access,if_pos hxl]
      refine ⟨ihl hll hxl,hlr,?_,?_⟩
      · intro hn _
        have := (prune_none_access_iff keep x l).mp hn
        rw [hv] at this
        contradiction
      · intros
        rfl
    · have hxr := hxLR.resolve_left hxl
      obtain ⟨v,hv,_⟩ := prune_exists_of_retained keep hxr hk
      rw [access,if_neg hxl,if_pos hxr]
      refine ⟨hll,ihr hlr hxr,?_,?_⟩
      · intros
        rfl
      · intro hn _
        have := (prune_none_access_iff keep x r).mp hn
        rw [hv] at this
        contradiction

def run (t : PrefRouter α) : List α → PrefRouter α
  | [] => t
  | x :: xs => run (t.access x) xs

def runFlips (t : PrefRouter α) : List α → Nat
  | [] => 0
  | x :: xs => t.accessFlips x + runFlips (t.access x) xs

/-- The commuting diagram and flip equality hold for complete histories. -/
theorem run_prune (keep : α → Bool) (xs : List α) {t u : PrefRouter α}
    (hlegal : Legal keep t) (hxs : ∀ x ∈ xs, x ∈ t.leaves ∧ keep x = true)
    (hp : t.prune keep = some u) :
    (t.run xs).prune keep = some (u.run xs) ∧ t.runFlips xs = u.runFlips xs := by
  induction xs generalizing t u with
  | nil => exact ⟨hp,rfl⟩
  | cons x xs ih =>
    obtain ⟨hx,hk⟩ := hxs x (by simp)
    obtain ⟨hs,hf⟩ := access_prune keep x hlegal hx hk hp
    have hl := legal_access keep x hlegal hx hk
    have htail : ∀ y ∈ xs, y ∈ (t.access x).leaves ∧ keep y = true := by
      intro y hy
      rw [access_leaves]
      exact hxs y (by simp [hy])
    obtain ⟨hr,hcost⟩ := ih hl htail hs
    exact ⟨hr,by simp only [runFlips,hf,hcost]⟩

theorem access_absent (x : α) (t : PrefRouter α) (hx : x ∉ t.leaves) : t.access x = t := by
  cases t with
  | leaf y => rfl
  | fork b l r =>
    have hl : x ∉ l.leaves := fun h => hx (List.mem_append_left _ h)
    have hr : x ∉ r.leaves := fun h => hx (List.mem_append_right _ h)
    simp only [access,if_neg hl,if_neg hr]

end TangoSquared.PreferredProjection.PrefRouter
