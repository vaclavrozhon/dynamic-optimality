import TangoSquared.Primary

/-!
# Concrete one-flip histories and the first-return property

Preferences are the last child actually accessed at each primary prefix, with
arbitrary fixed defaults before the first access.  A one-flip query changes at
most one of these concrete preferences.  The return lemmas below derive their
conclusion from this definition, rather than assuming a return property.
-/

namespace TangoSquared
namespace NormalizedWords

open Primary

/-- The preferred child after the given actual access history. -/
def preference (initial : Key → Bool) (history : List Key) (u : Key) : Bool :=
  (history.filterMap (branch u)).getLastD (initial u)

/-- Query `x` changes the preferred child at primary node `u`. -/
def Flips (initial : Key → Bool) (history : List Key) (x u : Key) : Prop :=
  ∃ b, branch u x = some b ∧ preference initial history u ≠ b

/-- At most one internal primary node changes at this query. -/
def OneFlip (initial : Key → Bool) (H : Nat) (history : List Key) (x : Key) : Prop :=
  ∀ u ∈ owners H, ∀ v ∈ owners H,
    Flips initial history x u → Flips initial history x v → u = v

/-- Every query in the word changes at most one primary preference. -/
def Normalized (initial : Key → Bool) (H : Nat) (word : List Key) : Prop :=
  ∀ history x future, word = history ++ x :: future → OneFlip initial H history x

/-- A last access inside a primary child sets the preference to that child. -/
theorem preference_append_last (initial : Key → Bool) (history : List Key)
    (x u : Key) (b : Bool) (h : branch u x = some b) :
    preference initial (history ++ [x]) u = b := by
  simp [preference, h]

/-- Accesses outside a node's subtree leave its preference unchanged. -/
theorem preference_append_silent (initial : Key → Bool) (history away : List Key) (u : Key)
    (h : ∀ x ∈ away, branch u x = none) :
    preference initial (history ++ away) u = preference initial history u := by
  have hempty : away.filterMap (branch u) = [] := List.filterMap_eq_nil_iff.mpr h
  simp [preference, hempty]

/-- Distinct equal-length keys diverge before either key ends. -/
theorem lcaDepth_lt_of_ne {p x : Key} (hlen : p.length = x.length) (hne : p ≠ x) :
    lcaDepth p x < p.length := by
  have hle := lcaDepth_le_left p x
  by_contra hn
  have he : lcaDepth p x = p.length := by omega
  have ht := take_lca_eq p x
  rw [he, List.take_length, hlen, List.take_length] at ht
  exact hne ht

/-- An outside key separates from an inside key strictly above the cell root. -/
theorem outside_lca_lt {cell q x : Key}
    (hx : cell.IsPrefix x) (hq : ¬ cell.IsPrefix q) :
    lcaDepth q x < cell.length := by
  by_contra hn
  have hdepth : cell.length ≤ lcaDepth q x := by omega
  have hqdepth : cell.length ≤ q.length := hdepth.trans (lcaDepth_le_left q x)
  have ht : q.take cell.length = x.take cell.length :=
    (take_eq_iff hqdepth hx.length_le).2 hdepth
  apply hq
  apply List.prefix_iff_eq_take.mpr
  rw [ht]
  exact List.prefix_iff_eq_take.mp hx

/-- At a proper LCA, the two accessed child labels are opposite. -/
theorem branches_at_proper_lca {p x : Key}
    (hp : lcaDepth p x < p.length) (hx : lcaDepth p x < x.length) :
    ∃ a b : Bool, a ≠ b ∧
      branch (x.take (lcaDepth p x)) p = some a ∧
      branch (x.take (lcaDepth p x)) x = some b := by
  refine ⟨p[lcaDepth p x], x[lcaDepth p x], ?_, ?_, ?_⟩
  · intro heq
    apply getElem?_ne_at_lca p x hp hx
    simpa only [List.getElem?_eq_getElem hp, List.getElem?_eq_getElem hx] using
      congrArg some heq
  · rw [branch_at_lca_left, List.getElem?_eq_getElem hp]
  · rw [branch_at_lca_right, List.getElem?_eq_getElem hx]

/-- A nonempty outside excursion must return to exactly the last key accessed
inside the cell.  Otherwise the returning query changes both an internal
preference and a preference strictly above the cell. -/
theorem first_return (initial : Key → Bool) (H : Nat)
    (history away : List Key) (cell p q x : Key)
    (hpH : p.length = H) (hqH : q.length = H) (hxH : x.length = H)
    (hp : cell.IsPrefix p) (hx : cell.IsPrefix x)
    (haway : ∀ y ∈ away ++ [q], ¬ cell.IsPrefix y)
    (hone : OneFlip initial H ((history ++ [p]) ++ (away ++ [q])) x) : x = p := by
  by_contra hne
  have hpx : p ≠ x := Ne.symm hne
  have he : lcaDepth p x < p.length := lcaDepth_lt_of_ne (hpH.trans hxH.symm) hpx
  have hex : lcaDepth p x < x.length := by omega
  let inside := x.take (lcaDepth p x)
  have hinside_len : inside.length = lcaDepth p x := by
    simp [inside, List.length_take, Nat.min_eq_left (lcaDepth_le_right p x)]
  have hinside_owner : inside ∈ owners H := (mem_owners inside H).2 (by omega)
  have hcell_inside : cell.IsPrefix inside := prefix_take_lca hp hx
  obtain ⟨a, b, hab, hpa, hxb⟩ := branches_at_proper_lca he hex
  have hsilent : ∀ y ∈ away ++ [q], branch inside y = none := by
    intro y hy
    have hn : ¬ inside.IsPrefix y := fun h => haway y hy (hcell_inside.trans h)
    simp [branch, hn]
  have hpref_inside : preference initial ((history ++ [p]) ++ (away ++ [q])) inside = a := by
    rw [preference_append_silent initial (history ++ [p]) (away ++ [q]) inside hsilent]
    exact preference_append_last initial history p inside a hpa
  have hflip_inside : Flips initial ((history ++ [p]) ++ (away ++ [q])) x inside := by
    exact ⟨b, hxb, by simpa only [hpref_inside] using hab⟩
  have hqout : ¬ cell.IsPrefix q := haway q (by simp)
  have hqx : q ≠ x := fun heq => hqout (heq ▸ hx)
  have heq : lcaDepth q x < q.length := lcaDepth_lt_of_ne (hqH.trans hxH.symm) hqx
  have heqx : lcaDepth q x < x.length := by omega
  let outside := x.take (lcaDepth q x)
  have houtside_len : outside.length = lcaDepth q x := by
    simp [outside, List.length_take, Nat.min_eq_left (lcaDepth_le_right q x)]
  have houtside_owner : outside ∈ owners H := (mem_owners outside H).2 (by omega)
  obtain ⟨c, d, hcd, hqc, hxd⟩ := branches_at_proper_lca heq heqx
  have hpref_outside : preference initial ((history ++ [p]) ++ (away ++ [q])) outside = c := by
    rw [← List.append_assoc]
    exact preference_append_last initial ((history ++ [p]) ++ away) q outside c hqc
  have hflip_outside : Flips initial ((history ++ [p]) ++ (away ++ [q])) x outside := by
    exact ⟨d, hxd, by simpa only [hpref_outside] using hcd⟩
  have hsame := hone inside hinside_owner outside houtside_owner hflip_inside hflip_outside
  have hlt : outside.length < cell.length := by
    rw [houtside_len]
    exact outside_lca_lt hx hqout
  have hle : cell.length ≤ inside.length := hcell_inside.length_le
  rw [hsame] at hle
  omega

/-- Distinct consecutive owner-local keys in a normalized word are consecutive
global queries: an intervening outside excursion would force an identical return. -/
theorem local_change_is_global_step (initial : Key → Bool) (H : Nat)
    (history away future : List Key) (cell p x : Key)
    (hpH : p.length = H) (hxH : x.length = H)
    (hawayH : ∀ y ∈ away, y.length = H)
    (hp : cell.IsPrefix p) (hx : cell.IsPrefix x)
    (haway : ∀ y ∈ away, ¬ cell.IsPrefix y)
    (hnormal : Normalized initial H ((history ++ [p]) ++ away ++ x :: future))
    (hne : p ≠ x) : away = [] := by
  induction away using List.reverseRecOn with
  | nil => rfl
  | append_singleton middle q ih =>
    have hqH : q.length = H := hawayH q (by simp)
    have hone : OneFlip initial H ((history ++ [p]) ++ (middle ++ [q])) x :=
      hnormal _ x future rfl
    have heq := first_return initial H history middle cell p q x
      hpH hqH hxH hp hx haway hone
    exact False.elim (hne heq.symm)

/-- In particular, changing the fine cell within a coarse owner always has a
globally consecutive source pair.  The fine projection can be arbitrary. -/
theorem fine_change_is_global_step {F : Type*} (fine : Key → F)
    (initial : Key → Bool) (H : Nat) (history away future : List Key) (cell p x : Key)
    (hpH : p.length = H) (hxH : x.length = H)
    (hawayH : ∀ y ∈ away, y.length = H)
    (hp : cell.IsPrefix p) (hx : cell.IsPrefix x)
    (haway : ∀ y ∈ away, ¬ cell.IsPrefix y)
    (hnormal : Normalized initial H ((history ++ [p]) ++ away ++ x :: future))
    (hfine : fine p ≠ fine x) : away = [] := by
  apply local_change_is_global_step initial H history away future cell p x
    hpH hxH hawayH hp hx haway hnormal
  intro heq
  exact hfine (congrArg fine heq)

/-- The LCA of two distinct consecutive global requests necessarily flips. -/
theorem consecutive_flip_lca (initial : Key → Bool) (history : List Key) {p x : Key}
    (hlen : p.length = x.length) (hne : p ≠ x) :
    Flips initial (history ++ [p]) x (x.take (lcaDepth p x)) := by
  have hp := lcaDepth_lt_of_ne hlen hne
  have hx : lcaDepth p x < x.length := by omega
  obtain ⟨a, b, hab, hpa, hxb⟩ := branches_at_proper_lca hp hx
  refine ⟨b, hxb, ?_⟩
  rw [preference_append_last initial history p _ a hpa]
  exact hab

/-- In a normalized query, that LCA is the unique changed primary node. -/
theorem unique_flip_is_lca (initial : Key → Bool) (H : Nat) (history : List Key)
    {p x u : Key} (hp : p.length = H) (hx : x.length = H) (hne : p ≠ x)
    (hone : OneFlip initial H (history ++ [p]) x)
    (hu : u ∈ owners H) (hflip : Flips initial (history ++ [p]) x u) :
    u = x.take (lcaDepth p x) := by
  have hlen : p.length = x.length := hp.trans hx.symm
  have hproper := lcaDepth_lt_of_ne hlen hne
  have hw : x.take (lcaDepth p x) ∈ owners H := by
    apply (mem_owners _ _).2
    rw [List.length_take, Nat.min_eq_left (lcaDepth_le_right p x)]
    omega
  exact hone u hu _ hw hflip (consecutive_flip_lca initial history hlen hne)

/-- Queries that either miss a node or use its current child preserve its preference. -/
theorem preference_append_same (initial : Key → Bool) (history away : List Key)
    (u : Key) (a : Bool) (hstart : preference initial history u = a)
    (hside : ∀ x ∈ away, branch u x = none ∨ branch u x = some a) :
    preference initial (history ++ away) u = a := by
  induction away using List.reverseRecOn with
  | nil => simpa using hstart
  | append_singleton as x ih =>
    have hxs : ∀ y ∈ as, branch u y = none ∨ branch u y = some a := by
      intro y hy
      exact hside y (by simp [hy])
    have hprev := ih hxs
    rw [← List.append_assoc]
    rcases hside x (by simp) with hnone | hsome
    · rw [preference_append_silent initial (history ++ as) [x] u (by simpa using hnone)]
      exact hprev
    · exact preference_append_last initial (history ++ as) x u a hsome

end NormalizedWords
end TangoSquared
