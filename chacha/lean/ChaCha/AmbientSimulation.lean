import ChaCha.PrefixOrder
import ChaCha.RestrictedRotations

namespace ChaCha.Primary

open MTR MTR.Tree

/-- At most one actual primary preference changes on this BST request. -/
def NormalizedAt (H : Nat) (t : Tree Key) (x : Key) : Prop :=
  ∀ u ∈ owners H, ∀ v ∈ owners H,
    bstPreference H (moveToRoot x t) u ≠ bstPreference H t u →
    bstPreference H (moveToRoot x t) v ≠ bstPreference H t v → u = v

/-- Ambient normalization along an actual move-to-root execution. -/
def AmbientNormalized (H : Nat) : Tree Key → List Key → Prop
  | _, [] => True
  | t, x :: xs => NormalizedAt H t x ∧ AmbientNormalized H (moveToRoot x t) xs

@[simp] theorem normalizedAt_root (H : Nat) (l r : Tree Key) (x : Key) :
    NormalizedAt H (.node l x r) x := by
  intro u hu v hv hflip
  exact (hflip (by rw [moveToRoot_root])).elim

theorem ambientNormalized_append (H : Nat) (t : Tree Key) (xs ys : List Key) :
    AmbientNormalized H t (xs ++ ys) ↔
      AmbientNormalized H t xs ∧ AmbientNormalized H (run t xs) ys := by
  induction xs generalizing t with
  | nil => simp [AmbientNormalized, run]
  | cons x xs ih =>
    simp only [List.cons_append, AmbientNormalized, run, List.foldl_cons]
    rw [ih]
    exact and_assoc.symm

theorem branch_some_of_prefix {u x : Key} (hp : u.IsPrefix x) (hlen : u.length < x.length) :
    ∃ b, branch u x = some b := by
  exact ⟨x[u.length], by simp [branch, hp, List.getElem?_eq_getElem hlen]⟩

/-- A changed preference separates the query from an old hull representative. -/
theorem changed_owner_witness {H : Nat} {t : Tree Key} {K : Set Key} {x u : Key}
    (hhull : RootedHull t K) (hxK : x ∈ K) (hlen : ∀ y ∈ K, y.length = H)
    (hu : u ∈ owners H)
    (hflip : bstPreference H (moveToRoot x t) u ≠ bstPreference H t u) :
    ∃ y ∈ K, ∃ bx bybit : Bool, bx ≠ bybit ∧
      branch u x = some bx ∧ branch u y = some bybit := by
  obtain ⟨⟨d, hd⟩, hpath⟩ := hhull x hxK
  have hrep := representative_moveToRoot (cellMin H u) (cellMax H u) x t d hd
  have hpx : u.IsPrefix x := by
    by_contra hnot
    have hout : ¬ InInterval (cellMin H u) (cellMax H u) x := by
      exact fun h => hnot ((prefix_iff_mem_cell (hlen x hxK)).2 h)
    simp only [if_neg hout] at hrep
    exact hflip (congrArg (fun z => z.bind (branch u)) hrep)
  obtain ⟨y, hyK, hyrep, hpy⟩ := cell_representative_in_hull H u x t K hhull hxK (hlen x hxK) hpx
  have hxu : u.length < x.length := by rw [hlen x hxK]; exact (mem_owners u H).1 hu
  have hyu : u.length < y.length := by rw [hlen y hyK]; exact (mem_owners u H).1 hu
  obtain ⟨bx, hbx⟩ := branch_some_of_prefix hpx hxu
  obtain ⟨bybit, hby⟩ := branch_some_of_prefix hpy hyu
  refine ⟨y, hyK, bx, bybit, ?_, hbx, hby⟩
  intro hsame
  have hin : InInterval (cellMin H u) (cellMax H u) x := (prefix_iff_mem_cell (hlen x hxK)).1 hpx
  apply hflip
  simp only [bstPreference, hrep, if_pos hin, hyrep, Option.bind_some, hbx, hby, hsame]

/-- Only the two branch nodes of the induced three-leaf reference can change. -/
theorem hull3_changed_owner {H : Nat} {a b c : Key} (A B C D : Tree Key)
    (hab : a < b) (hbc : b < c) (ha : a.length = H) (hb : b.length = H) (hc : c.length = H)
    (s : Shape3) (q : Fin 3) {u : Key} (hu : u ∈ owners H)
    (hflip : bstPreference H (moveToRoot (key3 a b c q) (hull3 a b c A B C D s)) u ≠
      bstPreference H (hull3 a b c A B C D s) u) :
    u = lcaNode a b ∨ u = lcaNode b c := by
  have hx : key3 a b c q ∈ ({a, b, c} : Set Key) := by fin_cases q <;> simp [key3]
  have hlen : ∀ y ∈ ({a, b, c} : Set Key), y.length = H := by
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl <;> assumption
  obtain ⟨y, hy, bx, bybit, hne, hbx, hby⟩ :=
    changed_owner_witness (hull3_rootedHull a b c A B C D hab hbc s) hx hlen hu hflip
  exact three_leaf_branch_owner hab hbc (ha.trans hb.symm) (hb.trans hc.symm)
    (by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hx)
    (by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hy) hbx hby hne


/-- A two-coordinate table proves ambient normalization once every changed owner
has been assigned to one of its coordinates. -/
theorem normalizedAt_of_two_coordinates {H : Nat} {t : Tree Key} {x u₀ u₁ : Key}
    (p p' : Preferences3)
    (hsupport : ∀ u ∈ owners H,
      bstPreference H (moveToRoot x t) u ≠ bstPreference H t u → u = u₀ ∨ u = u₁)
    (hbefore₀ : bstPreference H t u₀ = some p.1)
    (hbefore₁ : bstPreference H t u₁ = some p.2)
    (hafter₀ : bstPreference H (moveToRoot x t) u₀ = some p'.1)
    (hafter₁ : bstPreference H (moveToRoot x t) u₁ = some p'.2)
    (hbits : bitChanges p p' ≤ 1) : NormalizedAt H t x := by
  have hnotboth : ¬ (bstPreference H (moveToRoot x t) u₀ ≠ bstPreference H t u₀ ∧
      bstPreference H (moveToRoot x t) u₁ ≠ bstPreference H t u₁) := by
    rintro ⟨h₀, h₁⟩
    have hp₀ : p.1 ≠ p'.1 := by
      intro h
      apply h₀
      rw [hbefore₀, hafter₀, h]
    have hp₁ : p.2 ≠ p'.2 := by
      intro h
      apply h₁
      rw [hbefore₁, hafter₁, h]
    simp [bitChanges, hp₀, hp₁] at hbits
  intro u hu v hv hfu hfv
  rcases hsupport u hu hfu with rfl | rfl <;> rcases hsupport v hv hfv with rfl | rfl
  · rfl
  · exact (hnotboth ⟨hfu, hfv⟩).elim
  · exact (hnotboth ⟨hfv, hfu⟩).elim
  · rfl

/-- Which of the two three-leaf references is induced by these ordered keys. -/
def inducedReference (a b c : Key) : Reference3 :=
  if lcaDepth a b < lcaDepth b c then .rightSplit else .leftSplit

/-- One flip in the finite tour table is one flip in the full primary reference. -/
theorem hull3_normalized {H : Nat} {a b c : Key} (A B C D : Tree Key)
    (hab : a < b) (hbc : b < c) (ha : a.length = H) (hb : b.length = H) (hc : c.length = H)
    (s : Shape3) (q : Fin 3)
    (hbits : bitChanges (preferences3 (inducedReference a b c) s)
      (updatePreferences3 (inducedReference a b c) (preferences3 (inducedReference a b c) s) q) ≤ 1) :
    NormalizedAt H (hull3 a b c A B C D s) (key3 a b c q) := by
  rw [← preferences3_next] at hbits
  by_cases hd : lcaDepth a b < lcaDepth b c
  · simp only [inducedReference, if_pos hd] at hbits
    obtain ⟨hb₀, hb₁⟩ := hull3_preferences_right A B C D hab hbc ha hb hc hd s
    obtain ⟨ha₀, ha₁⟩ := hull3_preferences_right A B C D hab hbc ha hb hc hd (nextShape s q)
    apply normalizedAt_of_two_coordinates (preferences3 .rightSplit s)
      (preferences3 .rightSplit (nextShape s q))
      (fun _ hu hf => hull3_changed_owner A B C D hab hbc ha hb hc s q hu hf) hb₀ hb₁ _ _ hbits
    · rw [moveToRoot_hull3 a b c A B C D hab hbc s q]
      exact ha₀
    · rw [moveToRoot_hull3 a b c A B C D hab hbc s q]
      exact ha₁
  · have hne := (ordered_triple_lca hab hbc (ha.trans hb.symm) (hb.trans hc.symm)).1
    have hd' : lcaDepth b c < lcaDepth a b := by omega
    simp only [inducedReference, if_neg hd] at hbits
    obtain ⟨hb₀, hb₁⟩ := hull3_preferences_left A B C D hab hbc ha hb hc hd' s
    obtain ⟨ha₀, ha₁⟩ := hull3_preferences_left A B C D hab hbc ha hb hc hd' (nextShape s q)
    apply normalizedAt_of_two_coordinates (preferences3 .leftSplit s)
      (preferences3 .leftSplit (nextShape s q)) _ hb₀ hb₁ _ _ hbits
    · intro u hu hf
      exact (hull3_changed_owner A B C D hab hbc ha hb hc s q hu hf).symm
    · rw [moveToRoot_hull3 a b c A B C D hab hbc s q]
      exact ha₀
    · rw [moveToRoot_hull3 a b c A B C D hab hbc s q]
      exact ha₁

/-- Every table-certified path is normalized in the whole reference tree. -/
theorem hull3_ambientNormalized {H : Nat} {a b c : Key} (A B C D : Tree Key)
    (hab : a < b) (hbc : b < c) (ha : a.length = H) (hb : b.length = H) (hc : c.length = H)
    (s : Shape3) (qs : List (Fin 3))
    (hpath : OneFlipPath (inducedReference a b c) s qs) :
    AmbientNormalized H (hull3 a b c A B C D s) (qs.map (key3 a b c)) := by
  induction qs generalizing s with
  | nil => trivial
  | cons q qs ih =>
    obtain ⟨hbit, hrest⟩ := hpath
    constructor
    · exact hull3_normalized A B C D hab hbc ha hb hc s q (by omega)
    · rw [moveToRoot_hull3 a b c A B C D hab hbc s q]
      exact ih (nextShape s q) hrest

/-- Every hull-key request is successful, throughout any skeleton path. -/
theorem hull3_successful {a b c : Key} (A B C D : Tree Key) (hab : a < b) (hbc : b < c)
    (s : Shape3) (qs : List (Fin 3)) :
    Successful (hull3 a b c A B C D s) (qs.map (key3 a b c)) := by
  induction qs generalizing s with
  | nil => trivial
  | cons q qs ih =>
    constructor
    · exact ⟨shapeDepth s q, searchDepth_hull3 a b c A B C D hab hbc s q⟩
    · rw [moveToRoot_hull3 a b c A B C D hab hbc s q]
      exact ih (nextShape s q)

/-- The concrete ambient three-key simulation with a universal constant. -/
theorem hull3_ambient_simulation {H : Nat} {a b c : Key} (A B C D : Tree Key)
    (hab : a < b) (hbc : b < c) (ha : a.length = H) (hb : b.length = H) (hc : c.length = H)
    (s t : Shape3) :
    ∃ qs : List Key,
      run (hull3 a b c A B C D s) qs = hull3 a b c A B C D t ∧
      runCost (hull3 a b c A B C D s) qs ≤ 15 ∧
      AmbientNormalized H (hull3 a b c A B C D s) qs ∧
      Successful (hull3 a b c A B C D s) qs ∧
      ∀ x ∈ qs, x.length = H := by
  let r := inducedReference a b c
  let ranks := pathBetween r s t
  obtain ⟨hsize, hend, hnorm, hcost⟩ := pathBetween_spec r s t
  refine ⟨ranks.map (key3 a b c), ?_, ?_, ?_, ?_, ?_⟩
  · rw [run_hull3 a b c A B C D hab hbc s ranks]
    exact congrArg (hull3 a b c A B C D) hend
  · rw [runCost_hull3 a b c A B C D hab hbc s ranks]
    exact hcost
  · exact hull3_ambientNormalized A B C D hab hbc ha hb hc s ranks hnorm
  · exact hull3_successful A B C D hab hbc s ranks
  · intro x hx
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
    fin_cases q <;> simpa [key3] using (by assumption : _)


/-- Two hull keys can change only the primary node separating those two keys. -/
theorem hull2_normalized {H : Nat} {t : Tree Key} {a b x : Key}
    (hhull : RootedHull t {a, b}) (ha : a.length = H) (hb : b.length = H)
    (hx : x ∈ ({a, b} : Set Key)) : NormalizedAt H t x := by
  have howner : ∀ u ∈ owners H,
      bstPreference H (moveToRoot x t) u ≠ bstPreference H t u → u = lcaNode a b := by
    intro u hu hflip
    have hlen : ∀ y ∈ ({a, b} : Set Key), y.length = H := by
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl <;> assumption
    obtain ⟨y, hy, bx, bybit, hne, hbx, hby⟩ := changed_owner_witness hhull hx hlen hu hflip
    have hneq : x ≠ y := by
      intro heq
      subst y
      rw [hbx] at hby
      exact hne (Option.some.inj hby)
    have hlca := owner_eq_lcaNode_of_branch_ne hbx hby hne
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact (hneq rfl).elim
    · exact hlca
    · exact hlca.trans (lcaNode_comm _ _)
    · exact (hneq rfl).elim
  intro u hu v hv hfu hfv
  exact (howner u hu hfu).trans (howner v hv hfv).symm

private theorem ordered_left {l r : Tree Key} {x : Key} (h : Ordered (.node l x r)) :
    Ordered l := by
  simp only [Ordered, inorder, List.pairwise_append] at h ⊢
  exact h.1.1

private theorem ordered_right {l r : Tree Key} {x : Key} (h : Ordered (.node l x r)) :
    Ordered r := by
  simp only [Ordered, inorder, List.pairwise_append] at h ⊢
  exact h.2.1

private theorem ordered_left_lt {l r : Tree Key} {x y : Key}
    (h : Ordered (.node l x r)) (hy : y ∈ inorder l) : y < x := by
  simp only [Ordered, inorder, List.pairwise_append] at h
  exact h.1.2.2 y hy x (by simp)

private theorem ordered_lt_right {l r : Tree Key} {x y : Key}
    (h : Ordered (.node l x r)) (hy : y ∈ inorder r) : x < y := by
  simp only [Ordered, inorder, List.pairwise_append] at h
  exact h.2.2 x (by simp) y hy

private theorem ordered_hull3_keys {a b c : Key} {A B C D : Tree Key} (s : Shape3)
    (h : Ordered (hull3 a b c A B C D s)) : a < b ∧ b < c := by
  cases s with
  | t1 => exact ⟨ordered_lt_right h (by simp [inorder]),
      ordered_lt_right (ordered_right h) (by simp [inorder])⟩
  | t2 => exact ⟨ordered_lt_right h (by simp [inorder]),
      ordered_left_lt (ordered_right h) (by simp [inorder])⟩
  | t3 => exact ⟨ordered_left_lt h (by simp [inorder]), ordered_lt_right h (by simp [inorder])⟩
  | t4 => exact ⟨ordered_lt_right (ordered_left h) (by simp [inorder]),
      ordered_left_lt h (by simp [inorder])⟩
  | t5 => exact ⟨ordered_left_lt (ordered_left h) (by simp [inorder]),
      ordered_left_lt h (by simp [inorder])⟩

private theorem hull3_ambient_simulation_of_ordered {H : Nat} {a b c : Key} (A B C D : Tree Key)
    (s t : Shape3) (horder : Ordered (hull3 a b c A B C D s))
    (hheight : ∀ x ∈ inorder (hull3 a b c A B C D s), x.length = H) :
    ∃ qs : List Key,
      run (hull3 a b c A B C D s) qs = hull3 a b c A B C D t ∧
      runCost (hull3 a b c A B C D s) qs ≤ 15 ∧
      AmbientNormalized H (hull3 a b c A B C D s) qs ∧
      Successful (hull3 a b c A B C D s) qs ∧
      ∀ x ∈ qs, x.length = H := by
  obtain ⟨hab, hbc⟩ := ordered_hull3_keys s horder
  have ha : a.length = H := hheight a (by cases s <;> simp [hull3, inorder])
  have hb : b.length = H := hheight b (by cases s <;> simp [hull3, inorder])
  have hc : c.length = H := hheight c (by cases s <;> simp [hull3, inorder])
  exact hull3_ambient_simulation A B C D hab hbc ha hb hc s t

/-- Every legal shallow rotation admits a constant-cost, fully normalized actual
MTR replacement, with the same hanging subtrees and the same final physical tree. -/
theorem restrictedStep_normalized_simulation {H : Nat} {t u : Tree Key}
    (hstep : RestrictedStep t u) (horder : Ordered t)
    (hheight : ∀ x ∈ inorder t, x.length = H) :
    ∃ qs : List Key, run t qs = u ∧ runCost t qs ≤ 15 ∧
      AmbientNormalized H t qs ∧ Successful t qs ∧ ∀ x ∈ qs, x.length = H := by
  cases hstep with
  | rootRight A B C a b =>
    have hab : a < b := ordered_left_lt horder (by simp [inorder])
    have ha := hheight a (by simp [inorder])
    have hb := hheight b (by simp [inorder])
    have hhull : RootedHull (.node (.node A a B) b C) {a, b} := by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl <;>
        simp [searchDepth, searchPath, hab]
    have hnorm := hull2_normalized hhull ha hb (by simp : a ∈ ({a, b} : Set Key))
    refine ⟨[a], ?_, ?_, ?_, ?_, ?_⟩
    · simp [run, moveToRoot, hab, rotateRight]
    · simp [runCost, searchDepth, hab]
    · exact ⟨hnorm, trivial⟩
    · exact ⟨⟨1, by simp [searchDepth, hab]⟩, trivial⟩
    · simpa using ha
  | rootLeft A B C a b =>
    have hab : a < b := ordered_lt_right horder (by simp [inorder])
    have ha := hheight a (by simp [inorder])
    have hb := hheight b (by simp [inorder])
    have hhull : RootedHull (.node A a (.node B b C)) {a, b} := by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl <;>
        simp [searchDepth, searchPath, hab, not_lt.mpr (le_of_lt hab)]
    have hnorm := hull2_normalized hhull ha hb (by simp : b ∈ ({a, b} : Set Key))
    refine ⟨[b], ?_, ?_, ?_, ?_, ?_⟩
    · simp [run, moveToRoot, hab, not_lt.mpr (le_of_lt hab), rotateLeft]
    · simp [runCost, searchDepth, hab, not_lt.mpr (le_of_lt hab)]
    · exact ⟨hnorm, trivial⟩
    · exact ⟨⟨1, by simp [searchDepth, hab, not_lt.mpr (le_of_lt hab)]⟩, trivial⟩
    · simpa using hb
  | rightRight A B C D a b c =>
    exact hull3_ambient_simulation_of_ordered A B C D .t2 .t1 horder hheight
  | rightLeft A B C D a b c =>
    exact hull3_ambient_simulation_of_ordered A B C D .t1 .t2 horder hheight
  | leftRight A B C D a b c =>
    exact hull3_ambient_simulation_of_ordered A B C D .t5 .t4 horder hheight
  | leftLeft A B C D a b c =>
    exact hull3_ambient_simulation_of_ordered A B C D .t4 .t5 horder hheight

end ChaCha.Primary
