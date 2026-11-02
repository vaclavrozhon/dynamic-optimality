import ChaCha.Primary
import ChaCha.Recency
import Mathlib.Data.List.Lex

/-!
# Primary prefix cells and the actual key order

The order is Mathlib's lexicographic linear order on Boolean words. This file
proves the convexity and induced-reference geometry needed to pass from actual
BST interval representatives to the primary preference count.
-/

namespace ChaCha.Primary

/-- Taking a prefix is monotone in the lexicographic key order. -/
theorem take_mono_lex {α : Type*} [LinearOrder α] {x y : List α}
    (h : x ≤ y) (d : Nat) : x.take d ≤ y.take d := by
  rcases lt_or_eq_of_le h with hlt | rfl
  · induction hlt generalizing d with
    | nil =>
      cases d with
      | zero => exact le_rfl
      | succ d => exact le_of_lt List.Lex.nil
    | @rel a b xs ys hab =>
      cases d with
      | zero => simp
      | succ d => exact le_of_lt (List.Lex.rel hab)
    | @cons a xs ys hxy ih =>
      cases d with
      | zero => simp
      | succ d => simpa using List.cons_le_cons a (ih (le_of_lt hxy) d)
  · rfl

/-- A primary subtree is convex in key order. -/
theorem prefix_convex {u x y z : Key} (hx : u.IsPrefix x) (hz : u.IsPrefix z)
    (hxy : x ≤ y) (hyz : y ≤ z) : u.IsPrefix y := by
  have hl := take_mono_lex hxy u.length
  have hr := take_mono_lex hyz u.length
  rw [← List.prefix_iff_eq_take.mp hx] at hl
  rw [← List.prefix_iff_eq_take.mp hz] at hr
  exact List.prefix_iff_eq_take.mpr (le_antisymm hr hl).symm

/-- Equal first bits may be stripped from a strict lexicographic comparison. -/
theorem cons_lt_cons_iff (a : Bool) (x y : Key) :
    a :: x < a :: y ↔ x < y := List.lex_cons_iff

/-- Any false-headed key precedes any true-headed key. -/
theorem false_cons_lt_true_cons (x y : Key) : false :: x < true :: y :=
  List.Lex.rel (by decide)

/-- For three distinct same-depth leaves, their adjacent-pair LCAs are different,
and the outer-pair LCA is the shallower one. These are the two induced branches. -/
theorem ordered_triple_lca {a b c : Key} (hab : a < b) (hbc : b < c)
    (hlenab : a.length = b.length) (hlenbc : b.length = c.length) :
    lcaDepth a b ≠ lcaDepth b c ∧
      lcaDepth a c = min (lcaDepth a b) (lcaDepth b c) := by
  induction a generalizing b c with
  | nil =>
    have hb : b = [] := List.length_eq_zero_iff.mp hlenab.symm
    subst b
    exact (lt_irrefl [] hab).elim
  | cons xa as ih =>
    cases b with
    | nil => simp at hlenab
    | cons xb bs =>
      cases c with
      | nil => simp at hlenbc
      | cons xc cs =>
        simp only [List.length_cons, Nat.add_right_cancel_iff] at hlenab hlenbc
        cases xa <;> cases xb <;> cases xc
        · obtain ⟨hne, heq⟩ := ih ((cons_lt_cons_iff _ _ _).1 hab)
            ((cons_lt_cons_iff _ _ _).1 hbc) hlenab hlenbc
          simp [lcaDepth, hne, heq, Nat.add_min_add_left]
        · simp [lcaDepth]
        · exact (not_lt_of_gt (false_cons_lt_true_cons cs bs) hbc).elim
        · simp [lcaDepth]; omega
        · exact (not_lt_of_gt (false_cons_lt_true_cons bs as) hab).elim
        · exact (not_lt_of_gt (false_cons_lt_true_cons bs as) hab).elim
        · exact (not_lt_of_gt (false_cons_lt_true_cons cs bs) hbc).elim
        · obtain ⟨hne, heq⟩ := ih ((cons_lt_cons_iff _ _ _).1 hab)
            ((cons_lt_cons_iff _ _ _).1 hbc) hlenab hlenbc
          simp [lcaDepth, hne, heq, Nat.add_min_add_left]


/-- Fixed-length Boolean words are bounded by the all-left and all-right words. -/
theorem replicate_false_le (x : Key) : List.replicate x.length false ≤ x := by
  induction x with
  | nil => rfl
  | cons a xs ih =>
    cases a
    · simpa only [List.length_cons, List.replicate_succ] using List.cons_le_cons false ih
    · exact le_of_lt (false_cons_lt_true_cons _ _)

theorem le_replicate_true (x : Key) : x ≤ List.replicate x.length true := by
  induction x with
  | nil => rfl
  | cons a xs ih =>
    cases a
    · exact le_of_lt (false_cons_lt_true_cons _ _)
    · simpa only [List.length_cons, List.replicate_succ] using List.cons_le_cons true ih

/-- Adding a common prefix preserves lexicographic order. -/
theorem append_prefix_le {x y : Key} (h : x ≤ y) (u : Key) : u ++ x ≤ u ++ y := by
  rcases lt_or_eq_of_le h with h | rfl
  · exact le_of_lt (List.Lex.append_left _ h u)
  · rfl

/-- Extremal leaves of a primary subtree inside a height-H complete reference. -/
def cellMin (H : Nat) (u : Key) : Key := u ++ List.replicate (H - u.length) false

def cellMax (H : Nat) (u : Key) : Key := u ++ List.replicate (H - u.length) true

theorem prefix_cellMin (H : Nat) (u : Key) : u.IsPrefix (cellMin H u) :=
  List.prefix_append _ _

theorem prefix_cellMax (H : Nat) (u : Key) : u.IsPrefix (cellMax H u) :=
  List.prefix_append _ _

theorem cellMin_length {H : Nat} {u : Key} (hu : u.length ≤ H) :
    (cellMin H u).length = H := by simp [cellMin]; omega

theorem cellMax_length {H : Nat} {u : Key} (hu : u.length ≤ H) :
    (cellMax H u).length = H := by simp [cellMax]; omega

/-- The exact closed key interval corresponding to a primary prefix. -/
theorem prefix_iff_mem_cell {H : Nat} {u x : Key} (hx : x.length = H) :
    u.IsPrefix x ↔ cellMin H u ≤ x ∧ x ≤ cellMax H u := by
  constructor
  · intro h
    obtain ⟨tail, rfl⟩ := h
    have htail : tail.length = H - u.length := by
      simp only [List.length_append] at hx
      omega
    constructor
    · simpa [cellMin, htail] using append_prefix_le (replicate_false_le tail) u
    · simpa [cellMax, htail] using append_prefix_le (le_replicate_true tail) u
  · rintro ⟨hlo, hhi⟩
    exact prefix_convex (prefix_cellMin H u) (prefix_cellMax H u) hlo hhi

/-- The representative of a nonempty primary subtree is an actual hull key. -/
theorem cell_representative_in_hull (H : Nat) (u x : Key)
    (t : MTR.Tree Key) (K : Set Key) (hhull : MTR.Tree.RootedHull t K)
    (hx : x ∈ K) (hlen : x.length = H) (hprefix : u.IsPrefix x) :
    ∃ y ∈ K, MTR.Tree.representative (cellMin H u) (cellMax H u) t = some y ∧
      u.IsPrefix y := by
  obtain ⟨hlo, hhi⟩ := (prefix_iff_mem_cell hlen).1 hprefix
  obtain ⟨y, hyK, hy, hly, hhy⟩ :=
    MTR.Tree.representative_in_rootedHull (cellMin H u) (cellMax H u) x t K hhull hx hlo hhi
  exact ⟨y, hyK, hy,
    prefix_convex (prefix_cellMin H u) (prefix_cellMax H u) hly hhy⟩


/-- The actual primary node at the LCA of two leaves. -/
def lcaNode (x y : Key) : Key := y.take (lcaDepth x y)

theorem lcaNode_comm (x y : Key) : lcaNode x y = lcaNode y x := by
  simp only [lcaNode, lcaDepth_comm y x]
  exact (take_lca_eq x y).symm

/-- Different child bits uniquely identify the primary node as the pair's LCA. -/
theorem owner_eq_lcaNode_of_branch_ne {u x y : Key} {a b : Bool}
    (hx : branch u x = some a) (hy : branch u y = some b) (hne : a ≠ b) :
    u = lcaNode x y := by
  have hpx : u.IsPrefix x := by
    by_contra hp
    simp [branch, hp] at hx
  have hpy : u.IsPrefix y := by
    by_contra hp
    simp [branch, hp] at hy
  have htake : x.take u.length = y.take u.length := by
    rw [← List.prefix_iff_eq_take.mp hpx, ← List.prefix_iff_eq_take.mp hpy]
  have hle : u.length ≤ lcaDepth x y :=
    (take_eq_iff hpx.length_le hpy.length_le).1 htake
  have heq : u.length = lcaDepth x y := by
    by_contra h
    have hlt : u.length < lcaDepth x y := by omega
    have hbits := getElem?_eq_of_lt_lca hlt
    simp only [branch, if_pos hpx] at hx
    simp only [branch, if_pos hpy] at hy
    rw [hx, hy] at hbits
    exact hne (Option.some.inj hbits)
  rw [lcaNode, ← heq]
  exact List.prefix_iff_eq_take.mp hpy

/-- The outer-pair branch is one of the two adjacent-pair branches. -/
theorem lcaNode_outer_eq_adjacent {a b c : Key} (hab : a < b) (hbc : b < c)
    (hlenab : a.length = b.length) (hlenbc : b.length = c.length) :
    lcaNode a c = lcaNode a b ∨ lcaNode a c = lcaNode b c := by
  obtain ⟨hne, hmin⟩ := ordered_triple_lca hab hbc hlenab hlenbc
  by_cases hlt : lcaDepth a b < lcaDepth b c
  · left
    have hd : lcaDepth a c = lcaDepth a b := by rw [hmin, Nat.min_eq_left (Nat.le_of_lt hlt)]
    rw [lcaNode, ← take_lca_eq a c, hd]
    exact take_lca_eq a b
  · right
    have hd : lcaDepth a c = lcaDepth b c := by
      rw [hmin, Nat.min_eq_right (by omega)]
    simp only [lcaNode, hd]

/-- All branching owners of an induced three-leaf reference are its two LCAs. -/
theorem three_leaf_branch_owner {a b c u x y : Key}
    (hab : a < b) (hbc : b < c) (hlenab : a.length = b.length) (hlenbc : b.length = c.length)
    (hx : x = a ∨ x = b ∨ x = c) (hy : y = a ∨ y = b ∨ y = c)
    {bx bybit : Bool} (hbx : branch u x = some bx) (hby : branch u y = some bybit)
    (hne : bx ≠ bybit) : u = lcaNode a b ∨ u = lcaNode b c := by
  have hxy : x ≠ y := by
    intro heq
    subst y
    rw [hbx] at hby
    exact hne (Option.some.inj hby)
  have hu := owner_eq_lcaNode_of_branch_ne hbx hby hne
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
  · exact (hxy rfl).elim
  · exact Or.inl hu
  · exact (lcaNode_outer_eq_adjacent hab hbc hlenab hlenbc).imp
      (fun h => hu.trans h) (fun h => hu.trans h)
  · exact Or.inl (hu.trans (lcaNode_comm _ _))
  · exact (hxy rfl).elim
  · exact Or.inr hu
  · rw [lcaNode_comm _ _] at hu
    exact (lcaNode_outer_eq_adjacent hab hbc hlenab hlenbc).imp
      (fun h => hu.trans h) (fun h => hu.trans h)
  · exact Or.inr (hu.trans (lcaNode_comm _ _))
  · exact (hxy rfl).elim


/-- Lexicographic key order fixes the two child bits at a proper LCA. -/
theorem bits_at_lca_of_lt {x y : Key} (hxy : x < y) (hlen : x.length = y.length) :
    x[lcaDepth x y]? = some false ∧ y[lcaDepth x y]? = some true := by
  induction x generalizing y with
  | nil =>
    have hy : y = [] := List.length_eq_zero_iff.mp hlen.symm
    subst y
    exact (lt_irrefl [] hxy).elim
  | cons a xs ih =>
    cases y with
    | nil => simp at hlen
    | cons b ys =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      cases a <;> cases b
      · have ht := ih ((cons_lt_cons_iff _ _ _).1 hxy) hlen
        simpa only [lcaDepth, if_pos rfl, ↓reduceIte, Nat.add_comm 1, List.getElem?_cons_succ] using ht
      · simp [lcaDepth]
      · exact (not_lt_of_gt (false_cons_lt_true_cons ys xs) hxy).elim
      · have ht := ih ((cons_lt_cons_iff _ _ _).1 hxy) hlen
        simpa only [lcaDepth, if_pos rfl, ↓reduceIte, Nat.add_comm 1, List.getElem?_cons_succ] using ht

theorem branches_lca_of_lt {x y : Key} (hxy : x < y) (hlen : x.length = y.length) :
    branch (lcaNode x y) x = some false ∧ branch (lcaNode x y) y = some true := by
  simpa only [lcaNode, branch_at_lca_left, branch_at_lca_right] using bits_at_lca_of_lt hxy hlen

theorem lcaNode_length (x y : Key) : (lcaNode x y).length = lcaDepth x y := by
  simp [lcaNode, List.length_take, Nat.min_eq_left (lcaDepth_le_right x y)]

theorem prefix_lcaNode_left (x y : Key) : (lcaNode x y).IsPrefix x :=
  take_lca_prefix_left x y

theorem prefix_lcaNode_right (x y : Key) : (lcaNode x y).IsPrefix y :=
  take_lca_prefix_right x y

/-- In a | (b,c), the lower owner excludes a. -/
theorem not_prefix_lower_right {a b c : Key} (h : lcaDepth a b < lcaDepth b c) :
    ¬ (lcaNode b c).IsPrefix a := by
  intro hp
  have hpb := prefix_lcaNode_left b c
  have ht : a.take (lcaNode b c).length = b.take (lcaNode b c).length := by
    rw [← List.prefix_iff_eq_take.mp hp, ← List.prefix_iff_eq_take.mp hpb]
  have hd := (take_eq_iff hp.length_le hpb.length_le).1 ht
  rw [lcaNode_length] at hd
  omega

/-- In (a,b) | c, the lower owner excludes c. -/
theorem not_prefix_lower_left {a b c : Key} (h : lcaDepth b c < lcaDepth a b) :
    ¬ (lcaNode a b).IsPrefix c := by
  intro hp
  have hpb := prefix_lcaNode_right a b
  have ht : b.take (lcaNode a b).length = c.take (lcaNode a b).length := by
    rw [← List.prefix_iff_eq_take.mp hpb, ← List.prefix_iff_eq_take.mp hp]
  have hd := (take_eq_iff hpb.length_le hp.length_le).1 ht
  rw [lcaNode_length] at hd
  omega

theorem lt_cellMin_of_lt_not_prefix {H : Nat} {u x y : Key}
    (hx : x.length = H) (hy : y.length = H) (hxy : x < y)
    (hpy : u.IsPrefix y) (hpx : ¬ u.IsPrefix x) : x < cellMin H u := by
  obtain ⟨hly, hhy⟩ := (prefix_iff_mem_cell hy).1 hpy
  have hxh : x ≤ cellMax H u := le_trans (le_of_lt hxy) hhy
  by_contra h
  have hlx : cellMin H u ≤ x := le_of_not_gt h
  exact hpx ((prefix_iff_mem_cell hx).2 ⟨hlx, hxh⟩)

theorem cellMax_lt_of_lt_not_prefix {H : Nat} {u x y : Key}
    (hx : x.length = H) (hy : y.length = H) (hxy : x < y)
    (hpx : u.IsPrefix x) (hpy : ¬ u.IsPrefix y) : cellMax H u < y := by
  obtain ⟨hlx, hhx⟩ := (prefix_iff_mem_cell hx).1 hpx
  have hyl : cellMin H u ≤ y := le_trans hlx (le_of_lt hxy)
  by_contra h
  have hhy : y ≤ cellMax H u := le_of_not_gt h
  exact hpy ((prefix_iff_mem_cell hy).2 ⟨hyl, hhy⟩)

/-- An actual BST's preference at a primary owner, read from its interval representative. -/
def bstPreference (H : Nat) (t : MTR.Tree Key) (u : Key) : Option Bool :=
  (MTR.Tree.representative (cellMin H u) (cellMax H u) t).bind (branch u)


theorem prefix_of_branch_some {u x : Key} {b : Bool} (h : branch u x = some b) :
    u.IsPrefix x := by
  by_contra hn
  simp [branch, hn] at h

/-- Actual BST representative bits for the a | (b,c) induced reference. -/
theorem hull3_preferences_right {H : Nat} {a b c : Key}
    (A B C D : MTR.Tree Key) (hab : a < b) (hbc : b < c)
    (ha : a.length = H) (hb : b.length = H) (hc : c.length = H)
    (hdepth : lcaDepth a b < lcaDepth b c) (s : MTR.Shape3) :
    bstPreference H (MTR.hull3 a b c A B C D s) (lcaNode a b) =
      some (MTR.preferences3 .rightSplit s).1 ∧
    bstPreference H (MTR.hull3 a b c A B C D s) (lcaNode b c) =
      some (MTR.preferences3 .rightSplit s).2 := by
  have hablen : a.length = b.length := ha.trans hb.symm
  have hbclen : b.length = c.length := hb.trans hc.symm
  obtain ⟨htopa, htopb⟩ := branches_lca_of_lt hab hablen
  obtain ⟨hlowb, hlowc⟩ := branches_lca_of_lt hbc hbclen
  have htopc : branch (lcaNode a b) c = some true := by
    rw [lcaNode_comm a b]
    change branch (a.take (lcaDepth b a)) c = some true
    rw [branch_at_lca_third (by simpa only [lcaDepth_comm b a] using hdepth)]
    simpa only [lcaDepth_comm b a] using (bits_at_lca_of_lt hab hablen).2
  obtain ⟨htala, htaha⟩ := (prefix_iff_mem_cell ha).1 (prefix_of_branch_some htopa)
  obtain ⟨htalb, htahb⟩ := (prefix_iff_mem_cell hb).1 (prefix_of_branch_some htopb)
  obtain ⟨htalc, htahc⟩ := (prefix_iff_mem_cell hc).1 (prefix_of_branch_some htopc)
  obtain ⟨hllb, hlhb⟩ := (prefix_iff_mem_cell hb).1 (prefix_of_branch_some hlowb)
  obtain ⟨hllc, hlhc⟩ := (prefix_iff_mem_cell hc).1 (prefix_of_branch_some hlowc)
  have halow := lt_cellMin_of_lt_not_prefix ha hb hab (prefix_of_branch_some hlowb)
    (not_prefix_lower_right hdepth)
  cases s <;>
    simp [bstPreference, MTR.hull3, MTR.Tree.representative, MTR.preferences3,
      not_lt.mpr htala, not_lt.mpr htaha, not_lt.mpr htalb, not_lt.mpr htahb,
      not_lt.mpr htalc, not_lt.mpr htahc, not_lt.mpr hllb, not_lt.mpr hlhb,
      not_lt.mpr hllc, not_lt.mpr hlhc, halow, htopa, htopb, htopc, hlowb, hlowc]

/-- Actual BST representative bits for the (a,b) | c induced reference. -/
theorem hull3_preferences_left {H : Nat} {a b c : Key}
    (A B C D : MTR.Tree Key) (hab : a < b) (hbc : b < c)
    (ha : a.length = H) (hb : b.length = H) (hc : c.length = H)
    (hdepth : lcaDepth b c < lcaDepth a b) (s : MTR.Shape3) :
    bstPreference H (MTR.hull3 a b c A B C D s) (lcaNode b c) =
      some (MTR.preferences3 .leftSplit s).1 ∧
    bstPreference H (MTR.hull3 a b c A B C D s) (lcaNode a b) =
      some (MTR.preferences3 .leftSplit s).2 := by
  have hablen : a.length = b.length := ha.trans hb.symm
  have hbclen : b.length = c.length := hb.trans hc.symm
  obtain ⟨hlowa, hlowb⟩ := branches_lca_of_lt hab hablen
  obtain ⟨htopb, htopc⟩ := branches_lca_of_lt hbc hbclen
  have htopa : branch (lcaNode b c) a = some false := by
    change branch (c.take (lcaDepth b c)) a = some false
    rw [branch_at_lca_third (by simpa only [lcaDepth_comm b a] using hdepth)]
    exact (bits_at_lca_of_lt hbc hbclen).1
  obtain ⟨htala, htaha⟩ := (prefix_iff_mem_cell ha).1 (prefix_of_branch_some htopa)
  obtain ⟨htalb, htahb⟩ := (prefix_iff_mem_cell hb).1 (prefix_of_branch_some htopb)
  obtain ⟨htalc, htahc⟩ := (prefix_iff_mem_cell hc).1 (prefix_of_branch_some htopc)
  obtain ⟨hlla, hlha⟩ := (prefix_iff_mem_cell ha).1 (prefix_of_branch_some hlowa)
  obtain ⟨hllb, hlhb⟩ := (prefix_iff_mem_cell hb).1 (prefix_of_branch_some hlowb)
  have hclow := cellMax_lt_of_lt_not_prefix hb hc hbc (prefix_of_branch_some hlowb)
    (not_prefix_lower_left hdepth)
  have hlc : cellMin H (lcaNode a b) ≤ c := hllb.trans (le_of_lt hbc)
  cases s <;>
    simp [bstPreference, MTR.hull3, MTR.Tree.representative, MTR.preferences3,
      not_lt.mpr htala, not_lt.mpr htaha, not_lt.mpr htalb, not_lt.mpr htahb,
      not_lt.mpr htalc, not_lt.mpr htahc, not_lt.mpr hlla, not_lt.mpr hlha,
      not_lt.mpr hllb, not_lt.mpr hlhb, not_lt.mpr hlc, hclow,
      htopa, htopb, htopc, hlowa, hlowb]

end ChaCha.Primary

namespace ChaCha.MTR

open Tree

/-- The three skeleton keys form a rooted hull for any hanging subtrees. -/
theorem hull3_rootedHull {α : Type*} [LinearOrder α] (a b c : α)
    (A B C D : Tree α) (hab : a < b) (hbc : b < c) (s : Shape3) :
    RootedHull (hull3 a b c A B C D s) {a, b, c} := by
  intro x hx
  have hac := lt_trans hab hbc
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  all_goals constructor
  all_goals
    cases s <;> simp [hull3, searchPath, searchDepth, hab, hbc, hac,
      not_lt.mpr (le_of_lt hab), not_lt.mpr (le_of_lt hbc), not_lt.mpr (le_of_lt hac)]

end ChaCha.MTR
