import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.Image
import Lean.Elab.Tactic.Omega

/-!
# The complete primary reference

Leaves are equal-length Boolean words, and internal nodes are their proper
prefixes.  All definitions below use actual prefixes rather than an abstract
uniqueness or laminarity assumption.
-/

namespace TangoSquared
namespace Primary

abbrev Key := List Bool

/-- The depth of the lowest common ancestor, including the leaf depth for
identical keys. -/
def lcaDepth : Key → Key → Nat
  | a :: xs, b :: ys => if a = b then 1 + lcaDepth xs ys else 0
  | _, _ => 0

theorem lcaDepth_le_left (x y : Key) : lcaDepth x y ≤ x.length := by
  induction x generalizing y with
  | nil => simp [lcaDepth]
  | cons a xs ih =>
    cases y with
    | nil => simp [lcaDepth]
    | cons b ys => simp only [lcaDepth, List.length_cons]; split_ifs <;> have := ih ys <;> omega

theorem lcaDepth_comm (x y : Key) : lcaDepth x y = lcaDepth y x := by
  induction x generalizing y with
  | nil => cases y <;> rfl
  | cons a xs ih => cases y with
    | nil => rfl
    | cons b ys => simp [lcaDepth, eq_comm, ih]

theorem lcaDepth_le_right (x y : Key) : lcaDepth x y ≤ y.length := by
  rw [lcaDepth_comm]
  exact lcaDepth_le_left y x

/-- Two depth-`d` cells agree exactly when their LCA is at least that deep. -/
theorem take_eq_iff {x y : Key} {d : Nat}
    (hx : d ≤ x.length) (hy : d ≤ y.length) :
    x.take d = y.take d ↔ d ≤ lcaDepth x y := by
  induction x generalizing y d with
  | nil =>
    have : d = 0 := by simpa using hx
    subst d
    simp [lcaDepth]
  | cons a xs ih =>
    cases d with
    | zero => simp
    | succ d =>
      cases y with
      | nil => simp at hy
      | cons b ys =>
        simp only [List.length_cons, Nat.succ_le_succ_iff] at hx hy
        simp only [List.take_succ_cons, List.cons.injEq, lcaDepth]
        by_cases hab : a = b
        · simp only [hab, if_pos, true_and]
          rw [ih hx hy]
          omega
        · simp [hab]

/-- All words of one fixed depth. -/
def level : Nat → Finset Key
  | 0 => {[]}
  | d + 1 => (level d).image (false :: ·) ∪ (level d).image (true :: ·)

theorem mem_level (x : Key) (d : Nat) : x ∈ level d ↔ x.length = d := by
  induction d generalizing x with
  | zero => simp [level]
  | succ d ih =>
    cases x with
    | nil => simp [level]
    | cons b xs => cases b <;> simp [level, ih]

/-- The internal nodes of a complete reference tree of height `H`. -/
def owners : Nat → Finset Key
  | 0 => ∅
  | H + 1 => insert [] ((owners H).image (false :: ·) ∪ (owners H).image (true :: ·))

theorem mem_owners (x : Key) (H : Nat) : x ∈ owners H ↔ x.length < H := by
  induction H generalizing x with
  | zero => simp [owners]
  | succ H ih =>
    cases x with
    | nil => simp [owners]
    | cons b xs => cases b <;> simp [owners, ih]

/-- Restriction of the access word to one reference subtree. -/
def ownerWord (u : Key) (xs : List Key) : List Key :=
  xs.filter (fun x => decide (u.IsPrefix x))

/-- The child visited at `u`, or no symbol for an access outside its subtree. -/
def branch (u x : Key) : Option Bool :=
  if u.IsPrefix x then x[u.length]? else none

/-- Both keys have the same prefix at their LCA depth. -/
theorem take_lca_eq (p x : Key) :
    p.take (lcaDepth p x) = x.take (lcaDepth p x) :=
  (take_eq_iff (lcaDepth_le_left p x) (lcaDepth_le_right p x)).2 (Nat.le_refl _)

/-- If `p,z` agree deeper than `p,x`, the latter LCA also separates `z,x`. -/
theorem lcaDepth_eq_of_lt {p x z : Key} (h : lcaDepth p x < lcaDepth p z) :
    lcaDepth z x = lcaDepth p x := by
  induction p generalizing x z with
  | nil => simp [lcaDepth] at h
  | cons a ps ih =>
    cases x with
    | nil => simp [lcaDepth]
    | cons b xs =>
      cases z with
      | nil => simp [lcaDepth] at h
      | cons c zs =>
        by_cases hac : a = c
        · subst c
          by_cases hab : a = b
          · subst b
            simp only [lcaDepth, ↓reduceIte] at h ⊢
            have htail : lcaDepth ps xs < lcaDepth ps zs := by omega
            rw [ih htail]
          · simp [lcaDepth, hab]
        · simp [lcaDepth, hac] at h

/-- Every bit strictly above the LCA agrees. -/
theorem getElem?_eq_of_lt_lca {p z : Key} {d : Nat} (h : d < lcaDepth p z) :
    p[d]? = z[d]? := by
  have ht := congrArg (fun word : Key => word[d]?) (take_lca_eq p z)
  simpa only [List.getElem?_take_of_lt h] using ht

/-- At a proper LCA, the two next child bits differ. -/
theorem getElem?_ne_at_lca (p x : Key)
    (hp : lcaDepth p x < p.length) (hx : lcaDepth p x < x.length) :
    p[lcaDepth p x]? ≠ x[lcaDepth p x]? := by
  intro heq
  have ht : p.take (lcaDepth p x + 1) = x.take (lcaDepth p x + 1) := by
    rw [List.take_add_one, List.take_add_one, take_lca_eq, heq]
  have h := (take_eq_iff (by omega : lcaDepth p x + 1 ≤ p.length)
    (by omega : lcaDepth p x + 1 ≤ x.length)).1 ht
  omega

/-- A shared owner is a prefix of both keys' common ancestor. -/
theorem prefix_take_lca {u p x : Key} (hp : u.IsPrefix p) (hx : u.IsPrefix x) :
    u.IsPrefix (x.take (lcaDepth p x)) := by
  have heq : p.take u.length = x.take u.length := by
    rw [← List.prefix_iff_eq_take.mp hp, ← List.prefix_iff_eq_take.mp hx]
  have hdepth : u.length ≤ lcaDepth p x :=
    (take_eq_iff hp.length_le hx.length_le).1 heq
  apply List.prefix_iff_eq_take.mpr
  rw [List.take_take, Nat.min_eq_left hdepth]
  exact List.prefix_iff_eq_take.mp hx

/-- A common-prefix node is inside any ancestor owner's subtree. -/
theorem prefix_of_take_lca_prefix {u p x y : Key} (hp : u.IsPrefix p) (hx : u.IsPrefix x)
    (hwy : (x.take (lcaDepth p x)).IsPrefix y) : u.IsPrefix y :=
  (prefix_take_lca hp hx).trans hwy

/-- The LCA prefix is a prefix of the first key. -/
theorem take_lca_prefix_left (p x : Key) :
    (x.take (lcaDepth p x)).IsPrefix p := by
  rw [← take_lca_eq p x]
  exact List.take_prefix _ _

/-- The LCA prefix is a prefix of the second key. -/
theorem take_lca_prefix_right (p x : Key) :
    (x.take (lcaDepth p x)).IsPrefix x := List.take_prefix _ _

/-- The branch of the first key at its common ancestor is its LCA-depth bit. -/
theorem branch_at_lca_left (p x : Key) :
    branch (x.take (lcaDepth p x)) p = p[lcaDepth p x]? := by
  simp [branch, take_lca_prefix_left, List.length_take,
    Nat.min_eq_left (lcaDepth_le_right p x)]

/-- The branch of the second key at its common ancestor is its LCA-depth bit. -/
theorem branch_at_lca_right (p x : Key) :
    branch (x.take (lcaDepth p x)) x = x[lcaDepth p x]? := by
  simp [branch, take_lca_prefix_right, List.length_take,
    Nat.min_eq_left (lcaDepth_le_right p x)]

/-- The deeper-agreeing third key has the same branch as the first key. -/
theorem branch_at_lca_third {p x z : Key} (h : lcaDepth p x < lcaDepth p z) :
    branch (x.take (lcaDepth p x)) z = p[lcaDepth p x]? := by
  have hlen : lcaDepth p x ≤ z.length := (Nat.le_of_lt h).trans (lcaDepth_le_right p z)
  have ht : p.take (lcaDepth p x) = z.take (lcaDepth p x) :=
    (take_eq_iff (lcaDepth_le_left p x) hlen).2 (Nat.le_of_lt h)
  have hz : (x.take (lcaDepth p x)).IsPrefix z := by
    rw [← take_lca_eq p x, ht]
    exact List.take_prefix _ _
  rw [branch, if_pos hz, List.length_take, Nat.min_eq_left (lcaDepth_le_right p x)]
  exact (getElem?_eq_of_lt_lca h).symm

/-- The charging node sees equal neighbors on one side and the deleted key on the other. -/
theorem branches_at_lca {p x z : Key}
    (h : lcaDepth p x < lcaDepth p z) (hx : lcaDepth p x < x.length) :
    ∃ a b : Bool, a ≠ b ∧
      branch (x.take (lcaDepth p x)) p = some a ∧
      branch (x.take (lcaDepth p x)) z = some a ∧
      branch (x.take (lcaDepth p x)) x = some b := by
  have hp : lcaDepth p x < p.length := h.trans_le (lcaDepth_le_left p z)
  refine ⟨p[lcaDepth p x], x[lcaDepth p x], ?_, ?_, ?_, ?_⟩
  · intro heq
    apply getElem?_ne_at_lca p x hp hx
    simpa only [List.getElem?_eq_getElem hp, List.getElem?_eq_getElem hx] using
      congrArg some heq
  · rw [branch_at_lca_left, List.getElem?_eq_getElem hp]
  · rw [branch_at_lca_third h, List.getElem?_eq_getElem hp]
  · rw [branch_at_lca_right, List.getElem?_eq_getElem hx]

end Primary
end TangoSquared
