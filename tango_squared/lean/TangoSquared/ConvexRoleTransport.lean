import TangoSquared.Reference
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Card

/-!
# Branch roles under a convex split of a sparse depth reference

The ambient depth tree is fixed. A branch is active exactly when the leaf
mask meets both of its children. Splitting a mask at a numerical cut keeps
each surviving branch on exactly one side. Exactly one active branch is
lost when both parts are nonempty. A surviving branch keeps the greatest
retained label in its left child, the separator assignment used in the
actual-key arm construction.

This module is a structural kernel. It does not formalize the recursive
history, role epochs, the first-private-plane lower bound, or BST costs.
-/

namespace TangoSquared
namespace ConvexRoleTransport

def lowerMask (M : Finset Nat) (d : Nat) : Finset Nat :=
  M.filter (fun x => x ≤ d)

def upperMask (M : Finset Nat) (d : Nat) : Finset Nat :=
  M.filter (fun x => d < x)

def Active (M : Finset Nat) (s : DepthSplit) : Prop :=
  (∃ x ∈ M, s.lo ≤ x ∧ x ≤ s.cut) ∧
  (∃ y ∈ M, s.cut < y ∧ y ≤ s.hi)

instance (M : Finset Nat) (s : DepthSplit) : Decidable (Active M s) :=
  inferInstanceAs (Decidable (_ ∧ _))

def roles (t : DepthTree a b) (M : Finset Nat) : Finset DepthSplit :=
  t.nodes.filter (Active M)

def leftLabels (M : Finset Nat) (s : DepthSplit) : Finset Nat :=
  M.filter (fun x => s.lo ≤ x ∧ x ≤ s.cut)

def roleKey (M : Finset Nat) (s : DepthSplit) : Nat :=
  (leftLabels M s).sup id

theorem active_mono {M N : Finset Nat} {s : DepthSplit}
    (hMN : M ⊆ N) (h : Active M s) : Active N s := by
  obtain ⟨⟨x, hx, hxlo, hxcut⟩, ⟨y, hy, hycut, hyhi⟩⟩ := h
  exact ⟨⟨x, hMN hx, hxlo, hxcut⟩, ⟨y, hMN hy, hycut, hyhi⟩⟩

theorem active_prefix (M : Finset Nat) (d : Nat) (s : DepthSplit)
    (h : Active (lowerMask M d) s) : Active M s :=
  active_mono (Finset.filter_subset _ _) h

theorem active_suffix (M : Finset Nat) (d : Nat) (s : DepthSplit)
    (h : Active (upperMask M d) s) : Active M s :=
  active_mono (Finset.filter_subset _ _) h

theorem not_active_both (M : Finset Nat) (d : Nat) (s : DepthSplit) :
    ¬ (Active (lowerMask M d) s ∧ Active (upperMask M d) s) := by
  rintro ⟨⟨_, ⟨y, hy, hycut, _⟩⟩, ⟨⟨x, hx, _, hxcut⟩, _⟩⟩
  have hyd : y ≤ d := (Finset.mem_filter.mp hy).2
  have hdx : d < x := (Finset.mem_filter.mp hx).2
  omega

theorem roles_disjoint (t : DepthTree a b) (M : Finset Nat) (d : Nat) :
    Disjoint (roles t (lowerMask M d)) (roles t (upperMask M d)) := by
  rw [Finset.disjoint_left]
  intro s hs hp
  exact not_active_both M d s
    ⟨(Finset.mem_filter.mp hs).2, (Finset.mem_filter.mp hp).2⟩

theorem prefix_leftLabels (M : Finset Nat) (d : Nat) (s : DepthSplit)
    (h : Active (lowerMask M d) s) :
    leftLabels (lowerMask M d) s = leftLabels M s := by
  obtain ⟨_, ⟨y, hy, hycut, _⟩⟩ := h
  have hyd : y ≤ d := (Finset.mem_filter.mp hy).2
  ext x
  simp only [leftLabels, lowerMask, Finset.mem_filter]
  constructor
  · rintro ⟨⟨hx, _⟩, hbounds⟩
    exact ⟨hx, hbounds⟩
  · rintro ⟨hx, hxlo, hxcut⟩
    exact ⟨⟨hx, by omega⟩, hxlo, hxcut⟩

theorem prefix_roleKey (M : Finset Nat) (d : Nat) (s : DepthSplit)
    (h : Active (lowerMask M d) s) :
    roleKey (lowerMask M d) s = roleKey M s := by
  simp only [roleKey, prefix_leftLabels M d s h]

theorem suffix_roleKey (M : Finset Nat) (d : Nat) (s : DepthSplit)
    (h : Active (upperMask M d) s) :
    roleKey (upperMask M d) s = roleKey M s := by
  obtain ⟨⟨z, hz, hzlo, hzcut⟩, _⟩ := h
  have hdz : d < z := (Finset.mem_filter.mp hz).2
  have hzleft : z ∈ leftLabels (upperMask M d) s :=
    Finset.mem_filter.mpr ⟨hz, hzlo, hzcut⟩
  apply Nat.le_antisymm
  · apply Finset.sup_le
    intro x hx
    have hxleft := Finset.mem_filter.mp hx
    apply Finset.le_sup
    exact Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp hxleft.1).1, hxleft.2⟩
  · apply Finset.sup_le
    intro x hx
    obtain ⟨hxM, hxlo, hxcut⟩ := Finset.mem_filter.mp hx
    by_cases hdx : d < x
    · apply Finset.le_sup
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨hxM, hdx⟩, hxlo, hxcut⟩
    · have hzle : z ≤ roleKey (upperMask M d) s :=
        Finset.le_sup (f := id) hzleft
      change x ≤ roleKey (upperMask M d) s
      exact Nat.le_trans (by omega) hzle

/-- A branch lost on both sides separates the adjacent retained labels at
the cut. The extrema premises name those concrete two labels. -/
theorem lost_iff_separates (M : Finset Nat) (d e f : Nat) (s : DepthSplit)
    (he : e ∈ M) (hed : e ≤ d)
    (hemax : ∀ x ∈ M, x ≤ d → x ≤ e)
    (hf : f ∈ M) (hdf : d < f)
    (hfmin : ∀ x ∈ M, d < x → f ≤ x) :
    (Active M s ∧ ¬ Active (lowerMask M d) s ∧
      ¬ Active (upperMask M d) s) ↔ s.Separates e f := by
  constructor
  · rintro ⟨⟨⟨x, hx, hxlo, hxcut⟩, ⟨y, hy, hycut, hyhi⟩⟩, hnlow, hnup⟩
    have hxd : x ≤ d := by
      by_contra h
      apply hnup
      exact ⟨⟨x, Finset.mem_filter.mpr ⟨hx, by omega⟩, hxlo, hxcut⟩,
        ⟨y, Finset.mem_filter.mpr ⟨hy, by omega⟩, hycut, hyhi⟩⟩
    have hdy : d < y := by
      by_contra h
      apply hnlow
      exact ⟨⟨x, Finset.mem_filter.mpr ⟨hx, hxd⟩, hxlo, hxcut⟩,
        ⟨y, Finset.mem_filter.mpr ⟨hy, by omega⟩, hycut, hyhi⟩⟩
    have hxe := hemax x hx hxd
    have hfy := hfmin y hy hdy
    have hecut : e ≤ s.cut := by
      by_contra h
      apply hnlow
      exact ⟨⟨x, Finset.mem_filter.mpr ⟨hx, hxd⟩, hxlo, hxcut⟩,
        ⟨e, Finset.mem_filter.mpr ⟨he, hed⟩, by omega, by omega⟩⟩
    have hcutf : s.cut < f := by
      by_contra h
      apply hnup
      exact ⟨⟨f, Finset.mem_filter.mpr ⟨hf, hdf⟩, by omega, by omega⟩,
        ⟨y, Finset.mem_filter.mpr ⟨hy, hdy⟩, hycut, hyhi⟩⟩
    exact ⟨by omega, hecut, hcutf, by omega⟩
  · rintro ⟨helo, hecut, hcutf, hfhi⟩
    refine ⟨⟨⟨e, he, helo, hecut⟩, ⟨f, hf, hcutf, hfhi⟩⟩, ?_, ?_⟩
    · rintro ⟨_, ⟨y, hy, hycut, _⟩⟩
      obtain ⟨hyM, hyd⟩ := Finset.mem_filter.mp hy
      have := hemax y hyM hyd
      omega
    · rintro ⟨⟨x, hx, _, hxcut⟩, _⟩
      obtain ⟨hxM, hdx⟩ := Finset.mem_filter.mp hx
      have := hfmin x hxM hdx
      omega

theorem unique_lost_role (t : DepthTree a b) (M : Finset Nat) (d e f : Nat)
    (ha : a ≤ e) (hb : f ≤ b)
    (he : e ∈ M) (hed : e ≤ d)
    (hemax : ∀ x ∈ M, x ≤ d → x ≤ e)
    (hf : f ∈ M) (hdf : d < f)
    (hfmin : ∀ x ∈ M, d < x → f ≤ x) :
    ∃! s, s ∈ roles t M ∧ s ∉ roles t (lowerMask M d) ∧
      s ∉ roles t (upperMask M d) := by
  obtain ⟨s, ⟨hs, hsep⟩, huniq⟩ := t.unique_separating ha (by omega) hb
  have hlost := (lost_iff_separates M d e f s he hed hemax hf hdf hfmin).2 hsep
  refine ⟨s, ?_, ?_⟩
  · refine ⟨Finset.mem_filter.mpr ⟨hs, hlost.1⟩, ?_, ?_⟩
    · intro h
      exact hlost.2.1 (Finset.mem_filter.mp h).2
    · intro h
      exact hlost.2.2 (Finset.mem_filter.mp h).2
  · intro r hr
    obtain ⟨hrM, hrL, hrR⟩ := hr
    obtain ⟨hrnodes, hractive⟩ := Finset.mem_filter.mp hrM
    apply huniq r
    refine ⟨hrnodes, ?_⟩
    apply (lost_iff_separates M d e f r he hed hemax hf hdf hfmin).1
    refine ⟨hractive, ?_, ?_⟩
    · intro h
      exact hrL (Finset.mem_filter.mpr ⟨hrnodes, h⟩)
    · intro h
      exact hrR (Finset.mem_filter.mpr ⟨hrnodes, h⟩)

theorem roles_split (t : DepthTree a b) (M : Finset Nat) (d e f : Nat)
    (ha : a ≤ e) (hb : f ≤ b)
    (he : e ∈ M) (hed : e ≤ d)
    (hemax : ∀ x ∈ M, x ≤ d → x ≤ e)
    (hf : f ∈ M) (hdf : d < f)
    (hfmin : ∀ x ∈ M, d < x → f ≤ x) :
    ∃ s, s ∈ roles t M ∧ s ∉ roles t (lowerMask M d) ∧
      s ∉ roles t (upperMask M d) ∧
      roles t M = insert s (roles t (lowerMask M d) ∪ roles t (upperMask M d)) := by
  obtain ⟨s, hs, huniq⟩ := unique_lost_role t M d e f ha hb he hed hemax hf hdf hfmin
  refine ⟨s, hs.1, hs.2.1, hs.2.2, ?_⟩
  ext r
  constructor
  · intro hr
    by_cases hrl : r ∈ roles t (lowerMask M d)
    · exact Finset.mem_insert_of_mem (Finset.mem_union_left _ hrl)
    by_cases hrr : r ∈ roles t (upperMask M d)
    · exact Finset.mem_insert_of_mem (Finset.mem_union_right _ hrr)
    have hrs : r = s := huniq r ⟨hr, hrl, hrr⟩
    subst r
    exact Finset.mem_insert_self s _
  · intro hr
    rcases Finset.mem_insert.mp hr with rfl | hr
    · exact hs.1
    rcases Finset.mem_union.mp hr with hr | hr
    · obtain ⟨hrnodes, hractive⟩ := Finset.mem_filter.mp hr
      exact Finset.mem_filter.mpr ⟨hrnodes, active_prefix M d r hractive⟩
    · obtain ⟨hrnodes, hractive⟩ := Finset.mem_filter.mp hr
      exact Finset.mem_filter.mpr ⟨hrnodes, active_suffix M d r hractive⟩

/-- The unique deleted branch is carried by the last retained label below
the cut. This identifies the actual separator, not just its ambient role. -/
theorem lost_roleKey (M : Finset Nat) (d e f : Nat) (s : DepthSplit)
    (he : e ∈ M)
    (hemax : ∀ x ∈ M, x ≤ d → x ≤ e)
    (hfmin : ∀ x ∈ M, d < x → f ≤ x)
    (hsep : s.Separates e f) : roleKey M s = e := by
  obtain ⟨helo, hecut, hcutf, _⟩ := hsep
  apply Nat.le_antisymm
  · apply Finset.sup_le
    intro x hx
    obtain ⟨hxM, _, hxcut⟩ := Finset.mem_filter.mp hx
    have hxd : x ≤ d := by
      by_contra h
      have := hfmin x hxM (by omega)
      omega
    exact hemax x hxM hxd
  · exact Finset.le_sup (f := id) (Finset.mem_filter.mpr ⟨he, helo, hecut⟩)

theorem roles_card_split (t : DepthTree a b) (M : Finset Nat) (d e f : Nat)
    (ha : a ≤ e) (hb : f ≤ b)
    (he : e ∈ M) (hed : e ≤ d)
    (hemax : ∀ x ∈ M, x ≤ d → x ≤ e)
    (hf : f ∈ M) (hdf : d < f)
    (hfmin : ∀ x ∈ M, d < x → f ≤ x) :
    (roles t (lowerMask M d)).card + (roles t (upperMask M d)).card + 1 =
      (roles t M).card := by
  obtain ⟨s, _, hsL, hsR, hsplit⟩ :=
    roles_split t M d e f ha hb he hed hemax hf hdf hfmin
  have hs : s ∉ roles t (lowerMask M d) ∪ roles t (upperMask M d) := by
    simpa only [Finset.mem_union, not_or] using And.intro hsL hsR
  rw [hsplit, Finset.card_insert_of_notMem hs,
    Finset.card_union_of_disjoint (roles_disjoint t M d)]

end ConvexRoleTransport
end TangoSquared
