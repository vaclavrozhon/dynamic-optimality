import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Lean.Elab.Tactic.Omega

/-!
# Input-free and robustly independent rectangles

Coordinates are integers; the first coordinate is a key and the second is
time. A rectangle is represented by its chronological defining points.
`On` checks membership, strictly increasing time, and distinct keys.
`InputFree` includes `On` and excludes all other input points from the
closed rectangle. Thus boundary points are not silently discarded.

`RobustPair` and `IndependentPair` are the manuscript's closed-corner and
open-corner conditions, respectively. The bounds maximize cardinality over
actual finite families; they are not unconstrained numerical parameters.
-/

namespace ChaCha.Paper20261030.Rectangles

abbrev Point := Int × Int
abbrev Rectangle := Point × Point

def Instance (P : Finset Point) : Prop :=
  ∀ p ∈ P, ∀ q ∈ P, p.2 = q.2 → p = q

def On (P : Finset Point) (r : Rectangle) : Prop :=
  r.1 ∈ P ∧ r.2 ∈ P ∧ r.1.2 < r.2.2 ∧ r.1.1 ≠ r.2.1

def Contains (r : Rectangle) (p : Point) : Prop :=
  min r.1.1 r.2.1 ≤ p.1 ∧ p.1 ≤ max r.1.1 r.2.1 ∧
    r.1.2 ≤ p.2 ∧ p.2 ≤ r.2.2

def Interior (r : Rectangle) (p : Point) : Prop :=
  min r.1.1 r.2.1 < p.1 ∧ p.1 < max r.1.1 r.2.1 ∧
    r.1.2 < p.2 ∧ p.2 < r.2.2

def Corner (r : Rectangle) (p : Point) : Prop :=
  (p.1 = r.1.1 ∨ p.1 = r.2.1) ∧ (p.2 = r.1.2 ∨ p.2 = r.2.2)

def InputFree (P : Finset Point) (r : Rectangle) : Prop :=
  On P r ∧ ∀ p ∈ P, Contains r p → p = r.1 ∨ p = r.2

def Shared (r s : Rectangle) : Prop :=
  r.1 = s.1 ∨ r.1 = s.2 ∨ r.2 = s.1 ∨ r.2 = s.2

def NoCorner (r s : Rectangle) : Prop :=
  ∀ p, Corner s p → ¬ Contains r p

def NoInteriorCorner (r s : Rectangle) : Prop :=
  ∀ p, Corner s p → ¬ Interior r p

def RobustPair (r s : Rectangle) : Prop :=
  Shared r s ∨ (NoCorner r s ∧ NoCorner s r)

def IndependentPair (r s : Rectangle) : Prop :=
  NoInteriorCorner r s ∧ NoInteriorCorner s r

def RobustFamily (P : Finset Point) (R : Finset Rectangle) : Prop :=
  (∀ r ∈ R, InputFree P r) ∧
    ∀ r ∈ R, ∀ s ∈ R, r ≠ s → RobustPair r s

def IndependentFamily (P : Finset Point) (R : Finset Rectangle) : Prop :=
  (∀ r ∈ R, InputFree P r) ∧
    ∀ r ∈ R, ∀ s ∈ R, r ≠ s → IndependentPair r s

theorem shared_symm {r s : Rectangle} (h : Shared r s) : Shared s r := by
  unfold Shared at *
  rcases h with h | h | h | h
  · exact Or.inl h.symm
  · exact Or.inr (Or.inr (Or.inl h.symm))
  · exact Or.inr (Or.inl h.symm)
  · exact Or.inr (Or.inr (Or.inr h.symm))

theorem interior_contains {r : Rectangle} {p : Point} (h : Interior r p) :
    Contains r p := ⟨h.1.le, h.2.1.le, h.2.2.1.le, h.2.2.2.le⟩

theorem inputFree_no_interior {P : Finset Point} {r : Rectangle}
    (h : InputFree P r) {p : Point} (hp : p ∈ P) : ¬ Interior r p := by
  intro hi
  rcases h.2 p hp (interior_contains hi) with he | he
  · subst p
    exact (lt_irrefl _ hi.2.2.1)
  · subst p
    exact (lt_irrefl _ hi.2.2.2)

theorem shared_no_interior {P : Finset Point} {r s : Rectangle}
    (hr : InputFree P r) (hs : InputFree P s) (h : Shared r s) :
    NoInteriorCorner r s := by
  have hb := inputFree_no_interior hr hs.1.1
  have ht := inputFree_no_interior hr hs.1.2.1
  intro p hp
  rcases r with ⟨⟨a,t⟩,⟨b,u⟩⟩
  rcases s with ⟨⟨c,v⟩,⟨d,w⟩⟩
  rcases p with ⟨x,y⟩
  simp only [Shared, Prod.mk.injEq, Corner, Interior] at h hp hb ht ⊢
  omega

/-- Robust independence really implies the ordinary rectangle condition. -/
theorem robustPair_independent {P : Finset Point} {r s : Rectangle}
    (hr : InputFree P r) (hs : InputFree P s) (h : RobustPair r s) :
    IndependentPair r s := by
  rcases h with h | ⟨hrs, hsr⟩
  · exact ⟨shared_no_interior hr hs h, shared_no_interior hs hr (shared_symm h)⟩
  · exact ⟨fun p hp hi => hrs p hp (interior_contains hi),
      fun p hp hi => hsr p hp (interior_contains hi)⟩

theorem robustFamily_independent {P : Finset Point} {R : Finset Rectangle}
    (h : RobustFamily P R) : IndependentFamily P R := by
  exact ⟨h.1, fun r hr s hs hne =>
    robustPair_independent (h.1 r hr) (h.1 s hs) (h.2 r hr s hs hne)⟩

theorem inputFree_excludes_endpoints {P : Finset Point} {r s : Rectangle}
    (hr : InputFree P r) (hs : InputFree P s) (hne : ¬ Shared r s) :
    ¬ Contains r s.1 ∧ ¬ Contains r s.2 ∧
      ¬ Contains s r.1 ∧ ¬ Contains s r.2 := by
  have hne' : ¬ Shared s r := fun h => hne (shared_symm h)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    rcases hr.2 _ hs.1.1 h with h | h
    · exact hne (Or.inl h.symm)
    · exact hne (Or.inr (Or.inr (Or.inl h.symm)))
  · intro h
    rcases hr.2 _ hs.1.2.1 h with h | h
    · exact hne (Or.inr (Or.inl h.symm))
    · exact hne (Or.inr (Or.inr (Or.inr h.symm)))
  · intro h
    rcases hs.2 _ hr.1.1 h with h | h
    · exact hne (Or.inl h)
    · exact hne (Or.inr (Or.inl h))
  · intro h
    rcases hs.2 _ hr.1.2.1 h with h | h
    · exact hne (Or.inr (Or.inr (Or.inl h)))
    · exact hne (Or.inr (Or.inr (Or.inr h)))

theorem noCorner_iff (r s : Rectangle) :
    NoCorner r s ↔ ¬ Contains r s.1 ∧ ¬ Contains r (s.1.1,s.2.2) ∧
      ¬ Contains r (s.2.1,s.1.2) ∧ ¬ Contains r s.2 := by
  constructor
  · intro h
    exact ⟨h _ ⟨Or.inl rfl, Or.inl rfl⟩,
      h _ ⟨Or.inl rfl, Or.inr rfl⟩,
      h _ ⟨Or.inr rfl, Or.inl rfl⟩,
      h _ ⟨Or.inr rfl, Or.inr rfl⟩⟩
  · rintro ⟨h₁,h₂,h₃,h₄⟩ ⟨x,y⟩ ⟨hx,hy⟩
    dsimp only at hx hy
    rcases hx with hx | hx <;> rcases hy with hy | hy <;>
      subst x <;> subst y <;> assumption

/-- The one-sided criterion in manuscript Lemma `rir-simpler`. -/
theorem noCorner_symm {P : Finset Point} {r s : Rectangle}
    (hr : InputFree P r) (hs : InputFree P s) (hne : ¬ Shared r s)
    (h : NoCorner r s) : NoCorner s r := by
  obtain ⟨h₁,h₂,h₃,h₄⟩ := inputFree_excludes_endpoints hr hs hne
  have hrt := hr.1.2.2.1
  have hst := hs.1.2.2.1
  rw [noCorner_iff] at h ⊢
  rcases r with ⟨⟨a,t⟩,⟨b,u⟩⟩
  rcases s with ⟨⟨c,v⟩,⟨d,w⟩⟩
  simp only [Contains] at *
  omega

theorem robustPair_of_noCorner {P : Finset Point} {r s : Rectangle}
    (hr : InputFree P r) (hs : InputFree P s) (h : NoCorner r s) :
    RobustPair r s := by
  by_cases he : Shared r s
  · exact Or.inl he
  · exact Or.inr ⟨h, noCorner_symm hr hs he h⟩

/-- Input-free rectangles of opposite directions are robustly independent. -/
theorem robustPair_opposite {P : Finset Point} {r s : Rectangle}
    (hr : InputFree P r) (hs : InputFree P s)
    (hop : (r.1.1 < r.2.1 ∧ s.2.1 < s.1.1) ∨
      (r.2.1 < r.1.1 ∧ s.1.1 < s.2.1)) : RobustPair r s := by
  by_cases he : Shared r s
  · exact Or.inl he
  · apply robustPair_of_noCorner hr hs
    obtain ⟨h₁,h₂,h₃,h₄⟩ := inputFree_excludes_endpoints hr hs he
    have hrt := hr.1.2.2.1
    have hst := hs.1.2.2.1
    rw [noCorner_iff]
    rcases r with ⟨⟨a,t⟩,⟨b,u⟩⟩
    rcases s with ⟨⟨c,v⟩,⟨d,w⟩⟩
    simp only [Contains] at *
    omega

noncomputable def rectangleBound (P : Finset Point) : Nat := by
  classical
  exact ((P ×ˢ P).powerset.filter (IndependentFamily P)).sup Finset.card

noncomputable def robustBound (P : Finset Point) : Nat := by
  classical
  exact ((P ×ˢ P).powerset.filter (RobustFamily P)).sup Finset.card

theorem independent_card_le {P : Finset Point} {R : Finset Rectangle}
    (h : IndependentFamily P R) : R.card ≤ rectangleBound P := by
  classical
  apply Finset.le_sup (f := Finset.card)
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_powerset.mpr ?_, h⟩
  intro r hr
  exact Finset.mem_product.mpr ⟨(h.1 r hr).1.1, (h.1 r hr).1.2.1⟩

theorem robust_card_le {P : Finset Point} {R : Finset Rectangle}
    (h : RobustFamily P R) : R.card ≤ robustBound P := by
  classical
  apply Finset.le_sup (f := Finset.card)
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_powerset.mpr ?_, h⟩
  intro r hr
  exact Finset.mem_product.mpr ⟨(h.1 r hr).1.1, (h.1 r hr).1.2.1⟩

theorem robustBound_le_rectangleBound (P : Finset Point) :
    robustBound P ≤ rectangleBound P := by
  classical
  apply Finset.sup_le
  intro R hR
  exact independent_card_le (robustFamily_independent (Finset.mem_filter.mp hR).2)

end ChaCha.Paper20261030.Rectangles
