import ChaCha.Paper20261030.RectangleSplit

/-!
# Geometric ingredients of the robust rectangle extension lemma

`ClearEarly P p q` says that before the first candidate `q`, no input
strictly later than `p` lies at or to the right of `p`. All conditions
refer to the actual finite instance. They are used to construct, rather
than presume, the rectangle required by manuscript Lemma `rect-gadget`.
-/

namespace ChaCha.Paper20261030.Rectangles

def ClearEarly (P : Finset Point) (p q : Point) : Prop :=
  ∀ z ∈ P, p.1 ≤ z.1 → p.2 < z.2 → z.2 < q.2 → False

theorem robustFamily_pair {P : Finset Point} {R : Finset Rectangle}
    (hR : RobustFamily P R) {r s : Rectangle} (hr : r ∈ R) (hs : s ∈ R) :
    RobustPair r s := by
  by_cases he : r = s
  · subst s
    exact Or.inl (Or.inl rfl)
  · exact hR.2 r hr s hs he

theorem nonshared_times {P : Finset Point} (hP : Instance P) {r s : Rectangle}
    (hr : On P r) (hs : On P s) (hne : ¬ Shared r s) :
    r.1.2 ≠ s.1.2 ∧ r.1.2 ≠ s.2.2 ∧ r.2.2 ≠ s.1.2 ∧ r.2.2 ≠ s.2.2 := by
  refine ⟨?_,?_,?_,?_⟩
  · intro h; exact hne (Or.inl (hP _ hr.1 _ hs.1 h))
  · intro h; exact hne (Or.inr (Or.inl (hP _ hr.1 _ hs.2.1 h)))
  · intro h; exact hne (Or.inr (Or.inr (Or.inl (hP _ hr.2.1 _ hs.1 h))))
  · intro h; exact hne (Or.inr (Or.inr (Or.inr (hP _ hr.2.1 _ hs.2.1 h))))

theorem inputFree_of_clearEarly {P : Finset Point} (hP : Instance P)
    {p q : Point} (hp : p ∈ P) (hq : q ∈ P) (hx : p.1 < q.1) (ht : p.2 < q.2)
    (clear : ClearEarly P p q) : InputFree P (p,q) := by
  refine ⟨⟨hp,hq,ht,ne_of_lt hx⟩,?_⟩
  intro z hz hc
  by_cases hzp : z.2 = p.2
  · exact Or.inl (hP _ hz _ hp hzp)
  by_cases hzq : z.2 = q.2
  · exact Or.inr (hP _ hz _ hq hzq)
  have hxz : p.1 ≤ z.1 := by simpa [Contains, min_eq_left hx.le] using hc.1
  exact (clear z hz hxz (by have := hc.2.2.1; dsimp at this; omega)
    (by have := hc.2.2.2; dsimp at this; omega)).elim

/-- A nonshared rectangle interfering with a right rectangle is right too. -/
theorem right_of_contains_corner {P : Finset Point} {p q : Point} {r : Rectangle}
    (hpq : InputFree P (p,q)) (hr : InputFree P r) (hx : p.1 < q.1)
    (hne : ¬ Shared (p,q) r) {z : Point} (hz : Corner (p,q) z)
    (hc : Contains r z) : r.1.1 < r.2.1 := by
  by_contra h
  have hdir : r.2.1 < r.1.1 := by have := hr.1.2.2.2; omega
  rcases robustPair_opposite hpq hr (Or.inl ⟨hx,hdir⟩) with he | ⟨_,hback⟩
  · exact hne he
  · exact hback z hz hc

/-- The lower-right corner of the first candidate has no nonshared blocker. -/
theorem first_candidate_bottom_clear {P : Finset Point} (hP : Instance P)
    {p q : Point} (hpq : InputFree P (p,q)) (hx : p.1 < q.1)
    (clear : ClearEarly P p q) {r : Rectangle} (hr : InputFree P r)
    (hne : ¬ Shared (p,q) r) : ¬ Contains r (q.1,p.2) := by
  intro hc
  have hdir := right_of_contains_corner hpq hr hx hne
    (z := (q.1,p.2)) ⟨Or.inr rfl,Or.inl rfl⟩ hc
  obtain ⟨h₁,h₂,h₃,h₄⟩ := inputFree_excludes_endpoints hpq hr hne
  have htimes := nonshared_times hP hpq.1 hr.1 hne
  have hpqt := hpq.1.2.2.1
  have hafter : p.2 < r.2.2 := by
    have htime := hc.2.2.2
    dsimp only at htime htimes
    omega
  have hxupper : p.1 ≤ r.2.1 := by
    have hkey := hc.2.1
    dsimp only at hkey
    omega
  have hlate : q.2 ≤ r.2.2 := by
    by_contra h
    exact clear r.2 hr.1.2.1 hxupper hafter (by omega)
  simp only [Contains] at hc h₁ h₂ h₃ h₄
  dsimp only at *
  omega

/-- The first candidate is compatible unless its upper-left corner is blocked. -/
theorem first_candidate_compatible {P : Finset Point} (hP : Instance P)
    {p q : Point} (hpq : InputFree P (p,q)) (hx : p.1 < q.1)
    (clear : ClearEarly P p q) {r : Rectangle} (hr : InputFree P r)
    (hupper : ¬ Shared (p,q) r → ¬ Contains r (p.1,q.2)) : RobustPair (p,q) r := by
  by_cases he : Shared (p,q) r
  · exact Or.inl he
  obtain ⟨_,_,h₃,h₄⟩ := inputFree_excludes_endpoints hpq hr he
  have hnc : NoCorner r (p,q) := (noCorner_iff _ _).mpr
    ⟨h₃,hupper he,first_candidate_bottom_clear hP hpq hx clear hr he,h₄⟩
  exact robustPair_symm (robustPair_of_noCorner hr hpq hnc)

/-- Coordinates of an upper-left blocker of the first candidate. -/
theorem first_blocker_geometry {P : Finset Point} (hP : Instance P)
    {p q : Point} (hpq : InputFree P (p,q)) (hx : p.1 < q.1)
    {r : Rectangle} (hr : InputFree P r) (hne : ¬ Shared (p,q) r)
    (hc : Contains r (p.1,q.2)) :
    r.1.1 ≤ p.1 ∧ p.2 < r.1.2 ∧ r.1.2 < q.2 ∧ q.2 < r.2.2 ∧ r.2.1 < q.1 := by
  have hdir := right_of_contains_corner hpq hr hx hne
    (z := (p.1,q.2)) ⟨Or.inl rfl,Or.inr rfl⟩ hc
  obtain ⟨h₁,h₂,h₃,h₄⟩ := inputFree_excludes_endpoints hpq hr hne
  have htimes := nonshared_times hP hpq.1 hr.1 hne
  have hpqt := hpq.1.2.2.1
  simp only [Contains] at hc h₁ h₂ h₃ h₄
  dsimp only at *
  omega

/-- The second candidate is input-free, using the first candidate's clear
region and the already present blocking rectangle. -/
theorem second_candidate_inputFree {P : Finset Point} (hP : Instance P)
    {p q : Point} (hp : p ∈ P) (clear : ClearEarly P p q)
    {r : Rectangle} (hr : InputFree P r)
    (hleft : r.1.1 < p.1) (hbottom : p.2 < r.1.2)
    (hmid : r.1.2 < q.2) (htop : q.2 < r.2.2) (hright : p.1 < r.2.1) :
    InputFree P (p,r.2) := by
  refine ⟨⟨hp,hr.1.2.1,lt_trans hbottom (lt_trans hmid htop),ne_of_lt hright⟩,?_⟩
  intro z hz hc
  by_cases hpz : z.2 = p.2
  · exact Or.inl (hP _ hz _ hp hpz)
  have hxz : p.1 ≤ z.1 := by simpa [Contains,min_eq_left hright.le] using hc.1
  have htz : p.2 < z.2 := by have := hc.2.2.1; dsimp at this; omega
  have hqz : q.2 ≤ z.2 := by
    by_contra h
    exact clear z hz hxz htz (by omega)
  have hrz : Contains r z := by
    simp only [Contains] at hc ⊢
    try dsimp only at hc
    omega
  rcases hr.2 z hz hrz with h | h
  · subst z
    omega
  · exact Or.inr h

end ChaCha.Paper20261030.Rectangles
