import ChaCha.Paper20261030.RectangleExtension

/-!
# Compatibility of the second rectangle candidate

If the first candidate is blocked at its upper-left corner, choose a
blocking rectangle with smallest upper key. Its upper endpoint supplies
the second candidate. This module proves the two corner-protection
arguments for that candidate, retaining all shared-endpoint cases.
-/

namespace ChaCha.Paper20261030.Rectangles

theorem shared_of_robust_contains {r s : Rectangle} (h : RobustPair r s)
    {p : Point} (hp : Corner r p) (hc : Contains s p) : Shared r s := by
  rcases h with h | ⟨_,hn⟩
  · exact h
  · exact (hn p hp hc).elim

theorem second_bottom_clear {P : Finset Point} (hP : Instance P)
    {p q : Point} (clear : ClearEarly P p q) {b r : Rectangle}
    (hnew : InputFree P (p,b.2)) (hr : InputFree P r)
    (hpair : RobustPair b r) (hne : ¬ Shared (p,b.2) r)
    (hleft : b.1.1 < p.1) (hbottom : p.2 < b.1.2)
    (hmid : b.1.2 < q.2) (htop : q.2 < b.2.2) (hright : p.1 < b.2.1) :
    ¬ Contains r (b.2.1,p.2) := by
  intro hc
  have hdir := right_of_contains_corner hnew hr hright hne
    (z := (b.2.1,p.2)) ⟨Or.inr rfl,Or.inl rfl⟩ hc
  have htimes := nonshared_times hP hnew.1 hr.1 hne
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
  have hcorner : Contains r (b.2.1,b.1.2) := by
    simp only [Contains] at hc ⊢
    dsimp only at *
    omega
  have hshared := shared_of_robust_contains hpair
    (p := (b.2.1,b.1.2)) ⟨Or.inr rfl,Or.inl rfl⟩ hcorner
  simp only [Contains] at hc
  simp only [Shared,Prod.ext_iff] at hshared hne
  dsimp only at *
  omega

theorem second_top_clear {P : Finset Point} (hP : Instance P)
    {p q : Point} {b r : Rectangle}
    (hnew : InputFree P (p,b.2)) (hb : InputFree P b) (hr : InputFree P r)
    (hpair : RobustPair b r) (hne : ¬ Shared (p,b.2) r)
    (hleft : b.1.1 < p.1) (hbottom : p.2 < b.1.2)
    (hmid : b.1.2 < q.2) (htop : q.2 < b.2.2)
    (hright : p.1 < b.2.1) (hfar : b.2.1 < q.1)
    (hminimal : ¬ Shared (p,q) r → Contains r (p.1,q.2) → b.2.1 ≤ r.2.1) :
    ¬ Contains r (p.1,b.2.2) := by
  intro hc
  have hdir := right_of_contains_corner hnew hr hright hne
    (z := (p.1,b.2.2)) ⟨Or.inl rfl,Or.inr rfl⟩ hc
  obtain ⟨h₁,h₂,h₃,h₄⟩ := inputFree_excludes_endpoints hnew hr hne
  have htimes := nonshared_times hP hnew.1 hr.1 hne
  by_cases hkey : r.1.1 < b.1.1
  · have hcorner : Contains r (b.1.1,b.2.2) := by
      simp only [Contains] at hc ⊢
      dsimp only at *
      omega
    have hshared := shared_of_robust_contains hpair
      (p := (b.1.1,b.2.2)) ⟨Or.inl rfl,Or.inr rfl⟩ hcorner
    simp only [Contains] at hc
    simp only [Shared,Prod.ext_iff] at hshared hne
    dsimp only at *
    omega
  · have hbase : r.1.2 ≤ b.1.2 := by
      have hin := hb.2 r.1 hr.1.1
      simp only [Contains,Prod.ext_iff] at hin hc
      dsimp only at *
      omega
    have hfirst : Contains r (p.1,q.2) := by
      simp only [Contains] at hc ⊢
      dsimp only at *
      omega
    have hnotfirst : ¬ Shared (p,q) r := by
      simp only [Shared,Prod.ext_iff] at hne ⊢
      simp only [Contains] at hc
      dsimp only at *
      omega
    have hlarge := hminimal hnotfirst hfirst
    apply h₄
    simp only [Contains] at hc ⊢
    dsimp only at *
    omega

/-- The minimum-key blocker supplies a compatible second candidate. -/
theorem second_candidate_compatible {P : Finset Point} (hP : Instance P)
    {p q : Point} (hp : p ∈ P) (clear : ClearEarly P p q)
    {R : Finset Rectangle} (hR : RobustFamily P R) {b : Rectangle} (hb : b ∈ R)
    (hleft : b.1.1 < p.1) (hbottom : p.2 < b.1.2)
    (hmid : b.1.2 < q.2) (htop : q.2 < b.2.2)
    (hright : p.1 < b.2.1) (hfar : b.2.1 < q.1)
    (hminimal : ∀ r ∈ R, ¬ Shared (p,q) r → Contains r (p.1,q.2) → b.2.1 ≤ r.2.1) :
    InputFree P (p,b.2) ∧ ∀ r ∈ R, RobustPair (p,b.2) r := by
  have hbfree := hR.1 b hb
  have hnew := second_candidate_inputFree hP hp clear hbfree hleft hbottom hmid htop hright
  refine ⟨hnew,?_⟩
  intro r hr
  by_cases he : Shared (p,b.2) r
  · exact Or.inl he
  have hrfree := hR.1 r hr
  have hpair := robustFamily_pair hR hb hr
  have hbottomClear := second_bottom_clear hP clear hnew hrfree hpair he
    hleft hbottom hmid htop hright
  have htopClear := second_top_clear hP hnew hbfree hrfree hpair he
    hleft hbottom hmid htop hright hfar (hminimal r hr)
  obtain ⟨_,_,h₃,h₄⟩ := inputFree_excludes_endpoints hnew hrfree he
  have hn : NoCorner r (p,b.2) := (noCorner_iff _ _).mpr
    ⟨h₃,htopClear,hbottomClear,h₄⟩
  exact robustPair_symm (robustPair_of_noCorner hrfree hnew hn)

end ChaCha.Paper20261030.Rectangles
