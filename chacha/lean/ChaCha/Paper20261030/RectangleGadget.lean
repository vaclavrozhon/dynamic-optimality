import ChaCha.Paper20261030.RectangleExtensionSecond

/-!
# The robust rectangle extension lemma

`rectangle_extension` proves manuscript Lemma `rect-gadget`. A finite
guard is an actual input point to the upper left. An absent guard is
represented by any time larger than every input time; the unbounded
wrapper constructs such a time from the finite point set.

The result extends every supplied robust family by an actual rectangle
from the distinguished point, without deleting an old rectangle.
-/

namespace ChaCha.Paper20261030.Rectangles

theorem robustFamily_insert {P : Finset Point} {R : Finset Rectangle}
    (hR : RobustFamily P R) {r : Rectangle} (hr : InputFree P r)
    (hpair : ∀ s ∈ R, RobustPair r s) : RobustFamily P (insert r R) := by
  constructor
  · intro s hs
    rcases Finset.mem_insert.mp hs with rfl | hs
    · exact hr
    · exact hR.1 s hs
  · intro s hs t ht hne
    rcases Finset.mem_insert.mp hs with rfl | hs0 <;>
      rcases Finset.mem_insert.mp ht with rfl | ht0
    · exact (hne rfl).elim
    · exact hpair _ ht0
    · exact robustPair_symm (hpair _ hs0)
    · exact hR.2 s hs0 t ht0 hne

/-- Finite-coordinate form of manuscript Lemma `rect-gadget`. -/
theorem rectangle_extension {P : Finset Point} (hP : Instance P)
    {p : Point} (hp : p ∈ P) (gx gy : Int) (hgx : gx < p.1)
    (guard : (gx,gy) ∈ P ∨ ∀ z ∈ P, z.2 < gy)
    (emptyStrip : ∀ z ∈ P, gx < z.1 → z.1 ≤ p.1 → p.2 < z.2 → z.2 < gy → False)
    (east : ∃ z ∈ P, p.1 < z.1 ∧ p.2 < z.2 ∧ z.2 < gy)
    {R : Finset Rectangle} (hR : RobustFamily P R) :
    ∃ z ∈ P, p.1 < z.1 ∧ p.2 < z.2 ∧ z.2 < gy ∧
      RobustFamily P (insert (p,z) R) := by
  classical
  let candidates := P.filter (fun z => p.1 < z.1 ∧ p.2 < z.2 ∧ z.2 < gy)
  have hnonempty : candidates.Nonempty := by
    obtain ⟨z,hz,he⟩ := east
    exact ⟨z,Finset.mem_filter.mpr ⟨hz,he⟩⟩
  obtain ⟨q,hq,hfirst⟩ := Finset.exists_min_image candidates Prod.snd hnonempty
  obtain ⟨hqP,hqx,hqt,hqgy⟩ := Finset.mem_filter.mp hq
  have clear : ClearEarly P p q := by
    intro z hz hx ht hbefore
    by_cases hsame : z.1 = p.1
    · exact emptyStrip z hz (by omega) (by omega) ht (by omega)
    · have hc : z ∈ candidates := Finset.mem_filter.mpr
        ⟨hz,by omega,ht,by omega⟩
      have := hfirst z hc
      try dsimp only at this
      omega
  have hpq := inputFree_of_clearEarly hP hp hqP hqx hqt clear
  let blockers := R.filter (fun r => ¬ Shared (p,q) r ∧ Contains r (p.1,q.2))
  by_cases hblock : blockers.Nonempty
  · obtain ⟨b,hb,hmin⟩ := Finset.exists_min_image blockers (fun r => r.2.1) hblock
    obtain ⟨hbR,hbnshared,hbcorner⟩ := Finset.mem_filter.mp hb
    have hbfree := hR.1 b hbR
    obtain ⟨hbleft,hbbottom,hbmid,hbtop,hbfar⟩ :=
      first_blocker_geometry hP hpq hqx hbfree hbnshared hbcorner
    have hbdir := right_of_contains_corner hpq hbfree hqx hbnshared
      (z := (p.1,q.2)) ⟨Or.inl rfl,Or.inr rfl⟩ hbcorner
    have hbrange : p.1 ≤ b.2.1 := by
      have := hbcorner.2.1
      try dsimp only at this
      omega
    have hbguard : b.1.1 ≤ gx := by
      by_contra h
      exact emptyStrip b.1 hbfree.1.1 (by omega) hbleft hbbottom (by omega)
    have hbgtime : b.2.2 < gy := by
      rcases guard with hguard | hall
      · by_contra h
        have hc : Contains b (gx,gy) := by
          simp only [Contains]
          try dsimp only
          omega
        have he := hbfree.2 (gx,gy) hguard hc
        simp only [Prod.ext_iff] at he
        try dsimp only at he
        omega
      · exact hall b.2 hbfree.1.2.1
    have hbright : p.1 < b.2.1 := by
      by_contra h
      exact emptyStrip b.2 hbfree.1.2.1 (by omega) (by omega) (by omega) hbgtime
    have hminimal : ∀ r ∈ R, ¬ Shared (p,q) r →
        Contains r (p.1,q.2) → b.2.1 ≤ r.2.1 := by
      intro r hr hn hc
      exact hmin r (Finset.mem_filter.mpr ⟨hr,hn,hc⟩)
    obtain ⟨hnew,hpairs⟩ := second_candidate_compatible hP hp clear hR hbR
      (by omega) hbbottom hbmid hbtop hbright hbfar hminimal
    exact ⟨b.2,hbfree.1.2.1,hbright,by omega,hbgtime,
      robustFamily_insert hR hnew hpairs⟩
  · refine ⟨q,hqP,hqx,hqt,hqgy,robustFamily_insert hR hpq ?_⟩
    intro r hr
    apply first_candidate_compatible hP hpq hqx clear (hR.1 r hr)
    intro hn hc
    exact hblock ⟨r,Finset.mem_filter.mpr ⟨hr,hn,hc⟩⟩

/-- The manuscript's absent-guard case, with no artificial time assumption. -/
theorem rectangle_extension_unbounded {P : Finset Point} (hP : Instance P)
    {p : Point} (hp : p ∈ P) (gx : Int) (hgx : gx < p.1)
    (emptyStrip : ∀ z ∈ P, gx < z.1 → z.1 ≤ p.1 → p.2 < z.2 → False)
    (east : ∃ z ∈ P, p.1 < z.1 ∧ p.2 < z.2)
    {R : Finset Rectangle} (hR : RobustFamily P R) :
    ∃ z ∈ P, p.1 < z.1 ∧ p.2 < z.2 ∧ RobustFamily P (insert (p,z) R) := by
  classical
  let times := P.image Prod.snd
  have htimes : times.Nonempty := ⟨p.2,Finset.mem_image.mpr ⟨p,hp,rfl⟩⟩
  let gy := times.max' htimes + 1
  have hall : ∀ z ∈ P, z.2 < gy := by
    intro z hz
    have hle := Finset.le_max' times z.2 (Finset.mem_image.mpr ⟨z,hz,rfl⟩)
    dsimp [gy]
    omega
  have heast : ∃ z ∈ P, p.1 < z.1 ∧ p.2 < z.2 ∧ z.2 < gy := by
    obtain ⟨z,hz,hx,ht⟩ := east
    exact ⟨z,hz,hx,ht,hall z hz⟩
  obtain ⟨z,hz,hx,ht,_,hnew⟩ := rectangle_extension hP hp gx gy hgx
    (Or.inr hall) (fun z hz hx₁ hx₂ ht _ => emptyStrip z hz hx₁ hx₂ ht) heast hR
  exact ⟨z,hz,hx,ht,hnew⟩

end ChaCha.Paper20261030.Rectangles
