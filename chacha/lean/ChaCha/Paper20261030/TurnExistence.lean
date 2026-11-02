import ChaCha.Paper20261030.TurnClassification

/-!
# Turns forced by opposite directions

The extrema argument works on finite timestamped instances with repeated
keys: a strict ascent followed by a strict descent forces an actual turn.
-/

namespace ChaCha.Paper20261030.Rectangles

theorem exists_nextDifferent {P : Finset Point} {p : Point} (hp : p ∈ P)
    (hex : ∃ q ∈ P, p.2 < q.2 ∧ p.1 ≠ q.1) :
    ∃ q, NextDifferent P p q := by
  classical
  let S := P.filter (fun q => p.2 < q.2 ∧ p.1 ≠ q.1)
  have hS : S.Nonempty := by
    obtain ⟨q,hq,ht,hk⟩ := hex
    exact ⟨q,Finset.mem_filter.mpr ⟨hq,ht,hk⟩⟩
  obtain ⟨q,hq,hmin⟩ := Finset.exists_min_image S Prod.snd hS
  obtain ⟨hqP,ht,hk⟩ := Finset.mem_filter.mp hq
  refine ⟨q,hp,hqP,ht,hk,?_⟩
  intro z hz hpz hzq
  by_contra hn
  have := hmin z (Finset.mem_filter.mpr ⟨hz,hpz,Ne.symm hn⟩)
  omega

theorem exists_previousDifferent {P : Finset Point} {q : Point} (hq : q ∈ P)
    (hex : ∃ p ∈ P, p.2 < q.2 ∧ p.1 ≠ q.1) :
    ∃ p, PreviousDifferent P p q := by
  classical
  let S := P.filter (fun p => p.2 < q.2 ∧ p.1 ≠ q.1)
  have hS : S.Nonempty := by
    obtain ⟨p,hp,ht,hk⟩ := hex
    exact ⟨p,Finset.mem_filter.mpr ⟨hp,ht,hk⟩⟩
  obtain ⟨p,hp,hmax⟩ := Finset.exists_max_image S Prod.snd hS
  obtain ⟨hpP,ht,hk⟩ := Finset.mem_filter.mp hp
  refine ⟨p,hpP,hq,ht,hk,?_⟩
  intro z hz hpz hzq
  by_contra hn
  have := hmax z (Finset.mem_filter.mpr ⟨hz,hzq,hn⟩)
  omega

theorem nextDifferent_le {P : Finset Point} {p q z : Point}
    (h : NextDifferent P p q) (hz : z ∈ P) (ht : p.2 < z.2)
    (hk : p.1 ≠ z.1) : q.2 ≤ z.2 := by
  by_contra hn
  exact hk (h.2.2.2.2 z hz ht (by omega)).symm

theorem previousDifferent_ge {P : Finset Point} {p q z : Point}
    (h : PreviousDifferent P p q) (hz : z ∈ P) (ht : z.2 < q.2)
    (hk : z.1 ≠ q.1) : z.2 ≤ p.2 := by
  by_contra hn
  exact hk (h.2.2.2.2 z hz (by omega) ht)

theorem turnPoint_of_distinct_neighbors {P : Finset Point} (hP : Instance P)
    {p q r : Point} (hpq : PreviousDifferent P p q)
    (hqr : NextDifferent P q r) (ht : Turn p q r) : TurnPoint P r := by
  obtain ⟨s,hsr⟩ := exists_previous hqr.2.1 ⟨q,hqr.1,hqr.2.2.1⟩
  have hqs : q.2 ≤ s.2 := previous_ge hsr hqr.1 hqr.2.2.1
  have hskey : s.1 = q.1 := by
    by_cases he : s.2 = q.2
    · exact congrArg Prod.fst (hP s hsr.1 q hqr.1 he)
    · exact hqr.2.2.2.2 s hsr.1 (by omega) hsr.2.2.1
  refine ⟨p,s,hsr,⟨hpq.1,hsr.1,by have := hpq.2.2.1; omega,
    by simpa only [hskey] using hpq.2.2.2.1,?_⟩,?_⟩
  · intro z hz hpz hzs
    rw [hskey]
    by_cases hzq : z.2 < q.2
    · exact hpq.2.2.2.2 z hz hpz hzq
    · by_cases he : z.2 = q.2
      · exact congrArg Prod.fst (hP z hz q hqr.1 he)
      · exact hqr.2.2.2.2 z hz (by omega) (by have := hsr.2.2.1; omega)
  · exact ⟨by have := hpq.2.2.1; omega,hsr.2.2.1,by simpa only [hskey] using ht.2.2⟩

/-- A strict ascent into `a` followed by a descent from `b` to `c`
forces a turn completed after `a` and no later than `c`. -/
theorem turn_between_ascent_descent {P : Finset Point} (hP : Instance P)
    {p a b c : Point} (hpa : PreviousDifferent P p a)
    (hb : b ∈ P) (hc : c ∈ P) (hab : a.2 ≤ b.2) (hbc : b.2 < c.2)
    (hup : p.1 < a.1) (hdown : c.1 < b.1) :
    ∃ r ∈ P, a.2 < r.2 ∧ r.2 ≤ c.2 ∧ TurnPoint P r := by
  classical
  let S := P.filter (fun z => p.2 < z.2 ∧ z.2 < c.2)
  have haS : a ∈ S := Finset.mem_filter.mpr ⟨hpa.2.1,hpa.2.2.1,by omega⟩
  have hbS : b ∈ S := Finset.mem_filter.mpr ⟨hb,by have := hpa.2.2.1; omega,hbc⟩
  obtain ⟨q,hq,hmax⟩ := Finset.exists_max_image S Prod.fst ⟨a,haS⟩
  obtain ⟨hqP,hpq,hqc⟩ := Finset.mem_filter.mp hq
  have haq := hmax a haS
  have hbq := hmax b hbS
  have hpkey : p.1 < q.1 := lt_of_lt_of_le hup haq
  have hckey : c.1 < q.1 := lt_of_lt_of_le hdown hbq
  obtain ⟨s,hsq⟩ := exists_previousDifferent hqP ⟨p,hpa.1,hpq,ne_of_lt hpkey⟩
  obtain ⟨r,hqr⟩ := exists_nextDifferent hqP ⟨c,hc,hqc,ne_of_gt hckey⟩
  have hps := previousDifferent_ge hsq hpa.1 hpq (ne_of_lt hpkey)
  have hrc := nextDifferent_le hqr hc hqc (ne_of_gt hckey)
  have hskey : s.1 < q.1 := by
    by_cases he : s.2 = p.2
    · have heq := hP s hsq.1 p hpa.1 he
      simpa only [heq] using hpkey
    · have := hmax s (Finset.mem_filter.mpr ⟨hsq.1,by omega,
        lt_trans hsq.2.2.1 hqc⟩)
      have := hsq.2.2.2.1
      omega
  have hrkey : r.1 < q.1 := by
    by_cases he : r.2 = c.2
    · have heq := hP r hqr.2.1 c hc he
      simpa only [heq] using hckey
    · have := hmax r (Finset.mem_filter.mpr ⟨hqr.2.1,
        lt_trans hpq hqr.2.2.1,by omega⟩)
      have := hqr.2.2.2.1
      omega
  have har : a.2 < r.2 := by
    by_contra hn
    have hqa : q.2 < a.2 := by have := hqr.2.2.1; omega
    have hqkey := hpa.2.2.2.2 q hqP hpq hqa
    have hrakey : r.1 = a.1 := by
      by_cases he : r.2 = a.2
      · exact congrArg Prod.fst (hP r hqr.2.1 a hpa.2.1 he)
      · exact hpa.2.2.2.2 r hqr.2.1 (lt_trans hpq hqr.2.2.1) (by omega)
    exact hqr.2.2.2.1 (hqkey.trans hrakey.symm)
  exact ⟨r,hqr.2.1,har,hrc,turnPoint_of_distinct_neighbors hP hsq hqr
    ⟨hsq.2.2.1,hqr.2.2.1,Or.inl ⟨hskey,hrkey⟩⟩⟩

theorem previousDifferent_mirror {P : Finset Point} {p q : Point}
    (h : PreviousDifferent P p q) :
    PreviousDifferent (P.image mirrorPoint) (mirrorPoint p) (mirrorPoint q) := by
  refine ⟨Finset.mem_image.mpr ⟨p,h.1,rfl⟩,
    Finset.mem_image.mpr ⟨q,h.2.1,rfl⟩,h.2.2.1,?_,?_⟩
  · dsimp [mirrorPoint]
    have := h.2.2.2.1
    omega
  · intro z hz hpz hzq
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hz
    exact congrArg (fun x : Int => -x) (h.2.2.2.2 a ha hpz hzq)

theorem next_mirror {P : Finset Point} {p q : Point} (h : Next P p q) :
    Next (P.image mirrorPoint) (mirrorPoint p) (mirrorPoint q) := by
  refine ⟨Finset.mem_image.mpr ⟨p,h.1,rfl⟩,
    Finset.mem_image.mpr ⟨q,h.2.1,rfl⟩,h.2.2.1,?_⟩
  intro z hz hpz hzq
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hz
  exact h.2.2.2 a ha hpz hzq

theorem turnPoint_mirror {P : Finset Point} {r : Point} (h : TurnPoint P r) :
    TurnPoint (P.image mirrorPoint) (mirrorPoint r) := by
  obtain ⟨p,q,hqr,hpq,ht⟩ := h
  refine ⟨mirrorPoint p,mirrorPoint q,next_mirror hqr,previousDifferent_mirror hpq,?_⟩
  simp only [Turn,mirrorPoint] at ht ⊢
  omega

theorem turn_between_descent_ascent {P : Finset Point} (hP : Instance P)
    {p a b c : Point} (hpa : PreviousDifferent P p a)
    (hb : b ∈ P) (hc : c ∈ P) (hab : a.2 ≤ b.2) (hbc : b.2 < c.2)
    (hdown : a.1 < p.1) (hup : b.1 < c.1) :
    ∃ r ∈ P, a.2 < r.2 ∧ r.2 ≤ c.2 ∧ TurnPoint P r := by
  obtain ⟨r,hr,har,hrc,ht⟩ := turn_between_ascent_descent (instance_mirror hP)
    (previousDifferent_mirror hpa) (Finset.mem_image.mpr ⟨b,hb,rfl⟩)
    (Finset.mem_image.mpr ⟨c,hc,rfl⟩) hab hbc
    (by dsimp [mirrorPoint]; omega) (by dsimp [mirrorPoint]; omega)
  obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hr
  have htz := turnPoint_mirror ht
  have hPP : (P.image mirrorPoint).image mirrorPoint = P :=
    horizontalReflection.point_image_image P
  rw [hPP,mirrorPoint_involutive z] at htz
  exact ⟨z,hz,har,hrc,htz⟩

end ChaCha.Paper20261030.Rectangles
