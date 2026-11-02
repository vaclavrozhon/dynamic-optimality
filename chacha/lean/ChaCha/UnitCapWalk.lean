import ChaCha.ArboralQuotient
import Mathlib.Data.Int.Interval

/-!
# Arboral satisfaction under a unit walk of the clipping boundary

An upward cap step is bridged on its new row. A downward cap step is
bridged on its old row. Both boundaries are real emitted points.
No physical deletion or free suffix reactivation is part of this kernel.
-/

namespace ChaCha.UnitCapWalk

open ArboralDilation ArboralQuotient

def clipRows (c : Int → Int) (P : Finset Point) : Finset Point :=
  P.image (fun p => (min p.1 (c p.2), p.2))

def UnitSteps (c : Int → Int) : Prop :=
  ∀ t, c (t - 1) - 1 ≤ c t ∧ c t ≤ c (t - 1) + 1

def Bridges (c : Int → Int) (Q : Set Point) : Prop :=
  (∀ t, c t = c (t - 1) + 1 →
    (c (t - 1), t) ∈ Q ∧ (c t, t) ∈ Q) ∧
  (∀ t, c t = c (t - 1) - 1 →
    (c t, t - 1) ∈ Q ∧ (c (t - 1), t - 1) ∈ Q)

theorem mem_clipRows {c : Int → Int} {P : Finset Point} {a t : Int} :
    (a, t) ∈ clipRows c P ↔
      ∃ x, (x, t) ∈ P ∧ min x (c t) = a := by
  constructor
  · intro h
    obtain ⟨⟨x, s⟩, hx, he⟩ := Finset.mem_image.mp h
    have hs : s = t := congrArg Prod.snd he
    subst s
    exact ⟨x, hx, congrArg Prod.fst he⟩
  · rintro ⟨x, hx, he⟩
    exact Finset.mem_image.mpr ⟨(x, t), hx, Prod.ext he rfl⟩

theorem crossing_up {c : Int → Int} (hc : UnitSteps c)
    {s t z : Int} (hst : s < t) (hs : c s < z) (ht : z ≤ c t) :
    ∃ j, s < j ∧ j ≤ t ∧ c (j - 1) = z - 1 ∧ c j = z := by
  let F := (Finset.Icc (s + 1) t).filter (fun j => z ≤ c j)
  have hF : F.Nonempty := ⟨t, by simp [F, show s + 1 ≤ t by omega, ht]⟩
  obtain ⟨j, hj, hjmin⟩ := Finset.exists_min_image F id hF
  have hj' := Finset.mem_filter.mp hj
  have hjtime := Finset.mem_Icc.mp hj'.1
  have hjcap := hj'.2
  have hprev : c (j - 1) < z := by
    by_cases he : j - 1 = s
    · simpa [he] using hs
    · by_contra hh
      have hp : j - 1 ∈ F := Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
      have := hjmin (j - 1) hp
      change j ≤ j - 1 at this
      omega
  have hstep := hc j
  exact ⟨j, by omega, hjtime.2, by omega, by omega⟩

theorem crossing_down {c : Int → Int} (hc : UnitSteps c)
    {s t z : Int} (hst : s < t) (hs : z ≤ c s) (ht : c t < z) :
    ∃ j, s < j ∧ j ≤ t ∧ c (j - 1) = z ∧ c j = z - 1 := by
  have hn : UnitSteps (fun j => -c j) := by
    intro j
    have := hc j
    change -c (j - 1) - 1 ≤ -c j ∧ -c j ≤ -c (j - 1) + 1
    constructor <;> omega
  obtain ⟨j, hj₁, hj₂, hj₃, hj₄⟩ :=
    crossing_up hn hst (z := 1 - z) (by omega) (by omega)
  exact ⟨j, hj₁, hj₂, by omega, by omega⟩

private def EmptyRectangle (Q : Set Point) (a t b u : Int) : Prop :=
  ∀ p ∈ Q, InRectangle a t b u p → p = (a, t) ∨ p = (b, u)

private theorem cap_ge_of_empty {Q : Set Point} {c : Int → Int}
    (hc : UnitSteps c) (hB : Bridges c Q) {a t b u : Int}
    (hab : a < b) (hub : b ≤ c u) (hE : EmptyRectangle Q a t b u)
    {v : Int} (hv₁ : min t u ≤ v) (hv₂ : v ≤ max t u) : b ≤ c v := by
  by_contra hv
  have hcv : c v < b := by omega
  by_cases huv : u < v
  · obtain ⟨j, hj₁, hj₂, hprev, hcurr⟩ := crossing_down hc huv hub hcv
    have hstep : c j = c (j - 1) - 1 := by omega
    have hp := (hB.2 j hstep).1
    rw [hcurr] at hp
    have hut : u < t := by omega
    have hr : InRectangle a t b u (b - 1, j - 1) := by
      simp only [InRectangle]
      constructor
      · omega
      constructor
      · omega
      constructor <;> omega
    rcases hE _ hp hr with he | he
    · have := congrArg Prod.snd he; omega
    · have := congrArg Prod.fst he; omega
  · have hvne : v ≠ u := by intro he; subst v; omega
    have hvu : v < u := by omega
    obtain ⟨j, hj₁, hj₂, hprev, hcurr⟩ := crossing_up hc hvu hcv hub
    have hstep : c j = c (j - 1) + 1 := by omega
    have hp := (hB.1 j hstep).1
    rw [hprev] at hp
    have htu : t < u := by omega
    have hr : InRectangle a t b u (b - 1, j) := by
      simp only [InRectangle]
      constructor
      · omega
      constructor
      · omega
      constructor <;> omega
    rcases hE _ hp hr with he | he
    · have := congrArg Prod.snd he; omega
    · have := congrArg Prod.fst he; omega

private theorem cap_le_of_empty {Q : Set Point} {c : Int → Int}
    (hc : UnitSteps c) (hB : Bridges c Q) {a t b u : Int}
    (hab : a < b) (hub : c u = b) (hE : EmptyRectangle Q a t b u)
    {v : Int} (hv₁ : min t u ≤ v) (hv₂ : v ≤ max t u) : c v ≤ b := by
  by_contra hv
  have hcv : b + 1 ≤ c v := by omega
  by_cases huv : u < v
  · obtain ⟨j, hj₁, hj₂, hprev, hcurr⟩ :=
      crossing_up hc huv (z := b + 1) (by omega) hcv
    have hstep : c j = c (j - 1) + 1 := by omega
    have hp := (hB.1 j hstep).1
    have hprev' : c (j - 1) = b := by omega
    rw [hprev'] at hp
    have hr : InRectangle a t b u (b, j) := by
      simp only [InRectangle]
      constructor
      · omega
      constructor
      · omega
      constructor <;> omega
    rcases hE _ hp hr with he | he
    · have := congrArg Prod.fst he; omega
    · have := congrArg Prod.snd he; omega
  · have hvne : v ≠ u := by intro he; subst v; omega
    have hvu : v < u := by omega
    obtain ⟨j, hj₁, hj₂, hprev, hcurr⟩ :=
      crossing_down hc hvu (z := b + 1) hcv (by omega)
    have hstep : c j = c (j - 1) - 1 := by omega
    have hp := (hB.2 j hstep).1
    have hcurr' : c j = b := by omega
    rw [hcurr'] at hp
    have hr : InRectangle a t b u (b, j - 1) := by
      simp only [InRectangle]
      constructor
      · omega
      constructor
      · omega
      constructor <;> omega
    rcases hE _ hp hr with he | he
    · have := congrArg Prod.fst he; omega
    · have := congrArg Prod.snd he; omega

theorem satisfied_clipRows (P : Finset Point) (c : Int → Int)
    (hP : Satisfied (P : Set Point)) (hc : UnitSteps c)
    (hB : Bridges c (clipRows c P : Set Point)) :
    Satisfied (clipRows c P : Set Point) := by
  intro a t b u ha hb hab htu
  classical
  by_contra hnone
  have hE : EmptyRectangle (clipRows c P : Set Point) a t b u := by
    intro p hp hr
    by_cases hpa : p = (a, t)
    · exact Or.inl hpa
    by_cases hpb : p = (b, u)
    · exact Or.inr hpb
    exact False.elim (hnone ⟨p, hp, hr, hpa, hpb⟩)
  obtain ⟨x, hx, hxa⟩ := mem_clipRows.mp ha
  obtain ⟨y, hy, hyb⟩ := mem_clipRows.mp hb
  have hub : b ≤ c u := by omega
  have hge : ∀ v, min t u ≤ v → v ≤ max t u → b ≤ c v :=
    fun _ hv₁ hv₂ => cap_ge_of_empty hc hB hab hub hE hv₁ hv₂
  have hct := hge t (min_le_left _ _) (le_max_left _ _)
  have hxx : x = a := by omega
  subst x
  by_cases hbu : (b, u) ∈ P
  · obtain ⟨p, hp, hr, hpa, hpb⟩ := hP a t b u hx hbu hab htu
    have hcp := hge p.2 hr.2.2.1 hr.2.2.2
    have hpc : p.1 ≤ c p.2 := le_trans hr.2.1 hcp
    have hp' : p ∈ clipRows c P := Finset.mem_image.mpr
      ⟨p, hp, Prod.ext (min_eq_left hpc) rfl⟩
    rcases hE p hp' hr with he | he
    · exact hpa he
    · exact hpb he
  · have hub' : c u = b := by
      by_contra h
      have hyy : y = b := by omega
      exact hbu (by simpa [hyy] using hy)
    have heq : ∀ v, min t u ≤ v → v ≤ max t u → c v = b := by
      intro v hv₁ hv₂
      have hlo := hge v hv₁ hv₂
      have hhi := cap_le_of_empty hc hB hab hub' hE hv₁ hv₂
      omega
    let F := mapColumns (fun z => min z b) P
    have hF : Satisfied (F : Set Point) :=
      satisfied_mapColumns P _ (fun _ _ h => min_le_min_right _ h) hP
    have haF : (a, t) ∈ (F : Set Point) := Finset.mem_image.mpr
      ⟨(a, t), hx, Prod.ext (min_eq_left (le_of_lt hab)) rfl⟩
    have hbF : (b, u) ∈ (F : Set Point) := Finset.mem_image.mpr
      ⟨(y, u), hy, Prod.ext (by simpa [hub'] using hyb) rfl⟩
    obtain ⟨p, hp, hr, hpa, hpb⟩ := hF a t b u haF hbF hab htu
    obtain ⟨z, hz, hzp⟩ := Finset.mem_image.mp hp
    have hzt := congrArg (fun w : Point => w.2) hzp
    change z.2 = p.2 at hzt
    have hcz : c z.2 = b := by
      rw [hzt]
      exact heq p.2 hr.2.2.1 hr.2.2.2
    have hp' : p ∈ clipRows c P := Finset.mem_image.mpr
      ⟨z, hz, by simpa [hcz] using hzp⟩
    rcases hE p hp' hr with he | he
    · exact hpa he
    · exact hpb he

/-- Pop rows still use the old maximum; its removal takes effect later. -/
def retiringCap (r : Int → Int) (t : Int) : Int := max (r (t - 1)) (r t)

theorem unitSteps_retiringCap {r : Int → Int} (hr : UnitSteps r) :
    UnitSteps (retiringCap r) := by
  intro t
  have hnow := hr t
  have hprev := hr (t - 1)
  simp only [retiringCap]
  constructor <;> omega

/-- A genuine request to the changing maximum followed by unit dilation
supplies these two actual source-row points. -/
def PreparedChanges (r : Int → Int) (P : Set Point) : Prop :=
  ∀ t, r t ≠ r (t - 1) → (r (t - 1), t) ∈ P ∧ (r t, t) ∈ P

theorem bridges_retiringCap (P : Finset Point) {r : Int → Int}
    (hr : UnitSteps r) (hprep : PreparedChanges r (P : Set Point)) :
    Bridges (retiringCap r) (clipRows (retiringCap r) P : Set Point) := by
  constructor
  · intro t hup
    have hnow := hr t
    have hprev := hr (t - 1)
    have hup' := hup
    simp only [retiringCap] at hup'
    have hstep : r t = r (t - 1) + 1 := by omega
    have hcur : retiringCap r t = r t := by simp [retiringCap]; omega
    have hold : retiringCap r (t - 1) = r (t - 1) := by
      simp [retiringCap]; omega
    have hne : r t ≠ r (t - 1) := by omega
    obtain ⟨ha, hb⟩ := hprep t hne
    constructor
    · apply mem_clipRows.mpr
      exact ⟨r (t - 1), ha, by rw [hcur, hold]; omega⟩
    · apply mem_clipRows.mpr
      exact ⟨r t, hb, by rw [hcur]; simp⟩
  · intro t hdown
    have hnow := hr t
    have hprev := hr (t - 1)
    have hdown' := hdown
    simp only [retiringCap] at hdown'
    have hstep : r (t - 1) = r ((t - 1) - 1) - 1 := by omega
    have hcur : retiringCap r t = r (t - 1) := by
      simp [retiringCap]; omega
    have hold : retiringCap r (t - 1) = r ((t - 1) - 1) := by
      simp [retiringCap]; omega
    have hne : r (t - 1) ≠ r ((t - 1) - 1) := by omega
    obtain ⟨ha, hb⟩ := hprep (t - 1) hne
    constructor
    · apply mem_clipRows.mpr
      exact ⟨r (t - 1), hb, by rw [hcur, hold]; omega⟩
    · apply mem_clipRows.mpr
      exact ⟨r ((t - 1) - 1), ha, by rw [hold]; simp⟩

theorem satisfied_retiringCap (P : Finset Point) (r : Int → Int)
    (hP : Satisfied (P : Set Point)) (hr : UnitSteps r)
    (hprep : PreparedChanges r (P : Set Point)) :
    Satisfied (clipRows (retiringCap r) P : Set Point) :=
  satisfied_clipRows P _ hP (unitSteps_retiringCap hr)
    (bridges_retiringCap P hr hprep)

theorem card_clipRows (c : Int → Int) (P : Finset Point) :
    (clipRows c P).card ≤ P.card := Finset.card_image_le

def boundedHalo (lo hi : Int) (P : Finset Point) : Finset Point :=
  (finiteDilation 1 P).filter (fun p => lo ≤ p.1 ∧ p.1 ≤ hi)

theorem satisfied_boundedHalo (P : Finset Point) (lo hi : Int)
    (hP : Satisfied (P : Set Point)) :
    Satisfied (boundedHalo lo hi P : Set Point) := by
  have he : (boundedHalo lo hi P : Set Point) =
      {p ∈ dilate 1 (P : Set Point) | lo ≤ p.1 ∧ p.1 ≤ hi} := by
    ext p
    simp [boundedHalo, mem_finiteDilation]
  rw [he]
  exact satisfied_clip (satisfied_dilate hP (by omega)) lo hi

theorem preparedChanges_boundedHalo (P : Finset Point) {r : Int → Int}
    {lo hi : Int} (hr : UnitSteps r) (hbound : ∀ t, lo ≤ r t ∧ r t ≤ hi)
    (hreq : ∀ t, r t ≠ r (t - 1) → (max (r (t - 1)) (r t), t) ∈ P) :
    PreparedChanges r (boundedHalo lo hi P : Set Point) := by
  intro t hne
  have hq := hreq t hne
  have hs := hr t
  have hb₁ := hbound (t - 1)
  have hb₂ := hbound t
  constructor
  · apply Finset.mem_filter.mpr
    constructor
    · exact (mem_finiteDilation 1 P _).mpr
        ⟨max (r (t - 1)) (r t), hq, by omega, by omega⟩
    · exact hb₁
  · apply Finset.mem_filter.mpr
    constructor
    · exact (mem_finiteDilation 1 P _).mpr
        ⟨max (r (t - 1)) (r t), hq, by omega, by omega⟩
    · exact hb₂

def preparedPrefix (lo hi : Int) (r : Int → Int) (P : Finset Point) : Finset Point :=
  clipRows (retiringCap r) (boundedHalo lo hi P)

theorem satisfied_preparedPrefix (P : Finset Point) (r : Int → Int) (lo hi : Int)
    (hP : Satisfied (P : Set Point)) (hr : UnitSteps r)
    (hbound : ∀ t, lo ≤ r t ∧ r t ≤ hi)
    (hreq : ∀ t, r t ≠ r (t - 1) → (max (r (t - 1)) (r t), t) ∈ P) :
    Satisfied (preparedPrefix lo hi r P : Set Point) :=
  satisfied_retiringCap _ r (satisfied_boundedHalo P lo hi hP) hr
    (preparedChanges_boundedHalo P hr hbound hreq)

theorem card_preparedPrefix (P : Finset Point) (r : Int → Int) (lo hi : Int) :
    (preparedPrefix lo hi r P).card ≤ P.card * 3 := by
  calc
    (preparedPrefix lo hi r P).card ≤ (boundedHalo lo hi P).card :=
      card_clipRows _ _
    _ ≤ (finiteDilation 1 P).card := Finset.card_filter_le _ _
    _ ≤ P.card * 3 := by simpa using finiteDilation_card_le 1 P

theorem nearby_active_port_survives (P : Finset Point) (r : Int → Int)
    {lo hi x z t : Int} (hx : (x, t) ∈ P) (hnear₁ : x - 1 ≤ z)
    (hnear₂ : z ≤ x + 1) (hzlo : lo ≤ z) (hzhi : z ≤ hi) (hzactive : z ≤ r t) :
    (z, t) ∈ preparedPrefix lo hi r P := by
  apply mem_clipRows.mpr
  refine ⟨z, ?_, ?_⟩
  · apply Finset.mem_filter.mpr
    exact ⟨(mem_finiteDilation 1 P _).mpr ⟨x, hx, hnear₁, hnear₂⟩, hzlo, hzhi⟩
  · apply min_eq_left
    exact le_trans hzactive (le_max_right _ _)

end ChaCha.UnitCapWalk
