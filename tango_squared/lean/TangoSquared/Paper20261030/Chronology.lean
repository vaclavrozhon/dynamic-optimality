import TangoSquared.Paper20261030.RectangleSymmetry

/-!
# Chronological events on actual input instances

`Next P p q` means consecutive accesses, including repeated keys.
`NextDifferent P p q` skips later repetitions of `p`'s key.
`PreviousDifferent P p q` skips earlier repetitions of `q`'s key.
The latter two relations deliberately differ. `SwitchPoint P q` charges
the actual later endpoint of an adjacent unequal-key pair.
-/

namespace TangoSquared.Paper20261030.Rectangles

def Next (P : Finset Point) (p q : Point) : Prop :=
  p ∈ P ∧ q ∈ P ∧ p.2 < q.2 ∧
    ∀ z ∈ P, p.2 < z.2 → z.2 < q.2 → False

def NextDifferent (P : Finset Point) (p q : Point) : Prop :=
  p ∈ P ∧ q ∈ P ∧ p.2 < q.2 ∧ p.1 ≠ q.1 ∧
    ∀ z ∈ P, p.2 < z.2 → z.2 < q.2 → z.1 = p.1

def PreviousDifferent (P : Finset Point) (p q : Point) : Prop :=
  p ∈ P ∧ q ∈ P ∧ p.2 < q.2 ∧ p.1 ≠ q.1 ∧
    ∀ z ∈ P, p.2 < z.2 → z.2 < q.2 → z.1 = q.1

def SwitchPoint (P : Finset Point) (q : Point) : Prop :=
  ∃ p, Next P p q ∧ p.1 ≠ q.1

def Turn (p q r : Point) : Prop :=
  p.2 < q.2 ∧ q.2 < r.2 ∧
    ((p.1 < q.1 ∧ r.1 < q.1) ∨ (q.1 < p.1 ∧ q.1 < r.1))

def TurnPoint (P : Finset Point) (r : Point) : Prop :=
  ∃ p q, Next P q r ∧ PreviousDifferent P p q ∧ Turn p q r

def DepthExit (P : Finset Point) (f : Int → Int) (p : Point) : Prop :=
  ∃ r q, PreviousDifferent P r p ∧ f r.1 = f p.1 ∧
    Next P p q ∧ f p.1 ≠ f q.1

def MixedTurn (P : Finset Point) (f : Int → Int) (p : Point) : Prop :=
  ∃ p' q, NextDifferent P p p' ∧ f p.1 = f p'.1 ∧ q ∈ P ∧
    f q.1 ≠ f p.1 ∧ Turn p p' q ∧
    ∀ h h', NextDifferent P h h' → f h.1 = f p.1 → f h'.1 = f p.1 →
      p.2 < h.2 → q.2 < h.2

theorem instance_subset {P Q : Finset Point} (hP : Instance P) (hQP : Q ⊆ P) :
    Instance Q := fun p hp q hq ht => hP p (hQP hp) q (hQP hq) ht

theorem instance_fiber {P : Finset Point} (hP : Instance P) (f : Int → Int) (i : Int) :
    Instance (fiber f i P) := instance_subset hP (Finset.filter_subset _ _)

theorem next_previous_unique {P : Finset Point} (hP : Instance P)
    {p r q : Point} (hp : Next P p q) (hr : Next P r q) : p = r := by
  apply hP p hp.1 r hr.1
  apply le_antisymm
  · by_contra h
    exact hr.2.2.2 p hp.1 (by omega) hp.2.2.1
  · by_contra h
    exact hp.2.2.2 r hr.1 (by omega) hr.2.2.1

theorem next_successor_unique {P : Finset Point} (hP : Instance P)
    {p q r : Point} (hq : Next P p q) (hr : Next P p r) : q = r := by
  apply hP q hq.2.1 r hr.2.1
  apply le_antisymm
  · by_contra h
    exact hq.2.2.2 r hr.2.1 hr.2.2.1 (by omega)
  · by_contra h
    exact hr.2.2.2 q hq.2.1 hq.2.2.1 (by omega)

theorem exists_previous {P : Finset Point} {q : Point} (hq : q ∈ P)
    (hbefore : ∃ p ∈ P, p.2 < q.2) : ∃ p, Next P p q := by
  classical
  let before := P.filter (fun p => p.2 < q.2)
  have hb : before.Nonempty := by
    obtain ⟨p,hp,ht⟩ := hbefore
    exact ⟨p,Finset.mem_filter.mpr ⟨hp,ht⟩⟩
  obtain ⟨p,hp,hmax⟩ := Finset.exists_max_image before Prod.snd hb
  obtain ⟨hpP,hpq⟩ := Finset.mem_filter.mp hp
  refine ⟨p,hpP,hq,hpq,?_⟩
  intro z hz hpz hzq
  have hle := hmax z (Finset.mem_filter.mpr ⟨hz,hzq⟩)
  exact (not_le_of_gt hpz) hle

theorem switchPoint_iff {P : Finset Point} (hP : Instance P)
    {p q : Point} (hp : Next P p q) : SwitchPoint P q ↔ p.1 ≠ q.1 := by
  constructor
  · rintro ⟨r,hr,hne⟩
    simpa only [next_previous_unique hP hr hp] using hne
  · intro h
    exact ⟨p,hp,h⟩

theorem next_project (f : Int → Int) {P : Finset Point} {p q : Point}
    (h : Next P p q) : Next (project f P) (mapPoint f p) (mapPoint f q) := by
  refine ⟨Finset.mem_image.mpr ⟨p,h.1,rfl⟩,
    Finset.mem_image.mpr ⟨q,h.2.1,rfl⟩,h.2.2.1,?_⟩
  intro z hz hpz hzq
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hz
  exact h.2.2.2 a ha hpz hzq

theorem next_of_project (f : Int → Int) {P : Finset Point} {p q : Point}
    (hp : p ∈ P) (hq : q ∈ P)
    (h : Next (project f P) (mapPoint f p) (mapPoint f q)) : Next P p q := by
  refine ⟨hp,hq,h.2.2.1,?_⟩
  intro z hz hpz hzq
  exact h.2.2.2 (mapPoint f z) (Finset.mem_image.mpr ⟨z,hz,rfl⟩) hpz hzq

theorem next_fiber (f : Int → Int) {P : Finset Point} {p q : Point}
    (h : Next P p q) (he : f p.1 = f q.1) : Next (fiber f (f q.1) P) p q := by
  refine ⟨Finset.mem_filter.mpr ⟨h.1,he⟩,
    Finset.mem_filter.mpr ⟨h.2.1,rfl⟩,h.2.2.1,?_⟩
  intro z hz hpz hzq
  exact h.2.2.2 z (Finset.mem_filter.mp hz).1 hpz hzq

theorem switchPoint_of_project (f : Int → Int) {P : Finset Point} {q : Point}
    (hq : q ∈ P) (h : SwitchPoint (project f P) (mapPoint f q)) : SwitchPoint P q := by
  obtain ⟨p,hp,hne⟩ := h
  obtain ⟨a,ha,hea⟩ := Finset.mem_image.mp hp.1
  subst p
  refine ⟨a,next_of_project f ha hq hp,?_⟩
  intro he
  exact hne (congrArg f he)

theorem switchPoint_of_fiber {P : Finset Point} (hP : Instance P)
    (f : Int → Int) {q : Point} (h : SwitchPoint (fiber f (f q.1) P) q) :
    SwitchPoint P q := by
  obtain ⟨a,ha,hne⟩ := h
  have hq := (Finset.mem_filter.mp ha.2.1).1
  obtain ⟨p,hp⟩ := exists_previous hq ⟨a,(Finset.mem_filter.mp ha.1).1,ha.2.2.1⟩
  refine ⟨p,hp,?_⟩
  intro he
  have hpf := next_fiber f hp (congrArg f he)
  have hap := next_previous_unique (instance_fiber hP f _) ha hpf
  exact hne (congrArg Prod.fst hap |>.trans he)

/-- Pointwise basis of the exact double-switch identity. -/
theorem switchPoint_split_iff {P : Finset Point} (hP : Instance P)
    (f : Int → Int) {q : Point} (hq : q ∈ P) :
    SwitchPoint P q ↔ SwitchPoint (project f P) (mapPoint f q) ∨
      SwitchPoint (fiber f (f q.1) P) q := by
  constructor
  · rintro ⟨p,hp,hne⟩
    by_cases he : f p.1 = f q.1
    · exact Or.inr ⟨p,next_fiber f hp he,hne⟩
    · exact Or.inl ⟨mapPoint f p,next_project f hp,he⟩
  · rintro (h | h)
    · exact switchPoint_of_project f hq h
    · exact switchPoint_of_fiber hP f h

end TangoSquared.Paper20261030.Rectangles
