import TangoSquared.Paper20261030.Rectangles

/-!
# Convex splitting of robust rectangle certificates

A nondecreasing integer map `f` represents the ordered interval partition:
its fibers are the segments. `mapPoint` contracts keys and retains time.
The one-input-point-per-time condition makes this map injective on the
actual input, even though it need not be injective on the key universe.
-/

namespace TangoSquared.Paper20261030.Rectangles

def mapPoint (f : Int → Int) (p : Point) : Point := (f p.1, p.2)
def mapRectangle (f : Int → Int) (r : Rectangle) : Rectangle :=
  (mapPoint f r.1, mapPoint f r.2)
def project (f : Int → Int) (P : Finset Point) : Finset Point :=
  P.image (mapPoint f)
def fiber (f : Int → Int) (i : Int) (P : Finset Point) : Finset Point :=
  P.filter (fun p => f p.1 = i)

theorem mapPoint_injective_on {P : Finset Point} (hP : Instance P)
    (f : Int → Int) {p q : Point} (hp : p ∈ P) (hq : q ∈ P)
    (he : mapPoint f p = mapPoint f q) : p = q :=
  hP p hp q hq (show (mapPoint f p).2 = (mapPoint f q).2 from congrArg Prod.snd he)

theorem mapRectangle_injective_on {P : Finset Point} (hP : Instance P)
    (f : Int → Int) {r s : Rectangle} (hr : On P r) (hs : On P s)
    (he : mapRectangle f r = mapRectangle f s) : r = s := by
  apply Prod.ext
  · exact mapPoint_injective_on hP f hr.1 hs.1 (congrArg Prod.fst he)
  · exact mapPoint_injective_on hP f hr.2.1 hs.2.1 (congrArg Prod.snd he)

theorem instance_project {P : Finset Point} (hP : Instance P) (f : Int → Int) :
    Instance (project f P) := by
  intro p hp q hq he
  change p ∈ P.image (mapPoint f) at hp
  change q ∈ P.image (mapPoint f) at hq
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hq
  exact congrArg (mapPoint f) (hP a ha b hb he)

theorem contains_map (f : Int → Int) (hf : Monotone f)
    {r : Rectangle} {p : Point} (h : Contains r p) :
    Contains (mapRectangle f r) (mapPoint f p) := by
  obtain ⟨h₁,h₂,h₃,h₄⟩ := h
  refine ⟨?_, ?_, h₃, h₄⟩
  · change min (f r.1.1) (f r.2.1) ≤ f p.1
    rcases le_total r.1.1 r.2.1 with he | he
    · exact (min_le_left _ _).trans (hf (by simpa [min_eq_left he] using h₁))
    · exact (min_le_right _ _).trans (hf (by simpa [min_eq_right he] using h₁))
  · change f p.1 ≤ max (f r.1.1) (f r.2.1)
    rcases le_total r.1.1 r.2.1 with he | he
    · exact (hf (by simpa [max_eq_right he] using h₂)).trans (le_max_right _ _)
    · exact (hf (by simpa [max_eq_left he] using h₂)).trans (le_max_left _ _)

theorem corner_map (f : Int → Int) {r : Rectangle} {p : Point} (h : Corner r p) :
    Corner (mapRectangle f r) (mapPoint f p) := by
  exact ⟨h.1.imp (congrArg f) (congrArg f), h.2⟩

theorem inputFree_of_project {P : Finset Point} (hP : Instance P)
    (f : Int → Int) (hf : Monotone f) {r : Rectangle}
    (hr : On P r) (h : InputFree (project f P) (mapRectangle f r)) :
    InputFree P r := by
  refine ⟨hr, ?_⟩
  intro p hp hc
  have hm := h.2 (mapPoint f p) (Finset.mem_image.mpr ⟨p,hp,rfl⟩)
    (contains_map f hf hc)
  exact hm.imp (mapPoint_injective_on hP f hp hr.1)
    (mapPoint_injective_on hP f hp hr.2.1)

theorem inputFree_of_fiber (f : Int → Int) (hf : Monotone f)
    {P : Finset Point} {i : Int} {r : Rectangle} (h : InputFree (fiber f i P) r) :
    InputFree P r := by
  obtain ⟨hp,hpi⟩ := Finset.mem_filter.mp h.1.1
  obtain ⟨hq,hqi⟩ := Finset.mem_filter.mp h.1.2.1
  refine ⟨⟨hp,hq,h.1.2.2⟩, ?_⟩
  intro p hp hc
  have hm := contains_map f hf hc
  have hkey : f p.1 = i := by
    have hlo : i ≤ f p.1 := by simpa [mapRectangle, mapPoint, hpi, hqi] using hm.1
    have hhi : f p.1 ≤ i := by simpa [mapRectangle, mapPoint, hpi, hqi] using hm.2.1
    exact le_antisymm hhi hlo
  exact h.2 p (Finset.mem_filter.mpr ⟨hp,hkey⟩) hc

theorem shared_of_map {P : Finset Point} (hP : Instance P)
    (f : Int → Int) {r s : Rectangle} (hr : On P r) (hs : On P s)
    (h : Shared (mapRectangle f r) (mapRectangle f s)) : Shared r s := by
  rcases h with h | h | h | h
  · exact Or.inl (mapPoint_injective_on hP f hr.1 hs.1 h)
  · exact Or.inr (Or.inl (mapPoint_injective_on hP f hr.1 hs.2.1 h))
  · exact Or.inr (Or.inr (Or.inl (mapPoint_injective_on hP f hr.2.1 hs.1 h)))
  · exact Or.inr (Or.inr (Or.inr (mapPoint_injective_on hP f hr.2.1 hs.2.1 h)))

theorem robustPair_of_project {P : Finset Point} (hP : Instance P)
    (f : Int → Int) (hf : Monotone f) {r s : Rectangle}
    (hr : On P r) (hs : On P s)
    (h : RobustPair (mapRectangle f r) (mapRectangle f s)) : RobustPair r s := by
  rcases h with h | ⟨h₁,h₂⟩
  · exact Or.inl (shared_of_map hP f hr hs h)
  · exact Or.inr ⟨fun p hp hc => h₁ _ (corner_map f hp) (contains_map f hf hc),
      fun p hp hc => h₂ _ (corner_map f hp) (contains_map f hf hc)⟩

/-- An outer certificate and an inner certificate are compatible on the
original input. Shared projected points are resolved by their actual times. -/
theorem robustPair_outer_inner {P : Finset Point} (hP : Instance P)
    (f : Int → Int) (hf : Monotone f) {i : Int} {r s : Rectangle}
    (hr : On P r) (houter : InputFree (project f P) (mapRectangle f r))
    (hinner : InputFree (fiber f i P) s) : RobustPair r s := by
  have hrfree := inputFree_of_project hP f hf hr houter
  have hsfree := inputFree_of_fiber f hf hinner
  by_cases he : Shared r s
  · exact Or.inl he
  have hs₁ := (Finset.mem_filter.mp hinner.1.1).2
  have hs₂ := (Finset.mem_filter.mp hinner.1.2.1).2
  obtain ⟨h₁,h₂,h₃,h₄⟩ := inputFree_excludes_endpoints hrfree hsfree he
  have hm₁ : ¬ Contains (mapRectangle f r) (mapPoint f s.1) := by
    intro hc
    rcases houter.2 _ (Finset.mem_image.mpr ⟨s.1,hsfree.1.1,rfl⟩) hc with h | h
    · exact he (Or.inl (mapPoint_injective_on hP f hsfree.1.1 hr.1 h).symm)
    · exact he (Or.inr (Or.inr
        (Or.inl (mapPoint_injective_on hP f hsfree.1.1 hr.2.1 h).symm)))
  have hm₂ : ¬ Contains (mapRectangle f r) (mapPoint f s.2) := by
    intro hc
    rcases houter.2 _ (Finset.mem_image.mpr ⟨s.2,hsfree.1.2.1,rfl⟩) hc with h | h
    · exact he (Or.inr (Or.inl (mapPoint_injective_on hP f hsfree.1.2.1 hr.1 h).symm))
    · exact he (Or.inr (Or.inr
        (Or.inr (mapPoint_injective_on hP f hsfree.1.2.1 hr.2.1 h).symm)))
  have hrt := hr.2.2.1
  have hst := hsfree.1.2.2.1
  have hn : NoCorner s r := by
    intro p hp hc
    have hm := contains_map f hf hc
    rcases r with ⟨⟨a,t⟩,⟨b,u⟩⟩
    rcases s with ⟨⟨c,v⟩,⟨d,w⟩⟩
    rcases p with ⟨x,y⟩
    rcases hp with ⟨hx,hy⟩
    dsimp only at hx hy
    rcases hx with hx | hx <;> rcases hy with hy | hy <;>
      subst x <;> subst y <;>
      simp only [Contains, mapRectangle, mapPoint] at * <;> omega
  exact Or.inr ⟨noCorner_symm hsfree hrfree (fun h => he (shared_symm h)) hn, hn⟩

theorem robustPair_distinct_fibers (f : Int → Int) (hf : Monotone f)
    {P : Finset Point} {i j : Int} {r s : Rectangle}
    (hr : InputFree (fiber f i P) r) (hs : InputFree (fiber f j P) s)
    (hij : i ≠ j) : RobustPair r s := by
  have hrfree := inputFree_of_fiber f hf hr
  have hsfree := inputFree_of_fiber f hf hs
  apply robustPair_of_noCorner hrfree hsfree
  intro p hp hc
  have hm := contains_map f hf hc
  have hr₁ := (Finset.mem_filter.mp hr.1.1).2
  have hr₂ := (Finset.mem_filter.mp hr.1.2.1).2
  have hs₁ := (Finset.mem_filter.mp hs.1.1).2
  have hs₂ := (Finset.mem_filter.mp hs.1.2.1).2
  have hpj : f p.1 = j := by
    rcases hp.1 with h | h
    · simpa [h] using hs₁
    · simpa [h] using hs₂
  have hpi : f p.1 = i := by
    have hleft : i ≤ f p.1 := by simpa [mapRectangle, mapPoint, hr₁, hr₂] using hm.1
    have hright : f p.1 ≤ i := by simpa [mapRectangle, mapPoint, hr₁, hr₂] using hm.2.1
    exact le_antisymm hright hleft
  exact hij (hpi.symm.trans hpj)

end TangoSquared.Paper20261030.Rectangles
