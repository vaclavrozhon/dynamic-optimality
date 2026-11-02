import ChaCha.Paper20261030.RectangleProjection
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Union of robust rectangle certificates under an interval split

The theorem `split_certificate` constructs the union from actual rectangle
families in the contracted instance and in the fibers. It proves both
robust independence and exact cardinality (manuscript Lemma `rir-union`).
`robustBound_split` applies this construction to maximizing families.
-/

namespace ChaCha.Paper20261030.Rectangles

open scoped BigOperators

noncomputable def pullPoint (P : Finset Point) (f : Int → Int) (p : Point) : Point :=
  if h : p ∈ project f P then Classical.choose (Finset.mem_image.mp h) else p

theorem pullPoint_spec {P : Finset Point} {f : Int → Int} {p : Point}
    (hp : p ∈ project f P) :
    pullPoint P f p ∈ P ∧ mapPoint f (pullPoint P f p) = p := by
  classical
  simp only [pullPoint, dif_pos hp]
  exact Classical.choose_spec (Finset.mem_image.mp hp)

noncomputable def pullRectangle (P : Finset Point) (f : Int → Int)
    (r : Rectangle) : Rectangle := (pullPoint P f r.1, pullPoint P f r.2)

theorem map_pullRectangle {P : Finset Point} {f : Int → Int} {r : Rectangle}
    (hr : On (project f P) r) : mapRectangle f (pullRectangle P f r) = r := by
  exact Prod.ext (pullPoint_spec hr.1).2 (pullPoint_spec hr.2.1).2

theorem pullRectangle_on {P : Finset Point} {f : Int → Int} {r : Rectangle}
    (hr : On (project f P) r) : On P (pullRectangle P f r) := by
  obtain ⟨hb,heb⟩ := pullPoint_spec hr.1
  obtain ⟨ht,het⟩ := pullPoint_spec hr.2.1
  refine ⟨hb,ht,?_,?_⟩
  · have hbt := congrArg Prod.snd heb
    have htt := congrArg Prod.snd het
    change (pullPoint P f r.1).2 < (pullPoint P f r.2).2
    exact hbt ▸ htt ▸ hr.2.2.1
  · intro he
    apply hr.2.2.2
    have hbk := congrArg Prod.fst heb
    have htk := congrArg Prod.fst het
    exact hbk.symm.trans ((congrArg f he).trans htk)

theorem robustFamily_pull {P : Finset Point} (hP : Instance P)
    (f : Int → Int) (hf : Monotone f) {R : Finset Rectangle}
    (hR : RobustFamily (project f P) R) :
    RobustFamily P (R.image (pullRectangle P f)) := by
  constructor
  · intro r hr
    obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hr
    apply inputFree_of_project hP f hf (pullRectangle_on (hR.1 s hs).1)
    simpa only [map_pullRectangle (hR.1 s hs).1] using hR.1 s hs
  · intro r hr s hs hne
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hr
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hs
    apply robustPair_of_project hP f hf
      (pullRectangle_on (hR.1 a ha).1) (pullRectangle_on (hR.1 b hb).1)
    rw [map_pullRectangle (hR.1 a ha).1, map_pullRectangle (hR.1 b hb).1]
    exact hR.2 a ha b hb (fun h => hne (congrArg (pullRectangle P f) h))

theorem card_pull {P : Finset Point} {f : Int → Int} {R : Finset Rectangle}
    (hR : RobustFamily (project f P) R) :
    (R.image (pullRectangle P f)).card = R.card := by
  apply Finset.card_image_iff.mpr
  intro r hr s hs he
  have hm := congrArg (mapRectangle f) he
  simpa only [map_pullRectangle (hR.1 r hr).1,
    map_pullRectangle (hR.1 s hs).1] using hm

theorem robustPair_symm {r s : Rectangle} (h : RobustPair r s) : RobustPair s r := by
  rcases h with h | ⟨h₁,h₂⟩
  · exact Or.inl (shared_symm h)
  · exact Or.inr ⟨h₂,h₁⟩

theorem robustFamily_inner_union (f : Int → Int) (hf : Monotone f)
    (P : Finset Point) (I : Finset Int) (R : Int → Finset Rectangle)
    (hR : ∀ i ∈ I, RobustFamily (fiber f i P) (R i)) :
    RobustFamily P (I.biUnion R) := by
  constructor
  · intro r hr
    obtain ⟨i,hi,hr⟩ := Finset.mem_biUnion.mp hr
    exact inputFree_of_fiber f hf ((hR i hi).1 r hr)
  · intro r hr s hs hne
    obtain ⟨i,hi,hr⟩ := Finset.mem_biUnion.mp hr
    obtain ⟨j,hj,hs⟩ := Finset.mem_biUnion.mp hs
    by_cases hij : i = j
    · subst j
      exact (hR i hi).2 r hr s hs hne
    · exact robustPair_distinct_fibers f hf ((hR i hi).1 r hr) ((hR j hj).1 s hs) hij

theorem inner_disjoint (f : Int → Int) (P : Finset Point)
    (I : Finset Int) (R : Int → Finset Rectangle)
    (hR : ∀ i ∈ I, RobustFamily (fiber f i P) (R i)) :
    (I : Set Int).PairwiseDisjoint R := by
  intro i hi j hj hij
  apply Finset.disjoint_left.mpr
  intro r hr hs
  have hri := (Finset.mem_filter.mp ((hR i hi).1 r hr).1.1).2
  have hrj := (Finset.mem_filter.mp ((hR j hj).1 r hs).1.1).2
  exact hij (hri.symm.trans hrj)

/-- Concrete form of manuscript Lemma `rir-union`. -/
theorem split_certificate {P : Finset Point} (hP : Instance P)
    (f : Int → Int) (hf : Monotone f) (I : Finset Int)
    (outer : Finset Rectangle) (inner : Int → Finset Rectangle)
    (ho : RobustFamily (project f P) outer)
    (hi : ∀ i ∈ I, RobustFamily (fiber f i P) (inner i)) :
    let R := outer.image (pullRectangle P f) ∪ I.biUnion inner
    RobustFamily P R ∧ R.card = outer.card + ∑ i ∈ I, (inner i).card := by
  dsimp only
  have hout := robustFamily_pull hP f hf ho
  have hin := robustFamily_inner_union f hf P I inner hi
  have hcross : ∀ r ∈ outer.image (pullRectangle P f),
      ∀ s ∈ I.biUnion inner, RobustPair r s := by
    intro r hr s hs
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hr
    obtain ⟨i,hiI,hsi⟩ := Finset.mem_biUnion.mp hs
    apply robustPair_outer_inner hP f hf (pullRectangle_on (ho.1 a ha).1)
    · simpa only [map_pullRectangle (ho.1 a ha).1] using ho.1 a ha
    · exact (hi i hiI).1 s hsi
  have hd : Disjoint (outer.image (pullRectangle P f)) (I.biUnion inner) := by
    apply Finset.disjoint_left.mpr
    intro r hr hs
    obtain ⟨s,hsout,rfl⟩ := Finset.mem_image.mp hr
    obtain ⟨i,hiI,hsin⟩ := Finset.mem_biUnion.mp hs
    have hkeys := (ho.1 s hsout).1.2.2.2
    have h₁ := (Finset.mem_filter.mp ((hi i hiI).1 _ hsin).1.1).2
    have h₂ := (Finset.mem_filter.mp ((hi i hiI).1 _ hsin).1.2.1).2
    have he := map_pullRectangle (ho.1 s hsout).1
    have ha := congrArg (fun r : Rectangle => r.1.1) he
    have hb := congrArg (fun r : Rectangle => r.2.1) he
    exact hkeys (ha.symm.trans ((h₁.trans h₂.symm).trans hb))
  constructor
  · constructor
    · intro r hr
      rcases Finset.mem_union.mp hr with hr | hr
      · exact hout.1 r hr
      · exact hin.1 r hr
    · intro r hr s hs hne
      rcases Finset.mem_union.mp hr with hr | hr <;>
        rcases Finset.mem_union.mp hs with hs | hs
      · exact hout.2 r hr s hs hne
      · exact hcross r hr s hs
      · exact robustPair_symm (hcross s hs r hr)
      · exact hin.2 r hr s hs hne
  · rw [Finset.card_union_of_disjoint hd, card_pull ho,
      Finset.card_biUnion (inner_disjoint f P I inner hi)]

theorem exists_robust_maximum (P : Finset Point) :
    ∃ R, RobustFamily P R ∧ R.card = robustBound P := by
  classical
  let families := (P ×ˢ P).powerset.filter (RobustFamily P)
  have hempty : (∅ : Finset Rectangle) ∈ families := by
    simp [families, RobustFamily]
  obtain ⟨R,hR,he⟩ := Finset.exists_mem_eq_sup families ⟨∅,hempty⟩ Finset.card
  exact ⟨R,(Finset.mem_filter.mp hR).2,he.symm⟩

/-- The robust rectangle bound is superadditive under convex splitting. -/
theorem robustBound_split {P : Finset Point} (hP : Instance P)
    (f : Int → Int) (hf : Monotone f) (I : Finset Int) :
    robustBound (project f P) + ∑ i ∈ I, robustBound (fiber f i P) ≤ robustBound P := by
  classical
  obtain ⟨outer,ho,hocard⟩ := exists_robust_maximum (project f P)
  choose inner hi hicard using fun i : Int => exists_robust_maximum (fiber f i P)
  obtain ⟨hR,hcard⟩ := split_certificate hP f hf I outer inner ho (fun i _ => hi i)
  have hbound := robust_card_le hR
  rw [hcard,hocard] at hbound
  simpa only [hicard] using hbound

end ChaCha.Paper20261030.Rectangles
