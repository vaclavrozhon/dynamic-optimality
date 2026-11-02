import ChaCha.Paper20261030.MixedWindow

/-!
# Maximal extensions and new mixed-turn rectangles

Maximality is constructed by maximizing cardinality in a finite powerset.
`split_union_excludes_crossing` identifies the genuinely new rectangles:
their projected lower edge already contains a later same-segment access,
so they cannot come from either part of the split certificate.
-/

namespace ChaCha.Paper20261030.Rectangles

def MaximalRobust (P : Finset Point) (R : Finset Rectangle) : Prop :=
  RobustFamily P R ∧ ∀ r, RobustFamily P (insert r R) → r ∈ R

theorem exists_maximal_extension {P : Finset Point} {R : Finset Rectangle}
    (hR : RobustFamily P R) : ∃ S, R ⊆ S ∧ MaximalRobust P S := by
  classical
  let families := (P ×ˢ P).powerset.filter (fun S => R ⊆ S ∧ RobustFamily P S)
  have hRmem : R ∈ families := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr ?_,Finset.Subset.refl R,hR⟩
    intro r hr
    exact Finset.mem_product.mpr ⟨(hR.1 r hr).1.1,(hR.1 r hr).1.2.1⟩
  obtain ⟨S,hS,hmax⟩ := Finset.exists_max_image families Finset.card ⟨R,hRmem⟩
  obtain ⟨_,hRS,hSrobust⟩ := Finset.mem_filter.mp hS
  refine ⟨S,hRS,hSrobust,?_⟩
  intro r hr
  have hins : insert r S ∈ families := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr ?_,hRS.trans (Finset.subset_insert _ _),hr⟩
    intro s hs
    exact Finset.mem_product.mpr ⟨(hr.1 s hs).1.1,(hr.1 s hs).1.2.1⟩
  have hc := hmax (insert r S) hins
  by_contra hnot
  rw [Finset.card_insert_of_notMem hnot] at hc
  omega

theorem split_union_excludes_crossing {P : Finset Point} (hP : Instance P)
    (f : Int → Int) (I : Finset Int)
    (outer : Finset Rectangle) (inner : Int → Finset Rectangle)
    (ho : RobustFamily (project f P) outer)
    (hi : ∀ i ∈ I, RobustFamily (fiber f i P) (inner i))
    {p p' q : Point} (hp' : p' ∈ P) (hcolor : f p.1 = f p'.1)
    (hcross : f p.1 ≠ f q.1) (ht₁ : p.2 < p'.2) (ht₂ : p'.2 < q.2) :
    (p,q) ∉ outer.image (pullRectangle P f) ∪ I.biUnion inner := by
  intro h
  rcases Finset.mem_union.mp h with h | h
  · obtain ⟨r,hr,he⟩ := Finset.mem_image.mp h
    have hmap := map_pullRectangle (ho.1 r hr).1
    rw [he] at hmap
    have hfree : InputFree (project f P) (mapRectangle f (p,q)) := by
      simpa only [hmap] using ho.1 r hr
    have hcontains : Contains (mapRectangle f (p,q)) (mapPoint f p') := by
      simp only [Contains,mapRectangle,mapPoint]
      omega
    have heq := hfree.2 (mapPoint f p') (Finset.mem_image.mpr ⟨p',hp',rfl⟩) hcontains
    rcases heq with heq | heq
    · have ht := congrArg Prod.snd heq
      dsimp [mapPoint,mapRectangle] at ht
      omega
    · have ht := congrArg Prod.snd heq
      dsimp [mapPoint,mapRectangle] at ht
      omega
  · obtain ⟨i,hiI,hr⟩ := Finset.mem_biUnion.mp h
    have h₁ := (Finset.mem_filter.mp ((hi i hiI).1 (p,q) hr).1.1).2
    have h₂ := (Finset.mem_filter.mp ((hi i hiI).1 (p,q) hr).1.2.1).2
    exact hcross (h₁.trans h₂.symm)

end ChaCha.Paper20261030.Rectangles
