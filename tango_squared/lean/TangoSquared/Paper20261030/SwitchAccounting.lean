import TangoSquared.Paper20261030.Chronology

/-!
# Exact switch accounting under a split

`eventCount` counts actual input points satisfying an event predicate.
`doubleSwitchCount` counts points that are switches both in their own
filtered segment and in the contracted instance. The final identity is
the unscaled statement of manuscript Lemma `phi-1-bound`.
-/

namespace TangoSquared.Paper20261030.Rectangles

open scoped BigOperators
attribute [local instance] Classical.propDecidable

noncomputable def eventCount (P : Finset Point) (event : Point → Prop) : Nat := by
  classical
  exact ∑ p ∈ P, if event p then 1 else 0

noncomputable def switchCount (P : Finset Point) : Nat := eventCount P (SwitchPoint P)
noncomputable def turnCount (P : Finset Point) : Nat := eventCount P (TurnPoint P)
noncomputable def depthAlternations (P : Finset Point) (f : Int → Int) : Nat :=
  eventCount P (DepthExit P f)
noncomputable def mixedTurns (P : Finset Point) (f : Int → Int) : Nat :=
  eventCount P (MixedTurn P f)

def DoubleSwitch (P : Finset Point) (f : Int → Int) (p : Point) : Prop :=
  SwitchPoint (project f P) (mapPoint f p) ∧ SwitchPoint (fiber f (f p.1) P) p

noncomputable def doubleSwitchCount (P : Finset Point) (f : Int → Int) : Nat :=
  eventCount P (DoubleSwitch P f)

theorem eventCount_eq_card (P : Finset Point) (event : Point → Prop) :
    eventCount P event = (P.filter event).card := by
  classical
  simp only [eventCount,Finset.card_eq_sum_ones,Finset.sum_filter]

theorem eventCount_project {P : Finset Point} (hP : Instance P)
    (f : Int → Int) (event : Point → Prop) :
    eventCount (project f P) event = eventCount P (fun p => event (mapPoint f p)) := by
  classical
  unfold eventCount project
  rw [Finset.sum_image]
  intro p hp q hq he
  exact mapPoint_injective_on hP f hp hq he

theorem switchCount_fibers (P : Finset Point) (f : Int → Int) (I : Finset Int)
    (hI : ∀ p ∈ P, f p.1 ∈ I) :
    ∑ i ∈ I, switchCount (fiber f i P) =
      eventCount P (fun p => SwitchPoint (fiber f (f p.1) P) p) := by
  classical
  unfold switchCount eventCount
  calc
    _ = ∑ i ∈ I, ∑ p ∈ P.filter (fun p => f p.1 = i),
        if SwitchPoint (fiber f (f p.1) P) p then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro p hp
      rw [(Finset.mem_filter.mp hp).2]
    _ = _ := Finset.sum_fiberwise_of_maps_to hI _

/-- Exact switch identity, including empty fibers and repeated accesses. -/
theorem switch_split_identity {P : Finset Point} (hP : Instance P)
    (f : Int → Int) (I : Finset Int) (hI : ∀ p ∈ P, f p.1 ∈ I) :
    switchCount (project f P) + ∑ i ∈ I, switchCount (fiber f i P) =
      switchCount P + doubleSwitchCount P f := by
  classical
  rw [switchCount_fibers P f I hI]
  unfold switchCount
  rw [eventCount_project hP f]
  unfold doubleSwitchCount eventCount
  rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  have he := switchPoint_split_iff hP f hp
  by_cases ho : SwitchPoint (project f P) (mapPoint f p) <;>
    by_cases hi : SwitchPoint (fiber f (f p.1) P) p <;>
    simp_all [DoubleSwitch]

noncomputable def switchEdges (P : Finset Point) : Finset Rectangle := by
  classical
  exact (P ×ˢ P).filter (fun r => Next P r.1 r.2 ∧ r.1.1 ≠ r.2.1)

theorem mem_switchEdges {P : Finset Point} {r : Rectangle} :
    r ∈ switchEdges P ↔ Next P r.1 r.2 ∧ r.1.1 ≠ r.2.1 := by
  classical
  simp only [switchEdges,Finset.mem_filter,Finset.mem_product]
  constructor
  · exact fun h => h.2
  · exact fun h => ⟨⟨h.1.1,h.1.2.1⟩,h⟩

theorem switchEdges_on {P : Finset Point} {r : Rectangle} (hr : r ∈ switchEdges P) :
    On P r := by
  obtain ⟨h,hne⟩ := mem_switchEdges.mp hr
  exact ⟨h.1,h.2.1,h.2.2.1,hne⟩

theorem switchEdges_inputFree {P : Finset Point} (hP : Instance P)
    {r : Rectangle} (hr : r ∈ switchEdges P) : InputFree P r := by
  obtain ⟨h,hne⟩ := mem_switchEdges.mp hr
  refine ⟨⟨h.1,h.2.1,h.2.2.1,hne⟩,?_⟩
  intro z hz hc
  by_cases he₁ : z.2 = r.1.2
  · exact Or.inl (hP z hz r.1 h.1 he₁)
  by_cases he₂ : z.2 = r.2.2
  · exact Or.inr (hP z hz r.2 h.2.1 he₂)
  exact (h.2.2.2 z hz (by have := hc.2.2.1; omega)
    (by have := hc.2.2.2; omega)).elim

theorem switchEdges_image (P : Finset Point) :
    (switchEdges P).image Prod.snd = P.filter (SwitchPoint P) := by
  classical
  ext q
  constructor
  · intro hq
    obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨h,hne⟩ := mem_switchEdges.mp hr
    exact Finset.mem_filter.mpr ⟨h.2.1,r.1,h,hne⟩
  · intro hq
    obtain ⟨_,p,h,hne⟩ := Finset.mem_filter.mp hq
    exact Finset.mem_image.mpr ⟨(p,q),mem_switchEdges.mpr ⟨h,hne⟩,rfl⟩

theorem switchCount_eq_edges {P : Finset Point} (hP : Instance P) :
    switchCount P = (switchEdges P).card := by
  classical
  rw [switchCount,eventCount_eq_card,← switchEdges_image]
  apply Finset.card_image_iff.mpr
  intro r hr s hs he
  apply Prod.ext _ he
  obtain ⟨hr,_⟩ := mem_switchEdges.mp hr
  obtain ⟨hs,_⟩ := mem_switchEdges.mp hs
  exact next_previous_unique hP hr (he ▸ hs)

theorem switchEdges_robust {P : Finset Point} (hP : Instance P) :
    RobustFamily P (switchEdges P) := by
  refine ⟨fun _ hr => switchEdges_inputFree hP hr,?_⟩
  intro r hr s hs hne
  by_cases hshared : Shared r s
  · exact Or.inl hshared
  have hrfree := switchEdges_inputFree hP hr
  have hsfree := switchEdges_inputFree hP hs
  apply robustPair_of_noCorner hrfree hsfree
  intro p hp hc
  have htimes := nonshared_times hP hrfree.1 hsfree.1 hshared
  have hrnext := (mem_switchEdges.mp hr).1
  have hsnext := (mem_switchEdges.mp hs).1
  rcases hp.2 with ht | ht
  · have htlo : r.1.2 < s.1.2 := by have := hc.2.2.1; omega
    have hthi : s.1.2 < r.2.2 := by have := hc.2.2.2; omega
    exact hrnext.2.2.2 s.1 hsnext.1 htlo hthi
  · have htlo : r.1.2 < s.2.2 := by have := hc.2.2.1; omega
    have hthi : s.2.2 < r.2.2 := by have := hc.2.2.2; omega
    exact hrnext.2.2.2 s.2 hsnext.2.1 htlo hthi

/-- Consecutive unequal accesses form an actual robust rectangle family. -/
theorem switchCount_le_robustBound {P : Finset Point} (hP : Instance P) :
    switchCount P ≤ robustBound P := by
  rw [switchCount_eq_edges hP]
  exact robust_card_le (switchEdges_robust hP)

end TangoSquared.Paper20261030.Rectangles
