import TangoSquared.Paper20261030.MixedRectangleAccounting

/-!
# Time-reversal accounting and the rectangle part of the split potential

Switch counts are invariant under reversing time. The exact split identity
then proves invariance of double-switch counts. Applying the strengthened
rectangle split inequality in both time directions yields the coefficient-
five rectangle-potential estimate of manuscript Lemma `phi-3-bound`.
-/

namespace TangoSquared.Paper20261030.Rectangles

open scoped BigOperators

theorem instance_reverse {P : Finset Point} (hP : Instance P) :
    Instance (P.image reversePoint) := by
  intro p hp q hq he
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hq
  apply congrArg reversePoint
  apply hP a ha b hb
  dsimp [reversePoint] at he
  omega

theorem next_reverse {P : Finset Point} {p q : Point} (h : Next P p q) :
    Next (P.image reversePoint) (reversePoint q) (reversePoint p) := by
  refine ⟨Finset.mem_image.mpr ⟨q,h.2.1,rfl⟩,
    Finset.mem_image.mpr ⟨p,h.1,rfl⟩,by dsimp [reversePoint]; have := h.2.2.1; omega,?_⟩
  intro z hz hqz hzp
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hz
  apply h.2.2.2 a ha
  · dsimp [reversePoint] at hzp
    omega
  · dsimp [reversePoint] at hqz
    omega

theorem reverse_mem_switchEdges {P : Finset Point} {r : Rectangle}
    (h : r ∈ switchEdges P) : reverseRectangle r ∈ switchEdges (P.image reversePoint) := by
  obtain ⟨hn,hne⟩ := mem_switchEdges.mp h
  exact mem_switchEdges.mpr ⟨next_reverse hn,Ne.symm hne⟩

theorem switchEdges_reverse (P : Finset Point) :
    switchEdges (P.image reversePoint) = (switchEdges P).image reverseRectangle := by
  ext r
  constructor
  · intro hr
    have h := reverse_mem_switchEdges hr
    have hback : reverseRectangle r ∈ switchEdges P := by
      have he : (P.image reversePoint).image reversePoint = P := timeReversal.point_image_image P
      simpa only [he] using h
    exact Finset.mem_image.mpr ⟨reverseRectangle r,hback,reverseRectangle_involutive r⟩
  · intro hr
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hr
    exact reverse_mem_switchEdges ha

theorem switchCount_reverse {P : Finset Point} (hP : Instance P) :
    switchCount (P.image reversePoint) = switchCount P := by
  rw [switchCount_eq_edges (instance_reverse hP),switchCount_eq_edges hP,switchEdges_reverse]
  exact Finset.card_image_of_injective _ reverseRectangle_involutive.injective

theorem project_reverse (P : Finset Point) (f : Int → Int) :
    project f (P.image reversePoint) = (project f P).image reversePoint := by
  simp only [project,Finset.image_image]
  rfl

theorem fiber_reverse (P : Finset Point) (f : Int → Int) (i : Int) :
    fiber f i (P.image reversePoint) = (fiber f i P).image reversePoint := by
  ext p
  constructor
  · intro hp
    obtain ⟨hp,hcolor⟩ := Finset.mem_filter.mp hp
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_image.mpr ⟨a,Finset.mem_filter.mpr ⟨ha,hcolor⟩,rfl⟩
  · intro hp
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨haP,hcolor⟩ := Finset.mem_filter.mp ha
    exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨a,haP,rfl⟩,hcolor⟩

theorem doubleSwitchCount_reverse {P : Finset Point} (hP : Instance P)
    (f : Int → Int) : doubleSwitchCount (P.image reversePoint) f = doubleSwitchCount P f := by
  let I := P.image (fun p => f p.1)
  have hI : ∀ p ∈ P, f p.1 ∈ I := fun p hp => Finset.mem_image.mpr ⟨p,hp,rfl⟩
  have hIR : ∀ p ∈ P.image reversePoint, f p.1 ∈ I := by
    intro p hp
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hp
    exact hI a ha
  have hforward := switch_split_identity hP f I hI
  have hreverse := switch_split_identity (instance_reverse hP) f I hIR
  have hsum : (∑ i ∈ I, switchCount (fiber f i (P.image reversePoint))) =
      ∑ i ∈ I, switchCount (fiber f i P) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [fiber_reverse,switchCount_reverse (instance_fiber hP f i)]
  rw [project_reverse,switchCount_reverse (instance_project hP f),hsum,switchCount_reverse hP]
    at hreverse
  omega

/-- Natural-number version of `Δ(5 rir) ≥ 2(mixed + reversedMixed) - 4 double`. -/
theorem rectangle_potential_release {P : Finset Point} (hP : Instance P)
    (f : Int → Int) (hf : Monotone f) (I : Finset Int) :
    5 * (robustBound (project f P) + ∑ i ∈ I, robustBound (fiber f i P)) +
      2 * (mixedTurns P f + mixedTurns (P.image reversePoint) f) ≤
      5 * robustBound P + 4 * doubleSwitchCount P f := by
  have hbase := robustBound_split hP f hf I
  have hforward := robustBound_split_mixed hP f hf I
  have hreverse := robustBound_split_mixed (instance_reverse hP) f hf I
  have hsum : (∑ i ∈ I, robustBound (fiber f i (P.image reversePoint))) =
      ∑ i ∈ I, robustBound (fiber f i P) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [fiber_reverse,robustBound_reverse]
  rw [project_reverse,robustBound_reverse,hsum,robustBound_reverse,doubleSwitchCount_reverse hP]
    at hreverse
  omega

end TangoSquared.Paper20261030.Rectangles
