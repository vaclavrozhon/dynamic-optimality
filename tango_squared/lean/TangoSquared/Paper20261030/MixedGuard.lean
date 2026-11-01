import TangoSquared.Paper20261030.MaximalRectangles

/-!
# Constructing the guard for an unpaid mixed turn

If a mixed-turn window has no double-switch donor, all its later local
points have the second endpoint's key. The next internal start is an
actual guard. If there is no such start, a finite time beyond the input
represents infinity. In BOTH cases the horizontal boundary is the second
endpoint's key, so that its own access is excluded from the open strip.
This corrects the manuscript's `previous key - 1` choice in the absent-
guard branch, which would put that access inside the purported empty strip.
-/

namespace TangoSquared.Paper20261030.Rectangles

theorem color_between (f : Int → Int) (hf : Monotone f) {a b x : Int}
    (he : f a = f b) (hax : a ≤ x) (hxb : x ≤ b) : f x = f b := by
  exact le_antisymm (hf hxb) (he ▸ hf hax)

theorem mixed_guard {P : Finset Point} {f : Int → Int} {p p' q : Point}
    (hnext : NextDifferent P p p') (hcolor : f p.1 = f p'.1)
    (hq : q ∈ P) (hturn : Turn p p' q)
    (hgap : ∀ h h', NextDifferent P h h' → f h.1 = f p.1 → f h'.1 = f p.1 →
      p.2 < h.2 → q.2 < h.2)
    (hconstant : ∀ z ∈ P, f z.1 = f p.1 → Window P f p z → z.1 = p'.1) :
    ∃ gy : Int, q.2 < gy ∧ ((p'.1,gy) ∈ P ∨ ∀ z ∈ P, z.2 < gy) ∧
      ∀ z ∈ P, f z.1 = f p.1 → p.2 < z.2 → z.2 < gy → z.1 = p'.1 := by
  classical
  let starts := P.filter (fun h => p.2 < h.2 ∧ InternalStart P f (f p.1) h)
  by_cases hex : starts.Nonempty
  · obtain ⟨h,hh,hmin⟩ := Finset.exists_min_image starts Prod.snd hex
    obtain ⟨hhP,hph,hhstart⟩ := Finset.mem_filter.mp hh
    have hwin : Window P f p h := by
      refine ⟨hph,?_⟩
      intro z hz hpz hzh
      have hzP := hz.choose_spec.1.1
      have hle := hmin z (Finset.mem_filter.mpr ⟨hzP,hpz,hz⟩)
      exact (not_le_of_gt hzh) hle
    obtain ⟨h',hhnext,hhcolor,hh'color⟩ := hhstart
    have hqh := hgap h h' hhnext hhcolor hh'color hph
    have hkey := hconstant h hhP hhcolor hwin
    refine ⟨h.2,hqh,Or.inl ?_,?_⟩
    · have he : (p'.1,h.2) = h := Prod.ext hkey.symm rfl
      exact he.symm ▸ hhP
    · intro z hz hzcolor hpz hzh
      exact hconstant z hz hzcolor (window_prefix hwin hpz hzh.le)
  · let times := P.image Prod.snd
    have ht : times.Nonempty := ⟨q.2,Finset.mem_image.mpr ⟨q,hq,rfl⟩⟩
    let gy := times.max' ht + 1
    have hall : ∀ z ∈ P, z.2 < gy := by
      intro z hz
      have hle := Finset.le_max' times z.2 (Finset.mem_image.mpr ⟨z,hz,rfl⟩)
      dsimp [gy]
      omega
    refine ⟨gy,hall q hq,Or.inr hall,?_⟩
    intro z hz hzcolor hpz _
    apply hconstant z hz hzcolor
    refine ⟨hpz,?_⟩
    intro h hh hph _
    exact hex ⟨h,Finset.mem_filter.mpr ⟨hh.choose_spec.1.1,hph,hh⟩⟩

/-- In a maximal robust family, an unpaid mixed turn creates a rectangle
from its own actual source point to a later point in a different segment. -/
theorem mixed_rectangle_or_donor {P : Finset Point} (hP : Instance P)
    (f : Int → Int) (hf : Monotone f) {p : Point} (hmixed : MixedTurn P f p)
    {S : Finset Rectangle} (hS : MaximalRobust P S) :
    (∃ u ∈ P, f u.1 = f p.1 ∧ Window P f p u ∧ DoubleSwitch P f u) ∨
    (∃ p' z, Next P p p' ∧ f p.1 = f p'.1 ∧ z ∈ P ∧
      p'.2 < z.2 ∧ f p.1 ≠ f z.1 ∧ (p,z) ∈ S) := by
  classical
  obtain ⟨p',q,hnd,hcolor,hq,hqcolor,hturn,hgap⟩ := hmixed
  have hnext := mixed_pair_consecutive hnd hcolor hturn hgap
  by_cases hchange : ∃ u ∈ P, f u.1 = f p.1 ∧ Window P f p u ∧ u.1 ≠ p'.1
  · exact Or.inl (exists_doubleSwitch_donor hP f hnext hcolor hchange)
  have hconstant : ∀ z ∈ P, f z.1 = f p.1 → Window P f p z → z.1 = p'.1 := by
    intro z hz hzcolor hwin
    by_contra hne
    exact hchange ⟨z,hz,hzcolor,hwin,hne⟩
  obtain ⟨gy,hqgy,hguard,hlocal⟩ := mixed_guard hnd hcolor hq hturn hgap hconstant
  have hrect : ∃ z ∈ P, p.2 < z.2 ∧ z.2 < gy ∧ z.1 ≠ p'.1 ∧
      RobustFamily P (insert (p,z) S) := by
    rcases hturn.2.2 with ⟨hpUp,hqDown⟩ | ⟨hpDown,hqUp⟩
    · have hqleft : q.1 < p.1 := by
        by_contra hh
        have he := color_between f hf hcolor (by omega) hqDown.le
        exact hqcolor (he.trans hcolor.symm)
      have hempty : ∀ z ∈ P, p.1 ≤ z.1 → z.1 < p'.1 → p.2 < z.2 → z.2 < gy → False := by
        intro z hz hx₁ hx₂ ht₁ ht₂
        have he := color_between f hf hcolor hx₁ hx₂.le
        have hk := hlocal z hz (he.trans hcolor.symm) ht₁ ht₂
        omega
      obtain ⟨z,hz,hzx,hzt,hzgy,hnew⟩ := rectangle_extension_left hP hnd.1 p'.1 gy
        hpUp hguard hempty ⟨q,hq,hqleft,lt_trans hturn.1 hturn.2.1,hqgy⟩ hS.1
      exact ⟨z,hz,hzt,hzgy,by omega,hnew⟩
    · have hqright : p.1 < q.1 := by
        by_contra hh
        have he := color_between f hf hcolor.symm hqUp.le (by omega)
        exact hqcolor he
      have hempty : ∀ z ∈ P, p'.1 < z.1 → z.1 ≤ p.1 → p.2 < z.2 → z.2 < gy → False := by
        intro z hz hx₁ hx₂ ht₁ ht₂
        have he := color_between f hf hcolor.symm hx₁.le hx₂
        have hk := hlocal z hz he ht₁ ht₂
        omega
      obtain ⟨z,hz,hzx,hzt,hzgy,hnew⟩ := rectangle_extension hP hnd.1 p'.1 gy
        hpDown hguard hempty ⟨q,hq,hqright,lt_trans hturn.1 hturn.2.1,hqgy⟩ hS.1
      exact ⟨z,hz,hzt,hzgy,by omega,hnew⟩
  obtain ⟨z,hz,hzt,hzgy,hzne,hnew⟩ := hrect
  have hp'z : p'.2 < z.2 := by
    by_contra hh
    by_cases he : z.2 = p'.2
    · exact hzne (congrArg Prod.fst (hP z hz p' hnext.2.1 he))
    · exact hnext.2.2.2 z hz hzt (by omega)
  have hcross : f p.1 ≠ f z.1 := by
    intro he
    exact hzne (hlocal z hz he.symm hzt hzgy)
  exact Or.inr ⟨p',z,hnext,hcolor,hz,hp'z,hcross,hS.2 (p,z) hnew⟩

end TangoSquared.Paper20261030.Rectangles
