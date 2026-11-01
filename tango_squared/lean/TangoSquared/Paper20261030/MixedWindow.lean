import TangoSquared.Paper20261030.SwitchAccounting

/-!
# Time windows and double-switch payments for mixed turns

An `InternalStart` begins a next-different pair inside one segment.
`Window P f p z` extends strictly after `p` up to, and including, the next
internal start in `p`'s segment. A first different local key in that window
is a genuine double switch. Distinct internal starts cannot charge the same
point through these windows.
-/

namespace TangoSquared.Paper20261030.Rectangles

def InternalStart (P : Finset Point) (f : Int → Int) (i : Int) (p : Point) : Prop :=
  ∃ q, NextDifferent P p q ∧ f p.1 = i ∧ f q.1 = i

def Window (P : Finset Point) (f : Int → Int) (p z : Point) : Prop :=
  p.2 < z.2 ∧ ∀ h, InternalStart P f (f p.1) h → p.2 < h.2 → h.2 < z.2 → False

theorem next_different {P : Finset Point} {p q : Point}
    (h : Next P p q) (hne : p.1 ≠ q.1) : NextDifferent P p q := by
  refine ⟨h.1,h.2.1,h.2.2.1,hne,?_⟩
  intro z hz hpz hzq
  exact (h.2.2.2 z hz hpz hzq).elim

theorem previous_ge {P : Finset Point} {p q z : Point}
    (h : Next P p q) (hz : z ∈ P) (hzq : z.2 < q.2) : z.2 ≤ p.2 := by
  by_contra hh
  exact h.2.2.2 z hz (by omega) hzq

theorem window_prefix {P : Finset Point} {f : Int → Int} {p z w : Point}
    (h : Window P f p z) (hpw : p.2 < w.2) (hwz : w.2 ≤ z.2) : Window P f p w := by
  exact ⟨hpw,fun q hq hpq hqw => h.2 q hq hpq (lt_of_lt_of_le hqw hwz)⟩

theorem mixed_internalStart {P : Finset Point} {f : Int → Int} {p : Point}
    (h : MixedTurn P f p) : InternalStart P f (f p.1) p := by
  obtain ⟨p',q,hnext,hcolor,_⟩ := h
  exact ⟨p',hnext,rfl,hcolor.symm⟩

/-- A mixed turn's first pair is actually consecutive, even with repetitions. -/
theorem mixed_pair_consecutive {P : Finset Point} {f : Int → Int}
    {p p' q : Point} (hnext : NextDifferent P p p') (hcolor : f p.1 = f p'.1)
    (hturn : Turn p p' q)
    (hgap : ∀ h h', NextDifferent P h h' → f h.1 = f p.1 → f h'.1 = f p.1 →
      p.2 < h.2 → q.2 < h.2) : Next P p p' := by
  refine ⟨hnext.1,hnext.2.1,hnext.2.2.1,?_⟩
  intro z hz hpz hzp'
  have hzkey := hnext.2.2.2.2 z hz hpz hzp'
  have hznext : NextDifferent P z p' := by
    refine ⟨hz,hnext.2.1,hzp',by simpa only [hzkey] using hnext.2.2.2.1,?_⟩
    intro w hw hzw hwp'
    exact (hnext.2.2.2.2 w hw (lt_trans hpz hzw) hwp').trans hzkey.symm
  have hqz := hgap z p' hznext (congrArg f hzkey) hcolor.symm hpz
  have hp'q := hturn.2.1
  omega

theorem mixed_witness_window {P : Finset Point} {f : Int → Int} {p : Point}
    (h : MixedTurn P f p) :
    ∃ p' q, Next P p p' ∧ p.1 ≠ p'.1 ∧ f p.1 = f p'.1 ∧ q ∈ P ∧
      f q.1 ≠ f p.1 ∧ Turn p p' q ∧ Window P f p q := by
  obtain ⟨p',q,hnext,hcolor,hq,hqcolor,hturn,hgap⟩ := h
  refine ⟨p',q,mixed_pair_consecutive hnext hcolor hturn hgap,
    hnext.2.2.2.1,hcolor,hq,hqcolor,hturn,lt_trans hturn.1 hturn.2.1,?_⟩
  intro z hz hpz hzq
  obtain ⟨z',hznext,hzcolor,hz'color⟩ := hz
  have hqz := hgap z z' hznext hzcolor hz'color hpz
  omega

/-- First local change in a mixed-turn window is paid by an actual double switch. -/
theorem doubleSwitch_of_first_change {P : Finset Point} (hP : Instance P)
    (f : Int → Int) {p p' u : Point} (hnext : Next P p p')
    (hcolor : f p.1 = f p'.1) (hu : u ∈ P) (hucolor : f u.1 = f p.1)
    (hwin : Window P f p u) (hudiff : u.1 ≠ p'.1)
    (hfirst : ∀ z ∈ P, f z.1 = f p.1 → p.2 < z.2 → z.2 < u.2 → z.1 = p'.1) :
    DoubleSwitch P f u := by
  have hp'u : p'.2 < u.2 := by
    by_contra h
    by_cases he : u.2 = p'.2
    · have heq := hP u hu p' hnext.2.1 he
      exact hudiff (congrArg Prod.fst heq)
    · exact hnext.2.2.2 u hu hwin.1 (by omega)
  obtain ⟨v,hv⟩ := exists_previous hu ⟨p',hnext.2.1,hp'u⟩
  have hvlo := previous_ge hv hnext.2.1 hp'u
  have hpv : p.2 < v.2 := lt_of_lt_of_le hnext.2.2.1 hvlo
  have hvoutside : f v.1 ≠ f u.1 := by
    intro he
    have hvkey := hfirst v hv.1 (he.trans hucolor) hpv hv.2.2.1
    have hnd := next_different hv (by intro h; exact hudiff (h.symm.trans hvkey))
    exact hwin.2 v ⟨u,hnd,he.trans hucolor,hucolor⟩ hpv hv.2.2.1
  have hufiber : u ∈ fiber f (f u.1) P := Finset.mem_filter.mpr ⟨hu,rfl⟩
  have hp'fiber : p' ∈ fiber f (f u.1) P :=
    Finset.mem_filter.mpr ⟨hnext.2.1,hcolor.symm.trans hucolor.symm⟩
  obtain ⟨w,hw⟩ := exists_previous hufiber ⟨p',hp'fiber,hp'u⟩
  have hwlo := previous_ge hw hp'fiber hp'u
  have hpw : p.2 < w.2 := lt_of_lt_of_le hnext.2.2.1 hwlo
  have hwkey := hfirst w (Finset.mem_filter.mp hw.1).1
    ((Finset.mem_filter.mp hw.1).2.trans hucolor) hpw hw.2.2.1
  exact ⟨⟨mapPoint f v,next_project f hv,hvoutside⟩,
    ⟨w,hw,by intro he; exact hudiff (he.symm.trans hwkey)⟩⟩

/-- Construct the earliest double-switch donor if the window contains a
different local key. The window itself is retained for the injection proof. -/
theorem exists_doubleSwitch_donor {P : Finset Point} (hP : Instance P)
    (f : Int → Int) {p p' : Point} (hnext : Next P p p')
    (hcolor : f p.1 = f p'.1)
    (hex : ∃ u ∈ P, f u.1 = f p.1 ∧ Window P f p u ∧ u.1 ≠ p'.1) :
    ∃ u ∈ P, f u.1 = f p.1 ∧ Window P f p u ∧ DoubleSwitch P f u := by
  classical
  let candidates := P.filter (fun u => f u.1 = f p.1 ∧ Window P f p u ∧ u.1 ≠ p'.1)
  have hc : candidates.Nonempty := by
    obtain ⟨u,hu,hrest⟩ := hex
    exact ⟨u,Finset.mem_filter.mpr ⟨hu,hrest⟩⟩
  obtain ⟨u,hu,hmin⟩ := Finset.exists_min_image candidates Prod.snd hc
  obtain ⟨huP,hucolor,hwin,hudiff⟩ := Finset.mem_filter.mp hu
  refine ⟨u,huP,hucolor,hwin,doubleSwitch_of_first_change hP f hnext hcolor
    huP hucolor hwin hudiff ?_⟩
  intro z hz hzcolor hpz hzu
  by_contra hdiff
  have hzC : z ∈ candidates := Finset.mem_filter.mpr
    ⟨hz,hzcolor,window_prefix hwin hpz hzu.le,hdiff⟩
  exact (not_le_of_gt hzu) (hmin z hzC)

/-- Windows of two internal starts in the same segment cannot charge the
same later point. This is a global injection, not a bounded-overlap premise. -/
theorem window_donor_injective {P : Finset Point} (hP : Instance P)
    (f : Int → Int) {p r u : Point}
    (hp : InternalStart P f (f p.1) p) (hr : InternalStart P f (f r.1) r)
    (he : f p.1 = f r.1) (hpu : Window P f p u) (hru : Window P f r u) : p = r := by
  have hpP := hp.choose_spec.1.1
  have hrP := hr.choose_spec.1.1
  apply hP p hpP r hrP
  apply le_antisymm
  · by_contra hh
    exact hru.2 p (he ▸ hp) (by omega) hpu.1
  · by_contra hh
    exact hpu.2 r (he.symm ▸ hr) (by omega) hru.1

end TangoSquared.Paper20261030.Rectangles
