import TangoSquared.Paper20261030.PotentialMagnitude

/-!
# Windows following a depth exit

An exit ends a same-segment run immediately before an outside access.
Its last preceding different key determines a unique internal start.
The next internal start in that segment lies beyond the outside access.
-/

namespace TangoSquared.Paper20261030.Rectangles

/-- Every previous-different pair supplies an actual internal start. -/
theorem previousDifferent_internalStart {P : Finset Point} (hP : Instance P)
    (f : Int → Int) {s p : Point} (hsp : PreviousDifferent P s p)
    (hcolor : f s.1 = f p.1) : InternalStart P f (f s.1) s := by
  obtain ⟨v,hsv⟩ := exists_successor hsp.1 ⟨p,hsp.2.1,hsp.2.2.1⟩
  have hvp := successor_le hsv hsp.2.1 hsp.2.2.1
  have hvkey : v.1 = p.1 := by
    by_cases he : v.2 = p.2
    · exact congrArg Prod.fst (hP v hsv.2.1 p hsp.2.1 he)
    · exact hsp.2.2.2.2 v hsv.2.1 hsv.2.2.1 (by omega)
  exact ⟨v,next_different hsv (by simpa only [hvkey] using hsp.2.2.2.1),
    rfl,by simpa only [hvkey] using hcolor.symm⟩

theorem internal_start_after_exit {P : Finset Point} (hP : Instance P)
    (f : Int → Int) {s p q h : Point} (hsp : PreviousDifferent P s p)
    (hpq : Next P p q) (hout : f q.1 ≠ f s.1)
    (hh : InternalStart P f (f s.1) h) (hsh : s.2 < h.2) : q.2 < h.2 := by
  obtain ⟨h',hnd,hcolor,h'color⟩ := hh
  by_contra hn
  have hhq : h.2 < q.2 := by
    by_cases he : h.2 = q.2
    · have heq := hP h hnd.1 q hpq.2.1 he
      exact (hout (heq ▸ hcolor)).elim
    · omega
  have hkey := turn_plateau hP hsp hpq hnd.1 hsh hhq
  have hnq : NextDifferent P h q := by
    refine ⟨hnd.1,hpq.2.1,hhq,?_,?_⟩
    · intro he
      exact hout (he ▸ hcolor)
    · intro z hz hhz hzq
      exact (turn_plateau hP hsp hpq hz (lt_trans hsh hhz) hzq).trans hkey.symm
  have heq := nextDifferent_unique hP hnd hnq
  exact hout (heq ▸ h'color)

theorem exit_source_unique {P : Finset Point} (hP : Instance P)
    (f : Int → Int) {s p q p' q' : Point}
    (hsp : PreviousDifferent P s p) (hpq : Next P p q)
    (hsp' : PreviousDifferent P s p') (hp'q' : Next P p' q')
    (hout : f p.1 ≠ f q.1) (hout' : f p'.1 ≠ f q'.1) : p = p' := by
  have hqq' := turn_source_injective hP hsp hpq hsp' hp'q'
    (fun he => hout (congrArg f he)) (fun he => hout' (congrArg f he))
  subst q'
  exact next_previous_unique hP hpq hp'q'

def NextInternal (P : Finset Point) (f : Int → Int) (s h : Point) : Prop :=
  InternalStart P f (f s.1) h ∧ s.2 < h.2 ∧
    ∀ z, InternalStart P f (f s.1) z → s.2 < z.2 → h.2 ≤ z.2

theorem next_internal_or_last (P : Finset Point) (f : Int → Int) (s : Point) :
    (∃ h, NextInternal P f s h) ∨
      (∀ h, InternalStart P f (f s.1) h → h.2 ≤ s.2) := by
  classical
  let S := P.filter (fun h => InternalStart P f (f s.1) h ∧ s.2 < h.2)
  by_cases hS : S.Nonempty
  · obtain ⟨h,hh,hmin⟩ := Finset.exists_min_image S Prod.snd hS
    obtain ⟨_,hhi,hsh⟩ := Finset.mem_filter.mp hh
    left
    exact ⟨h,hhi,hsh,fun z hz hsz => hmin z
      (Finset.mem_filter.mpr ⟨hz.choose_spec.1.1,hz,hsz⟩)⟩
  · right
    intro h hh
    by_contra hn
    exact hS ⟨h,Finset.mem_filter.mpr ⟨hh.choose_spec.1.1,hh,by omega⟩⟩

/-- Before the next internal pair ends, every local turn is broken. -/
theorem turn_before_next_internal_broken {P : Finset Point} (hP : Instance P)
    (f : Int → Int) {s p q h h' r : Point}
    (hsp : PreviousDifferent P s p) (hpq : Next P p q)
    (hcolor : f s.1 = f p.1) (hout : f q.1 ≠ f p.1)
    (hnext : NextInternal P f s h) (hnd : NextDifferent P h h')
    (hrcolor : f r.1 = f p.1) (hpr : p.2 < r.2) (hrh' : r.2 ≤ h'.2)
    (hlocal : LocalTurn P f r) : BrokenTurn P f r := by
  refine ⟨hlocal,?_⟩
  rintro ⟨a,b,hab,hbr,ht,hacolor,hbcolor⟩
  have haq : q.2 ≤ a.2 := by
    have hqr := successor_le hpq hbr.2.1 hpr
    by_contra hn
    have hqrlt : q.2 < r.2 := by
      by_cases he : q.2 = r.2
      · have heq := hP q hpq.2.1 r hbr.2.1 he
        exact (hout ((congrArg f (congrArg Prod.fst heq)).trans hrcolor)).elim
      · omega
    have hqkey := turn_plateau hP hab hbr hpq.2.1 (by omega) hqrlt
    exact hout ((congrArg f hqkey).trans (hbcolor.trans hrcolor))
  have hsa : s.2 < a.2 := by have := hsp.2.2.1; have := hpq.2.2.1; omega
  have haInt := previousDifferent_internalStart hP f hab (hacolor.trans hbcolor.symm)
  have hac : f a.1 = f s.1 := hacolor.trans (hrcolor.trans hcolor.symm)
  have hha := hnext.2.2 a (hac ▸ haInt) hsa
  have hah' : a.2 < h'.2 := by have := hab.2.2.1; have := hbr.2.2.1; omega
  have hakey : a.1 = h.1 := by
    by_cases he : a.2 = h.2
    · exact congrArg Prod.fst (hP a hab.1 h hnd.1 he)
    · exact hnd.2.2.2.2 a hab.1 (by omega) hah'
  have hbh' : b.2 < h'.2 := by have := hbr.2.2.1; omega
  have hbkey := hnd.2.2.2.2 b hab.2.1
    (by have := hab.2.2.1; omega) hbh'
  exact hab.2.2.2.1 (hakey.trans hbkey.symm)

end TangoSquared.Paper20261030.Rectangles
