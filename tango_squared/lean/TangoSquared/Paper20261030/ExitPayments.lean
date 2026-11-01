import TangoSquared.Paper20261030.ExitReverseMixed

/-!
# Actual payments for depth exits

Each exit is paid by a broken local turn, a mixed turn in one of the two
time directions, or the final switch allowance of its segment.
-/

namespace TangoSquared.Paper20261030.Rectangles

def ExitGap (P : Finset Point) (f : Int → Int) (p r : Point) : Prop :=
  p.2 < r.2 ∧ ∀ e, DepthExit P f e → f e.1 = f p.1 →
    p.2 < e.2 → e.2 < r.2 → False

theorem exit_gap_until_next_internal_end {P : Finset Point} (hP : Instance P)
    (f : Int → Int) {s p q h h' : Point}
    (hsp : PreviousDifferent P s p) (hpq : Next P p q)
    (hcolor : f s.1 = f p.1) (hout : f q.1 ≠ f p.1)
    (hnext : NextInternal P f s h) (hnd : NextDifferent P h h') :
    ExitGap P f p h' := by
  have hsq := lt_trans hsp.2.2.1 hpq.2.2.1
  have hout' : f q.1 ≠ f s.1 := fun he => hout (he.trans hcolor)
  have hqh := internal_start_after_exit hP f hsp hpq hout' hnext.1 hnext.2.1
  refine ⟨lt_trans hpq.2.2.1 (lt_trans hqh hnd.2.2.1),?_⟩
  intro e he hecolor hpe heh'
  obtain ⟨v,w,hve,hvcolor,hew,hewcolor⟩ := he
  have heq := previousDifferent_before_internal_end hP f hpq.2.1 hsq hout' hnext hnd
    hve (hvcolor.trans (hecolor.trans hcolor.symm)) (hecolor.trans hcolor.symm) heh'
  have hqe := successor_le hpq hve.2.1 hpe
  omega

theorem exit_gap_prefix {P : Finset Point} {f : Int → Int} {p r z : Point}
    (h : ExitGap P f p r) (hpz : p.2 < z.2) (hzr : z.2 ≤ r.2) : ExitGap P f p z :=
  ⟨hpz,fun e he hc hpe hez => h.2 e he hc hpe (lt_of_lt_of_le hez hzr)⟩

theorem exit_gap_injective {P : Finset Point} (hP : Instance P)
    (f : Int → Int) {p p' r : Point}
    (hp : DepthExit P f p) (hp' : DepthExit P f p')
    (he : f p.1 = f p'.1) (hpr : ExitGap P f p r) (hp'r : ExitGap P f p' r) : p = p' := by
  obtain ⟨s,q,hsp,hrest⟩ := hp
  obtain ⟨s',q',hsp',hrest'⟩ := hp'
  apply hP p hsp.2.1 p' hsp'.2.1
  apply le_antisymm
  · by_contra hn
    exact hp'r.2 p ⟨s,q,hsp,hrest⟩ he (by omega) hpr.1
  · by_contra hn
    exact hpr.2 p' ⟨s',q',hsp',hrest'⟩ he.symm (by omega) hp'r.1

theorem exit_payment_with_next {P : Finset Point} (hP : Instance P)
    (f : Int → Int) (hf : Monotone f) {s p q h h' : Point}
    (hsp : PreviousDifferent P s p) (hpq : Next P p q)
    (hcolor : f s.1 = f p.1) (hout : f q.1 ≠ f p.1)
    (hnext : NextInternal P f s h) (hnd : NextDifferent P h h')
    (hhcolor : f h.1 = f s.1) (hh'color : f h'.1 = f s.1) :
    MixedTurn P f s ∨
      (∃ r ∈ P, f r.1 = f p.1 ∧ ExitGap P f p r ∧ BrokenTurn P f r) ∨
      MixedTurn (P.image reversePoint) f (reversePoint h') := by
  have hout' : f q.1 ≠ f s.1 := fun he => hout (he.trans hcolor)
  have hqh := internal_start_after_exit hP f hsp hpq hout' hnext.1 hnext.2.1
  have hgap := exit_gap_until_next_internal_end hP f hsp hpq hcolor hout hnext hnd
  by_cases ht : Turn s p q
  · exact Or.inl (mixed_of_turn_exit hP f hsp hpq ht hcolor hout')
  right
  have hsplocal := previousDifferent_fiber f hsp hcolor
  have hhlocal : h ∈ fiber f (f p.1) P :=
    Finset.mem_filter.mpr ⟨hnd.1,hhcolor.trans hcolor⟩
  have hh'local : h' ∈ fiber f (f p.1) P :=
    Finset.mem_filter.mpr ⟨hnd.2.1,hh'color.trans hcolor⟩
  have hph : p.2 ≤ h.2 := (lt_trans hpq.2.2.1 hqh).le
  have payTurn : (∃ r ∈ fiber f (f p.1) P,
      p.2 < r.2 ∧ r.2 ≤ h'.2 ∧ TurnPoint (fiber f (f p.1) P) r) →
      ∃ r ∈ P, f r.1 = f p.1 ∧ ExitGap P f p r ∧ BrokenTurn P f r := by
    rintro ⟨r,hr,hpr,hrh',htr⟩
    obtain ⟨hrP,hrcolor⟩ := Finset.mem_filter.mp hr
    have hlocal : LocalTurn P f r := by simpa only [LocalTurn,hrcolor] using htr
    exact ⟨r,hrP,hrcolor,exit_gap_prefix hgap hpr hrh',
      turn_before_next_internal_broken hP f hsp hpq hcolor hout hnext hnd
        hrcolor hpr hrh' hlocal⟩
  by_cases hup : s.1 < p.1
  · by_cases hdown : h'.1 < h.1
    · exact Or.inl (payTurn (turn_between_ascent_descent (instance_fiber hP f _)
        hsplocal hhlocal hh'local hph hnd.2.2.1 hup hdown))
    · have hqhkey : h.1 < q.1 := by
        have hqp : p.1 ≤ q.1 := by
          have hpqt := hpq.2.2.1
          have hspt := hsp.2.2.1
          simp only [Turn] at ht
          omega
        have hle := hf hqp
        by_contra hn
        have hle' := hf (show q.1 ≤ h.1 by omega)
        have hc := hhcolor.trans hcolor
        exact hout (by omega)
      have hhh' : h.1 < h'.1 := by have := hnd.2.2.2.1; omega
      exact Or.inr (mixed_reverse_at_next_internal hP f hpq.2.1
        (lt_trans hsp.2.2.1 hpq.2.2.1) hqh hout' hnext hnd hhcolor hh'color
        ⟨hqh,hnd.2.2.1,Or.inr ⟨hqhkey,hhh'⟩⟩)
  · have hdown : p.1 < s.1 := by have := hsp.2.2.2.1; omega
    by_cases hup' : h.1 < h'.1
    · exact Or.inl (payTurn (turn_between_descent_ascent (instance_fiber hP f _)
        hsplocal hhlocal hh'local hph hnd.2.2.1 hdown hup'))
    · have hqhkey : q.1 < h.1 := by
        have hqp : q.1 ≤ p.1 := by
          have hpqt := hpq.2.2.1
          have hspt := hsp.2.2.1
          simp only [Turn] at ht
          omega
        have hle := hf hqp
        by_contra hn
        have hle' := hf (show h.1 ≤ q.1 by omega)
        have hc := hhcolor.trans hcolor
        exact hout (by omega)
      have hhh' : h'.1 < h.1 := by have := hnd.2.2.2.1; omega
      exact Or.inr (mixed_reverse_at_next_internal hP f hpq.2.1
        (lt_trans hsp.2.2.1 hpq.2.2.1) hqh hout' hnext hnd hhcolor hh'color
        ⟨hqh,hnd.2.2.1,Or.inl ⟨hqhkey,hhh'⟩⟩)

end TangoSquared.Paper20261030.Rectangles
