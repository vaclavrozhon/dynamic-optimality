import TangoSquared.Paper20261030.ReverseAccounting

/-!
# Distinct-key chronology and the mixed-turn classification

Previous/next different points are unique on an instance. A global turn
whose first edge stays in one segment and whose second edge leaves it
produces a mixed-turn witness at its first point. The proof includes any
repeated middle key, using the first access of that constant-key run.
-/

namespace TangoSquared.Paper20261030.Rectangles

theorem nextDifferent_unique {P : Finset Point} (hP : Instance P)
    {p q r : Point} (hq : NextDifferent P p q) (hr : NextDifferent P p r) : q = r := by
  apply hP q hq.2.1 r hr.2.1
  apply le_antisymm
  · by_contra hh
    have he := hq.2.2.2.2 r hr.2.1 hr.2.2.1 (by omega)
    exact hr.2.2.2.1 he.symm
  · by_contra hh
    have he := hr.2.2.2.2 q hq.2.1 hq.2.2.1 (by omega)
    exact hq.2.2.2.1 he.symm

theorem previousDifferent_unique {P : Finset Point} (hP : Instance P)
    {p r q : Point} (hp : PreviousDifferent P p q) (hr : PreviousDifferent P r q) : p = r := by
  apply hP p hp.1 r hr.1
  apply le_antisymm
  · by_contra hh
    have he := hr.2.2.2.2 p hp.1 (by omega) hp.2.2.1
    exact hp.2.2.2.1 he
  · by_contra hh
    have he := hp.2.2.2.2 r hr.1 (by omega) hr.2.2.1
    exact hr.2.2.2.1 he

theorem exists_successor {P : Finset Point} {p : Point} (hp : p ∈ P)
    (hafter : ∃ q ∈ P, p.2 < q.2) : ∃ q, Next P p q := by
  classical
  let after := P.filter (fun q => p.2 < q.2)
  have ha : after.Nonempty := by
    obtain ⟨q,hq,ht⟩ := hafter
    exact ⟨q,Finset.mem_filter.mpr ⟨hq,ht⟩⟩
  obtain ⟨q,hq,hmin⟩ := Finset.exists_min_image after Prod.snd ha
  obtain ⟨hqP,hpq⟩ := Finset.mem_filter.mp hq
  refine ⟨q,hp,hqP,hpq,?_⟩
  intro z hz hpz hzq
  exact (not_le_of_gt hzq) (hmin z (Finset.mem_filter.mpr ⟨hz,hpz⟩))

theorem successor_le {P : Finset Point} {p q z : Point}
    (h : Next P p q) (hz : z ∈ P) (hpz : p.2 < z.2) : q.2 ≤ z.2 := by
  by_contra hh
  exact h.2.2.2 z hz hpz (by omega)

theorem turn_plateau {P : Finset Point} (hP : Instance P) {p q r : Point}
    (hpq : PreviousDifferent P p q) (hqr : Next P q r)
    {z : Point} (hz : z ∈ P) (hpz : p.2 < z.2) (hzr : z.2 < r.2) : z.1 = q.1 := by
  by_cases he : z.2 = q.2
  · exact congrArg Prod.fst (hP z hz q hpq.2.1 he)
  by_cases hlt : z.2 < q.2
  · exact hpq.2.2.2.2 z hz hpz hlt
  · exact (hqr.2.2.2 z hz (by omega) hzr).elim

theorem nextDifferent_reverse {P : Finset Point} {p q : Point}
    (h : NextDifferent P p q) :
    PreviousDifferent (P.image reversePoint) (reversePoint q) (reversePoint p) := by
  refine ⟨Finset.mem_image.mpr ⟨q,h.2.1,rfl⟩,
    Finset.mem_image.mpr ⟨p,h.1,rfl⟩,?_,Ne.symm h.2.2.2.1,?_⟩
  · dsimp [reversePoint]
    have := h.2.2.1
    omega
  · intro z hz hqz hzp
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hz
    apply h.2.2.2.2 a ha
    · dsimp [reversePoint] at hzp
      omega
    · dsimp [reversePoint] at hqz
      omega

theorem turn_reverse {p q r : Point} (h : Turn p q r) :
    Turn (reversePoint r) (reversePoint q) (reversePoint p) := by
  simp only [Turn,reversePoint] at h ⊢
  omega

/-- The first mixed case in the global-turn classification. -/
theorem mixed_of_turn_exit {P : Finset Point} (hP : Instance P)
    (f : Int → Int) {p q r : Point}
    (hpq : PreviousDifferent P p q) (hqr : Next P q r) (hturn : Turn p q r)
    (hcolor : f p.1 = f q.1) (hout : f r.1 ≠ f p.1) : MixedTurn P f p := by
  obtain ⟨s,hps⟩ := exists_successor hpq.1 ⟨q,hpq.2.1,hpq.2.2.1⟩
  have hsq := successor_le hps hpq.2.1 hpq.2.2.1
  have hsr : s.2 < r.2 := lt_of_le_of_lt hsq hqr.2.2.1
  have hskey := turn_plateau hP hpq hqr hps.2.1 hps.2.2.1 hsr
  have hpnd : NextDifferent P p s := next_different hps
    (by simpa only [hskey] using hpq.2.2.2.1)
  have hpsturn : Turn p s r := by
    refine ⟨hps.2.2.1,hsr,?_⟩
    simpa only [hskey] using hturn.2.2
  refine ⟨s,r,hpnd,by simpa only [hskey] using hcolor,hqr.2.1,hout,hpsturn,?_⟩
  intro a b hab hacolor hbcolor hpa
  by_contra hh
  have har : a.2 < r.2 := by
    by_cases he : a.2 = r.2
    · have harEq := hP a hab.1 r hqr.2.1 he
      exact (hout (harEq ▸ hacolor)).elim
    · omega
  have hakey := turn_plateau hP hpq hqr hab.1 hpa har
  have hneq : a.1 ≠ r.1 := by
    intro he
    exact hout (he ▸ hacolor)
  have hand : NextDifferent P a r := by
    refine ⟨hab.1,hqr.2.1,har,hneq,?_⟩
    intro z hz haz hzr
    exact (turn_plateau hP hpq hqr hz (lt_trans hpa haz) hzr).trans hakey.symm
  have hbr := nextDifferent_unique hP hab hand
  exact hout (hbr ▸ hbcolor)

/-- The other mixed case is counted in the reversed instance. -/
theorem reversed_mixed_of_turn_entry {P : Finset Point} (hP : Instance P)
    (f : Int → Int) {p q r : Point}
    (hpq : PreviousDifferent P p q) (hqr : Next P q r) (hturn : Turn p q r)
    (hcolor : f q.1 = f r.1) (hout : f p.1 ≠ f r.1) :
    MixedTurn (P.image reversePoint) f (reversePoint r) := by
  obtain ⟨s,hps⟩ := exists_successor hpq.1 ⟨q,hpq.2.1,hpq.2.2.1⟩
  have hsq := successor_le hps hpq.2.1 hpq.2.2.1
  have hsr : s.2 < r.2 := lt_of_le_of_lt hsq hqr.2.2.1
  have hskey := turn_plateau hP hpq hqr hps.2.1 hps.2.2.1 hsr
  have hnd : NextDifferent P s r := by
    refine ⟨hps.2.1,hqr.2.1,hsr,?_,?_⟩
    · have := hturn.2.2
      rw [hskey]
      omega
    · intro z hz hsz hzr
      exact (turn_plateau hP hpq hqr hz (lt_trans hps.2.2.1 hsz) hzr).trans hskey.symm
  have hpsr : Turn p s r := ⟨hps.2.2.1,hsr,by simpa only [hskey] using hturn.2.2⟩
  apply mixed_of_turn_exit (instance_reverse hP) f (nextDifferent_reverse hnd)
    (next_reverse hps) (turn_reverse hpsr)
  · change f r.1 = f s.1
    rw [hskey]
    exact hcolor.symm
  · exact hout

/-- Distinct global turns cannot have the same first defining point. -/
theorem turn_source_injective {P : Finset Point} (hP : Instance P)
    {p q r q' r' : Point} (hpq : PreviousDifferent P p q) (hqr : Next P q r)
    (hpq' : PreviousDifferent P p q') (hq'r' : Next P q' r')
    (hneq : q.1 ≠ r.1) (hneq' : q'.1 ≠ r'.1) : r = r' := by
  have hqq' : q = q' := by
    apply hP q hpq.2.1 q' hpq'.2.1
    apply le_antisymm
    · by_contra hh
      have hqkey := hpq.2.2.2.2 q' hpq'.2.1 hpq'.2.2.1 (by omega)
      have hbound : r'.2 ≤ q.2 := successor_le hq'r' hpq.2.1 (by omega)
      by_cases he : r'.2 = q.2
      · have hr'q := hP r' hq'r'.2.1 q hpq.2.1 he
        exact hneq' (hqkey.trans (congrArg Prod.fst hr'q).symm)
      · have hr'key := hpq.2.2.2.2 r' hq'r'.2.1
          (lt_trans hpq'.2.2.1 hq'r'.2.2.1) (by omega)
        exact hneq' (hqkey.trans hr'key.symm)
    · by_contra hh
      have hqkey := hpq'.2.2.2.2 q hpq.2.1 hpq.2.2.1 (by omega)
      have hbound : r.2 ≤ q'.2 := successor_le hqr hpq'.2.1 (by omega)
      by_cases he : r.2 = q'.2
      · have hrq' := hP r hqr.2.1 q' hpq'.2.1 he
        exact hneq (hqkey.trans (congrArg Prod.fst hrq').symm)
      · have hrkey := hpq'.2.2.2.2 r hqr.2.1
          (lt_trans hpq.2.2.1 hqr.2.2.1) (by omega)
        exact hneq (hqkey.trans hrkey.symm)
  subst q'
  exact next_successor_unique hP hqr hq'r'

end TangoSquared.Paper20261030.Rectangles
