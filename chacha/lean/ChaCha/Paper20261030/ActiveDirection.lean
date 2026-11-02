import ChaCha.Paper20261030.SplitDecomposition

/-!
# The chronological active-direction state machine

`ActiveDown` reads only the most recent earlier distinct key. Equal-key
accesses preserve the state; a different key sets DOWN precisely when the
old and new keys belong to one segment. The counted DOWN-to-UP transitions
are proved equal to `depthAlternations`.
-/

namespace ChaCha.Paper20261030.Rectangles

attribute [local instance] Classical.propDecidable

def ActiveDown (P : Finset Point) (f : Int → Int) (p : Point) : Prop :=
  ∃ s, PreviousDifferent P s p ∧ f s.1 = f p.1

def DownUpAt (P : Finset Point) (f : Int → Int) (q : Point) : Prop :=
  ∃ p, Next P p q ∧ ActiveDown P f p ∧ ¬ ActiveDown P f q

theorem previousDifferent_across_repeat {P : Finset Point} (hP : Instance P)
    {p q s : Point} (hpq : Next P p q) (hk : p.1 = q.1) :
    PreviousDifferent P s q ↔ PreviousDifferent P s p := by
  constructor
  · intro hsq
    have hsp : s.2 < p.2 := by
      have hle := previous_ge hpq hsq.1 hsq.2.2.1
      by_cases he : s.2 = p.2
      · have heq := hP s hsq.1 p hpq.1 he
        exact (hsq.2.2.2.1 ((congrArg Prod.fst heq).trans hk)).elim
      · omega
    refine ⟨hsq.1,hpq.1,hsp,by simpa only [hk] using hsq.2.2.2.1,?_⟩
    intro z hz hsz hzp
    exact (hsq.2.2.2.2 z hz hsz (lt_trans hzp hpq.2.2.1)).trans hk.symm
  · intro hsp
    refine ⟨hsp.1,hpq.2.1,lt_trans hsp.2.2.1 hpq.2.2.1,
      by simpa only [hk] using hsp.2.2.2.1,?_⟩
    intro z hz hsz hzq
    by_cases he : z.2 = p.2
    · exact (congrArg Prod.fst (hP z hz p hpq.1 he)).trans hk
    by_cases hzp : z.2 < p.2
    · exact (hsp.2.2.2.2 z hz hsz hzp).trans hk
    · exact (hpq.2.2.2 z hz (by omega) hzq).elim

theorem activeDown_repeat {P : Finset Point} (hP : Instance P) (f : Int → Int)
    {p q : Point} (hpq : Next P p q) (hk : p.1 = q.1) :
    ActiveDown P f q ↔ ActiveDown P f p := by
  simp only [ActiveDown]
  constructor <;> rintro ⟨s,hs,hc⟩
  · exact ⟨s,(previousDifferent_across_repeat hP hpq hk).mp hs,by simpa only [hk] using hc⟩
  · exact ⟨s,(previousDifferent_across_repeat hP hpq hk).mpr hs,by simpa only [hk] using hc⟩

theorem activeDown_change {P : Finset Point} (hP : Instance P) (f : Int → Int)
    {p q : Point} (hpq : Next P p q) (hk : p.1 ≠ q.1) :
    ActiveDown P f q ↔ f p.1 = f q.1 := by
  have hpd : PreviousDifferent P p q :=
    ⟨hpq.1,hpq.2.1,hpq.2.2.1,hk,fun z hz hpz hzq => (hpq.2.2.2 z hz hpz hzq).elim⟩
  constructor
  · rintro ⟨s,hs,hc⟩
    exact previousDifferent_unique hP hs hpd ▸ hc
  · exact fun hc => ⟨p,hpd,hc⟩

theorem activeDown_initial {P : Finset Point} (f : Int → Int) {p : Point}
    (hfirst : ∀ s ∈ P, p.2 ≤ s.2) : ¬ ActiveDown P f p := by
  rintro ⟨s,hs,hc⟩
  have := hfirst s hs.1
  have := hs.2.2.1
  omega

theorem downUp_iff_exit_edge {P : Finset Point} (hP : Instance P) (f : Int → Int)
    {p q : Point} (hpq : Next P p q) :
    (ActiveDown P f p ∧ ¬ ActiveDown P f q) ↔
      (ActiveDown P f p ∧ f p.1 ≠ f q.1) := by
  by_cases hk : p.1 = q.1
  · rw [activeDown_repeat hP f hpq hk]
    simp only [hk,ne_eq,not_true_eq_false,and_false,and_not_self]
  · rw [activeDown_change hP f hpq hk]

theorem downUp_of_exit {P : Finset Point} (hP : Instance P) (f : Int → Int)
    {p : Point} (hp : DepthExit P f p) : ∃ q, Next P p q ∧ DownUpAt P f q := by
  obtain ⟨s,q,hsp,hc,hpq,hout⟩ := hp
  have hstate := (downUp_iff_exit_edge hP f hpq).mpr ⟨⟨s,hsp,hc⟩,hout⟩
  exact ⟨q,hpq,p,hpq,hstate⟩

theorem exit_of_downUp {P : Finset Point} (hP : Instance P) (f : Int → Int)
    {q : Point} (hq : DownUpAt P f q) : ∃ p, Next P p q ∧ DepthExit P f p := by
  obtain ⟨p,hpq,hstate⟩ := hq
  obtain ⟨⟨s,hsp,hc⟩,hout⟩ := (downUp_iff_exit_edge hP f hpq).mp hstate
  exact ⟨p,hpq,s,q,hsp,hc,hpq,hout⟩

/-- Reusable finite injection principle; callers supply proved event relations. -/
theorem eventCount_le_of_relation {P Q : Finset Point} {A B : Point → Prop}
    (R : Point → Point → Prop)
    (hex : ∀ p ∈ P, A p → ∃ q ∈ Q, B q ∧ R p q)
    (hinj : ∀ p ∈ P, ∀ p' ∈ P, ∀ q, R p q → R p' q → p = p') :
    eventCount P A ≤ eventCount Q B := by
  let S := P.filter A
  let T := Q.filter B
  have hchoice : ∀ p : S, ∃ q : T, R p.val q.val := by
    intro p
    obtain ⟨q,hq,hB,hR⟩ := hex p.val (Finset.mem_filter.mp p.property).1
      (Finset.mem_filter.mp p.property).2
    exact ⟨⟨q,Finset.mem_filter.mpr ⟨hq,hB⟩⟩,hR⟩
  choose assign hass using hchoice
  have hi : Function.Injective assign := by
    intro p p' he
    apply Subtype.ext
    exact hinj p.val (Finset.mem_filter.mp p.property).1 p'.val
      (Finset.mem_filter.mp p'.property).1 (assign p).val (hass p) (he ▸ hass p')
  simpa only [S,T,eventCount_eq_card] using Finset.card_le_card_of_injective hi

theorem depthAlternations_eq_downUp {P : Finset Point} (hP : Instance P) (f : Int → Int) :
    depthAlternations P f = eventCount P (DownUpAt P f) := by
  apply Nat.le_antisymm
  · apply eventCount_le_of_relation (Next P)
    · intro p hp he
      obtain ⟨q,hpq,hq⟩ := downUp_of_exit hP f he
      exact ⟨q,hpq.2.1,hq,hpq⟩
    · intro p hp p' hp' q hpq hp'q
      exact next_previous_unique hP hpq hp'q
  · apply eventCount_le_of_relation (fun q p => Next P p q)
    · intro q hq he
      obtain ⟨p,hpq,hp⟩ := exit_of_downUp hP f he
      exact ⟨p,hpq.1,hp,hpq⟩
    · intro q hq q' hq' p hpq hpq'
      exact next_successor_unique hP hpq hpq'

end ChaCha.Paper20261030.Rectangles
