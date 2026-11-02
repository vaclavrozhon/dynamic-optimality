import ChaCha.Paper20261030.ExitPayments

/-!
# Injective accounting of all depth exits

The four payment classes are disjoint. Actual chronological windows prove
that no broken turn or reversed mixed turn is paid twice; the source
uniqueness lemma treats forward mixed turns. A segment has at most one
final exit.
-/

namespace ChaCha.Paper20261030.Rectangles

open scoped BigOperators
attribute [local instance] Classical.propDecidable

def ExitSource (P : Finset Point) (f : Int → Int) (p s : Point) : Prop :=
  ∃ q, PreviousDifferent P s p ∧ f s.1 = f p.1 ∧ Next P p q ∧ f p.1 ≠ f q.1

def FinalExit (P : Finset Point) (f : Int → Int) (p : Point) : Prop :=
  ∃ s, ExitSource P f p s ∧ ∀ h, InternalStart P f (f s.1) h → h.2 ≤ s.2

theorem exitSource_depthExit {P : Finset Point} {f : Int → Int} {p s : Point}
    (h : ExitSource P f p s) : DepthExit P f p := by
  obtain ⟨q,hrest⟩ := h
  exact ⟨s,q,hrest⟩

theorem finalExit_unique {P : Finset Point} (hP : Instance P) (f : Int → Int)
    {p p' : Point} (hp : FinalExit P f p) (hp' : FinalExit P f p')
    (he : f p.1 = f p'.1) : p = p' := by
  obtain ⟨s,⟨q,hsp,hcolor,hpq,hout⟩,hlast⟩ := hp
  obtain ⟨s',⟨q',hsp',hcolor',hp'q',hout'⟩,hlast'⟩ := hp'
  have hsInt := previousDifferent_internalStart hP f hsp hcolor
  have hs'Int := previousDifferent_internalStart hP f hsp' hcolor'
  have hss' : f s.1 = f s'.1 := hcolor.trans (he.trans hcolor'.symm)
  have hle := hlast s' (hss'.symm ▸ hs'Int)
  have hle' := hlast' s (hss' ▸ hsInt)
  have heq := hP s hsp.1 s' hsp'.1 (by omega)
  subst s'
  exact exit_source_unique hP f hsp hpq hsp' hp'q' hout hout'

theorem switchCount_positive_of_previousDifferent {P : Finset Point} (hP : Instance P)
    {p q : Point} (hpq : PreviousDifferent P p q) : 0 < switchCount P := by
  obtain ⟨s,hps⟩ := exists_successor hpq.1 ⟨q,hpq.2.1,hpq.2.2.1⟩
  have hsq := successor_le hps hpq.2.1 hpq.2.2.1
  have hskey : s.1 = q.1 := by
    by_cases he : s.2 = q.2
    · exact congrArg Prod.fst (hP s hps.2.1 q hpq.2.1 he)
    · exact hpq.2.2.2.2 s hps.2.1 hps.2.2.1 (by omega)
  have hsw : SwitchPoint P s := ⟨p,hps,by simpa only [hskey] using hpq.2.2.2.1⟩
  rw [switchCount,eventCount_eq_card]
  exact Finset.card_pos.mpr ⟨s,Finset.mem_filter.mpr ⟨hps.2.1,hsw⟩⟩

theorem exit_fiber_switch_positive {P : Finset Point} (hP : Instance P)
    (f : Int → Int) {p : Point} (hp : DepthExit P f p) :
    0 < switchCount (fiber f (f p.1) P) := by
  obtain ⟨s,q,hsp,hcolor,_⟩ := hp
  exact switchCount_positive_of_previousDifferent (instance_fiber hP f _)
    (previousDifferent_fiber f hsp hcolor)

abbrev ExitPayment := Int ⊕ (Point ⊕ (Point ⊕ Point))

def ExitPaymentSpec (P : Finset Point) (f : Int → Int) (p : Point) : ExitPayment → Prop
  | .inl i => i = f p.1 ∧ FinalExit P f p
  | .inr (.inl r) => BrokenTurn P f r ∧ f r.1 = f p.1 ∧ ExitGap P f p r
  | .inr (.inr (.inl s)) => MixedTurn P f s ∧ ExitSource P f p s
  | .inr (.inr (.inr r)) => MixedTurn (P.image reversePoint) f r ∧
      f r.1 = f p.1 ∧ ExitGap P f p (reversePoint r)

theorem exists_exitPayment {P : Finset Point} (hP : Instance P)
    (f : Int → Int) (hf : Monotone f) {p : Point} (hp : DepthExit P f p) :
    ∃ a, ExitPaymentSpec P f p a := by
  obtain ⟨s,q,hsp,hcolor,hpq,hout⟩ := hp
  rcases next_internal_or_last P f s with ⟨h,hnext⟩ | hlast
  · obtain ⟨h',hnd,hhcolor,hh'color⟩ := hnext.1
    rcases exit_payment_with_next hP f hf hsp hpq hcolor (Ne.symm hout)
        hnext hnd hhcolor hh'color with hm | ⟨r,hr,hc,hgap,hbroken⟩ | hm
    · exact ⟨.inr (.inr (.inl s)),hm,q,hsp,hcolor,hpq,hout⟩
    · exact ⟨.inr (.inl r),hbroken,hc,hgap⟩
    · refine ⟨.inr (.inr (.inr (reversePoint h'))),hm,hh'color.trans hcolor,?_⟩
      rw [reversePoint_involutive h']
      exact exit_gap_until_next_internal_end hP f hsp hpq hcolor
        (Ne.symm hout) hnext hnd
  · exact ⟨.inl (f p.1),rfl,s,⟨q,hsp,hcolor,hpq,hout⟩,hlast⟩

theorem exitPayment_unique {P : Finset Point} (hP : Instance P)
    (f : Int → Int) {p p' : Point} (hp : DepthExit P f p) (hp' : DepthExit P f p')
    {a : ExitPayment} (ha : ExitPaymentSpec P f p a)
    (ha' : ExitPaymentSpec P f p' a) : p = p' := by
  rcases a with i | a
  · exact finalExit_unique hP f ha.2 ha'.2 (ha.1.symm.trans ha'.1)
  · rcases a with r | a
    · exact exit_gap_injective hP f hp hp' (ha.2.1.symm.trans ha'.2.1) ha.2.2 ha'.2.2
    · rcases a with s | r
      · obtain ⟨_,q,hsp,_,hpq,hout⟩ := ha
        obtain ⟨_,q',hsp',_,hp'q',hout'⟩ := ha'
        exact exit_source_unique hP f hsp hpq hsp' hp'q' hout hout'
      · exact exit_gap_injective hP f hp hp' (ha.2.1.symm.trans ha'.2.1) ha.2.2 ha'.2.2

noncomputable def exitPayments (P : Finset Point) (f : Int → Int) (I : Finset Int) :
    Finset ExitPayment :=
  (I.filter (fun i => 0 < switchCount (fiber f i P))).disjSum
    ((P.filter (BrokenTurn P f)).disjSum ((P.filter (MixedTurn P f)).disjSum
      ((P.image reversePoint).filter (MixedTurn (P.image reversePoint) f))))

theorem exitPayment_mem {P : Finset Point} (hP : Instance P)
    (f : Int → Int) (I : Finset Int) (hI : ∀ p ∈ P, f p.1 ∈ I)
    {p : Point} (hpP : p ∈ P) (hp : DepthExit P f p) {a : ExitPayment}
    (ha : ExitPaymentSpec P f p a) : a ∈ exitPayments P f I := by
  rcases a with i | a
  · apply Finset.inl_mem_disjSum.mpr
    exact Finset.mem_filter.mpr ⟨ha.1 ▸ hI p hpP,ha.1 ▸ exit_fiber_switch_positive hP f hp⟩
  · apply Finset.inr_mem_disjSum.mpr
    rcases a with r | a
    · have hrP : r ∈ P := by
        obtain ⟨u,v,hvr,_⟩ := ha.1.1
        exact (Finset.mem_filter.mp hvr.2.1).1
      exact Finset.inl_mem_disjSum.mpr (Finset.mem_filter.mpr ⟨hrP,ha.1⟩)
    · apply Finset.inr_mem_disjSum.mpr
      rcases a with s | r
      · exact Finset.inl_mem_disjSum.mpr (Finset.mem_filter.mpr
          ⟨(mixed_internalStart ha.1).choose_spec.1.1,ha.1⟩)
      · exact Finset.inr_mem_disjSum.mpr (Finset.mem_filter.mpr
          ⟨(mixed_internalStart ha.1).choose_spec.1.1,ha.1⟩)

theorem depth_exit_bound {P : Finset Point} (hP : Instance P)
    (f : Int → Int) (hf : Monotone f) (I : Finset Int) (hI : ∀ p ∈ P, f p.1 ∈ I) :
    depthAlternations P f ≤ (∑ i ∈ I, switchIndicator (fiber f i P)) +
      eventCount P (BrokenTurn P f) + mixedTurns P f + mixedTurns (P.image reversePoint) f := by
  classical
  let E := P.filter (DepthExit P f)
  have hex : ∀ p : E, ∃ a, ExitPaymentSpec P f p.val a := by
    intro p
    exact exists_exitPayment hP f hf (Finset.mem_filter.mp p.property).2
  choose pay hpay using hex
  let assign : E → exitPayments P f I := fun p => ⟨pay p,
    exitPayment_mem hP f I hI (Finset.mem_filter.mp p.property).1
      (Finset.mem_filter.mp p.property).2 (hpay p)⟩
  have hinj : Function.Injective assign := by
    intro p p' he
    apply Subtype.ext
    have heq : pay p = pay p' := congrArg Subtype.val he
    exact exitPayment_unique hP f (Finset.mem_filter.mp p.property).2
      (Finset.mem_filter.mp p'.property).2 (hpay p) (heq.symm ▸ hpay p')
  have hc := Finset.card_le_card_of_injective hinj
  have hind : (I.filter (fun i => 0 < switchCount (fiber f i P))).card =
      ∑ i ∈ I, switchIndicator (fiber f i P) := by
    simp only [Finset.card_eq_sum_ones,Finset.sum_filter,switchIndicator]
  simpa only [E,exitPayments,depthAlternations,mixedTurns,eventCount_eq_card,
    Finset.card_disjSum,hind,Nat.add_assoc] using hc

end ChaCha.Paper20261030.Rectangles
