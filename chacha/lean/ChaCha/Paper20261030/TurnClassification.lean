import ChaCha.Paper20261030.DistinctChronology

/-!
# Classification and payment of global turns

An `UnbrokenTurn` is a local turn whose defining triple already occurs
globally without an intervening outside access. The remaining local turns
are reserved for the depth-alternation charge. Global turns inject into
contracted turns, unbroken local turns, or mixed turns in either time
direction. Every count refers to actual input points.
-/

namespace ChaCha.Paper20261030.Rectangles

attribute [local instance] Classical.propDecidable

def LocalTurn (P : Finset Point) (f : Int → Int) (r : Point) : Prop :=
  TurnPoint (fiber f (f r.1) P) r

def UnbrokenTurn (P : Finset Point) (f : Int → Int) (r : Point) : Prop :=
  ∃ p q, PreviousDifferent P p q ∧ Next P q r ∧ Turn p q r ∧
    f p.1 = f r.1 ∧ f q.1 = f r.1

def BrokenTurn (P : Finset Point) (f : Int → Int) (r : Point) : Prop :=
  LocalTurn P f r ∧ ¬ UnbrokenTurn P f r

theorem previousDifferent_fiber (f : Int → Int) {P : Finset Point} {p q : Point}
    (h : PreviousDifferent P p q) (he : f p.1 = f q.1) :
    PreviousDifferent (fiber f (f q.1) P) p q := by
  refine ⟨Finset.mem_filter.mpr ⟨h.1,he⟩,
    Finset.mem_filter.mpr ⟨h.2.1,rfl⟩,h.2.2.1,h.2.2.2.1,?_⟩
  intro z hz hpz hzq
  exact h.2.2.2.2 z (Finset.mem_filter.mp hz).1 hpz hzq

theorem unbroken_local {P : Finset Point} {f : Int → Int} {r : Point}
    (h : UnbrokenTurn P f r) : LocalTurn P f r := by
  obtain ⟨p,q,hpq,hqr,hturn,hpcolor,hqcolor⟩ := h
  refine ⟨p,q,next_fiber f hqr hqcolor,?_,hturn⟩
  have hpf := previousDifferent_fiber f hpq (hpcolor.trans hqcolor.symm)
  simpa only [hqcolor] using hpf

theorem previousDifferent_project (f : Int → Int) {P : Finset Point} {p q : Point}
    (h : PreviousDifferent P p q) (hne : f p.1 ≠ f q.1) :
    PreviousDifferent (project f P) (mapPoint f p) (mapPoint f q) := by
  refine ⟨Finset.mem_image.mpr ⟨p,h.1,rfl⟩,
    Finset.mem_image.mpr ⟨q,h.2.1,rfl⟩,h.2.2.1,hne,?_⟩
  intro z hz hpz hzq
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hz
  exact congrArg f (h.2.2.2.2 a ha hpz hzq)

theorem turn_project (f : Int → Int) (hf : Monotone f) {p q r : Point}
    (h : Turn p q r) (hpq : f p.1 ≠ f q.1) (hqr : f q.1 ≠ f r.1) :
    Turn (mapPoint f p) (mapPoint f q) (mapPoint f r) := by
  refine ⟨h.1,h.2.1,?_⟩
  rcases h.2.2 with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
  · have hp := hf h₁.le
    have hr := hf h₂.le
    left
    dsimp [mapPoint]
    omega
  · have hp := hf h₁.le
    have hr := hf h₂.le
    right
    dsimp [mapPoint]
    omega

abbrev TurnPayment := Point ⊕ (Point ⊕ (Point ⊕ Point))

def TurnPaymentSpec (P : Finset Point) (f : Int → Int) (r : Point) : TurnPayment → Prop
  | .inl a => a = mapPoint f r ∧ TurnPoint (project f P) a
  | .inr (.inl a) => a = r ∧ UnbrokenTurn P f a
  | .inr (.inr (.inl a)) => MixedTurn P f a ∧
      ∃ q, PreviousDifferent P a q ∧ Next P q r ∧ Turn a q r
  | .inr (.inr (.inr a)) => a = reversePoint r ∧ MixedTurn (P.image reversePoint) f a

theorem global_turn_payment {P : Finset Point} (hP : Instance P)
    (f : Int → Int) (hf : Monotone f) {r : Point} (hr : TurnPoint P r) :
    ∃ a, TurnPaymentSpec P f r a := by
  obtain ⟨p,q,hqr,hpq,hturn⟩ := hr
  by_cases hpqcolor : f p.1 = f q.1
  · by_cases hqrcolor : f q.1 = f r.1
    · exact ⟨.inr (.inl r),rfl,p,q,hpq,hqr,hturn,hpqcolor.trans hqrcolor,hqrcolor⟩
    · have hout : f r.1 ≠ f p.1 := by omega
      exact ⟨.inr (.inr (.inl p)),
        mixed_of_turn_exit hP f hpq hqr hturn hpqcolor hout,q,hpq,hqr,hturn⟩
  · by_cases hqrcolor : f q.1 = f r.1
    · have hout : f p.1 ≠ f r.1 := by omega
      exact ⟨.inr (.inr (.inr (reversePoint r))),rfl,
        reversed_mixed_of_turn_entry hP f hpq hqr hturn hqrcolor hout⟩
    · exact ⟨.inl (mapPoint f r),rfl,mapPoint f p,mapPoint f q,
        next_project f hqr,previousDifferent_project f hpq hpqcolor,
        turn_project f hf hturn hpqcolor hqrcolor⟩

theorem global_turn_payment_unique {P : Finset Point} (hP : Instance P)
    (f : Int → Int) {r s : Point} (hr : r ∈ P) (hs : s ∈ P) {a : TurnPayment}
    (hra : TurnPaymentSpec P f r a) (hsa : TurnPaymentSpec P f s a) : r = s := by
  rcases a with a | a
  · exact mapPoint_injective_on hP f hr hs (hra.1.symm.trans hsa.1)
  · rcases a with a | a
    · exact hra.1.symm.trans hsa.1
    · rcases a with a | a
      · obtain ⟨_,q,hpq,hqr,hturn⟩ := hra
        obtain ⟨_,q',hpq',hq's,hturn'⟩ := hsa
        exact turn_source_injective hP hpq hqr hpq' hq's
          (by have := hturn.2.2; omega) (by have := hturn'.2.2; omega)
      · exact reversePoint_involutive.injective (hra.1.symm.trans hsa.1)

noncomputable def turnPayments (P : Finset Point) (f : Int → Int) : Finset TurnPayment :=
  ((project f P).filter (TurnPoint (project f P))).disjSum
    ((P.filter (UnbrokenTurn P f)).disjSum
      ((P.filter (MixedTurn P f)).disjSum
        ((P.image reversePoint).filter (MixedTurn (P.image reversePoint) f))))

theorem turnPayment_mem {P : Finset Point} {f : Int → Int} {r : Point}
    (hr : r ∈ P) {a : TurnPayment} (h : TurnPaymentSpec P f r a) : a ∈ turnPayments P f := by
  rcases a with a | a
  · apply Finset.inl_mem_disjSum.mpr
    exact Finset.mem_filter.mpr ⟨h.1 ▸ Finset.mem_image.mpr ⟨r,hr,rfl⟩,h.2⟩
  · apply Finset.inr_mem_disjSum.mpr
    rcases a with a | a
    · exact Finset.inl_mem_disjSum.mpr (Finset.mem_filter.mpr ⟨h.1 ▸ hr,h.2⟩)
    · apply Finset.inr_mem_disjSum.mpr
      rcases a with a | a
      · have haP := (mixed_internalStart h.1).choose_spec.1.1
        exact Finset.inl_mem_disjSum.mpr (Finset.mem_filter.mpr ⟨haP,h.1⟩)
      · exact Finset.inr_mem_disjSum.mpr (Finset.mem_filter.mpr
          ⟨h.1 ▸ Finset.mem_image.mpr ⟨r,hr,rfl⟩,h.2⟩)

theorem global_turn_bound {P : Finset Point} (hP : Instance P)
    (f : Int → Int) (hf : Monotone f) :
    turnCount P ≤ turnCount (project f P) + eventCount P (UnbrokenTurn P f) +
      mixedTurns P f + mixedTurns (P.image reversePoint) f := by
  classical
  let M := P.filter (TurnPoint P)
  have hex : ∀ r : M, ∃ a, TurnPaymentSpec P f r.val a := by
    intro r
    exact global_turn_payment hP f hf (Finset.mem_filter.mp r.property).2
  choose pay hpay using hex
  let assign : M → turnPayments P f := fun r =>
    ⟨pay r,turnPayment_mem (Finset.mem_filter.mp r.property).1 (hpay r)⟩
  have hinj : Function.Injective assign := by
    intro r s he
    apply Subtype.ext
    have hpayeq : pay r = pay s := congrArg Subtype.val he
    exact global_turn_payment_unique hP f (Finset.mem_filter.mp r.property).1
      (Finset.mem_filter.mp s.property).1 (hpay r) (hpayeq.symm ▸ hpay s)
  have hc := Finset.card_le_card_of_injective hinj
  simpa only [M,turnPayments,turnCount,mixedTurns,eventCount_eq_card,
    Finset.card_disjSum,Nat.add_assoc] using hc

end ChaCha.Paper20261030.Rectangles
