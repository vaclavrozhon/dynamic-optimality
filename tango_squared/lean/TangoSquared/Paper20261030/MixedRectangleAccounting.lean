import TangoSquared.Paper20261030.MixedGuard
import Mathlib.Data.Finset.Sum

/-!
# The strengthened robust-rectangle split inequality

Every mixed turn is assigned either an actual double-switch point in its
chronological window, or a new rectangle whose lower defining point is
that mixed turn. `payment_unique` proves the resulting assignment
injective. The final theorem is manuscript Lemma `rir-union-stronger`,
written with natural-number addition instead of truncated subtraction.
-/

namespace TangoSquared.Paper20261030.Rectangles

open scoped BigOperators
attribute [local instance] Classical.propDecidable

def PaymentSpec (P : Finset Point) (f : Int → Int)
    (base S : Finset Rectangle) (p : Point) : Point ⊕ Rectangle → Prop
  | .inl u => u ∈ P ∧ DoubleSwitch P f u ∧ f u.1 = f p.1 ∧ Window P f p u
  | .inr r => r ∈ S \ base ∧ r.1 = p

theorem exists_payment {P : Finset Point} (hP : Instance P)
    (f : Int → Int) (hf : Monotone f) (I : Finset Int)
    (outer : Finset Rectangle) (inner : Int → Finset Rectangle)
    (ho : RobustFamily (project f P) outer)
    (hi : ∀ i ∈ I, RobustFamily (fiber f i P) (inner i))
    {S : Finset Rectangle} (hS : MaximalRobust P S)
    {p : Point} (hp : MixedTurn P f p) :
    ∃ a, PaymentSpec P f (outer.image (pullRectangle P f) ∪ I.biUnion inner) S p a := by
  rcases mixed_rectangle_or_donor hP f hf hp hS with h | h
  · obtain ⟨u,hu,hcolor,hwin,hdouble⟩ := h
    exact ⟨.inl u,hu,hdouble,hcolor,hwin⟩
  · obtain ⟨p',z,hnext,hcolor,hz,ht,hcross,hmem⟩ := h
    have hnot := split_union_excludes_crossing hP f I outer inner ho hi
      hnext.2.1 hcolor hcross hnext.2.2.1 ht
    exact ⟨.inr (p,z),Finset.mem_sdiff.mpr ⟨hmem,hnot⟩,rfl⟩

theorem payment_unique {P : Finset Point} (hP : Instance P)
    (f : Int → Int) {base S : Finset Rectangle} {p q : Point}
    (hp : MixedTurn P f p) (hq : MixedTurn P f q) {a : Point ⊕ Rectangle}
    (hpa : PaymentSpec P f base S p a) (hqa : PaymentSpec P f base S q a) : p = q := by
  cases a with
  | inl u =>
      obtain ⟨_,_,hucolor,hpu⟩ := hpa
      obtain ⟨_,_,huqcolor,hqu⟩ := hqa
      exact window_donor_injective hP f (mixed_internalStart hp) (mixed_internalStart hq)
        (hucolor.symm.trans huqcolor) hpu hqu
  | inr r => exact hpa.2.symm.trans hqa.2

theorem payment_mem {P : Finset Point} {f : Int → Int}
    {base S : Finset Rectangle} {p : Point} {a : Point ⊕ Rectangle}
    (h : PaymentSpec P f base S p a) :
    a ∈ (P.filter (DoubleSwitch P f)).disjSum (S \ base) := by
  cases a with
  | inl u => exact Finset.inl_mem_disjSum.mpr (Finset.mem_filter.mpr ⟨h.1,h.2.1⟩)
  | inr r => exact Finset.inr_mem_disjSum.mpr h.1

theorem mixed_payment_bound {P : Finset Point} (hP : Instance P)
    (f : Int → Int) (base S : Finset Rectangle)
    (hex : ∀ p ∈ P, MixedTurn P f p → ∃ a, PaymentSpec P f base S p a) :
    mixedTurns P f ≤ doubleSwitchCount P f + (S \ base).card := by
  classical
  let M := P.filter (MixedTurn P f)
  let T := (P.filter (DoubleSwitch P f)).disjSum (S \ base)
  have hchoose : ∀ p : M, ∃ a, PaymentSpec P f base S p.val a := by
    intro p
    obtain ⟨hp,hpmixed⟩ := Finset.mem_filter.mp p.property
    exact hex p.val hp hpmixed
  choose payment hpayment using hchoose
  let assignment : M → T := fun p => ⟨payment p,payment_mem (hpayment p)⟩
  have hinj : Function.Injective assignment := by
    intro p q he
    apply Subtype.ext
    have hvalue : payment p = payment q := congrArg Subtype.val he
    have hpmixed := (Finset.mem_filter.mp p.property).2
    have hqmixed := (Finset.mem_filter.mp q.property).2
    exact payment_unique hP f hpmixed hqmixed (hpayment p) (hvalue.symm ▸ hpayment q)
  have hcard : M.card ≤ T.card := Finset.card_le_card_of_injective hinj
  simpa only [M,T,Finset.card_disjSum,mixedTurns,doubleSwitchCount,eventCount_eq_card] using hcard

/-- Manuscript Lemma `rir-union-stronger`, for arbitrary repeated-key inputs. -/
theorem robustBound_split_mixed {P : Finset Point} (hP : Instance P)
    (f : Int → Int) (hf : Monotone f) (I : Finset Int) :
    robustBound (project f P) + (∑ i ∈ I, robustBound (fiber f i P)) + mixedTurns P f ≤
      robustBound P + doubleSwitchCount P f := by
  classical
  obtain ⟨outer,ho,hocard⟩ := exists_robust_maximum (project f P)
  choose inner hi hicard using fun i : Int => exists_robust_maximum (fiber f i P)
  let base := outer.image (pullRectangle P f) ∪ I.biUnion inner
  obtain ⟨hbase,hbasecard⟩ := split_certificate hP f hf I outer inner ho (fun i _ => hi i)
  obtain ⟨S,hBS,hS⟩ := exists_maximal_extension hbase
  have hpay : mixedTurns P f ≤ doubleSwitchCount P f + (S \ base).card :=
    mixed_payment_bound hP f base S (fun p _ hp =>
      exists_payment hP f hf I outer inner ho (fun i _ => hi i) hS hp)
  have hScard := robust_card_le hS.1
  have hdiff := Finset.card_sdiff_add_card_eq_card hBS
  have hbasevalue : base.card = robustBound (project f P) +
      ∑ i ∈ I, robustBound (fiber f i P) := by
    simpa only [hocard,hicard] using hbasecard
  change (S \ base).card + base.card = S.card at hdiff
  omega

end TangoSquared.Paper20261030.Rectangles
