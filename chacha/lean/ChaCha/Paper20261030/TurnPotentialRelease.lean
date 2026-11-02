import ChaCha.Paper20261030.ExitAccounting
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Turn potential release

This proves Lemma `phi-2-bound` for actual finite instances and arbitrary
monotone interval contractions, including the empty and single-segment
cases. No charging or bounded-overlap assumptions are supplied externally.
-/

namespace ChaCha.Paper20261030.Rectangles

open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem local_turn_partition (P : Finset Point) (f : Int → Int) (I : Finset Int)
    (hI : ∀ p ∈ P, f p.1 ∈ I) :
    eventCount P (UnbrokenTurn P f) + eventCount P (BrokenTurn P f) =
      ∑ i ∈ I, turnCount (fiber f i P) := by
  have hfib : (∑ i ∈ I, turnCount (fiber f i P)) = eventCount P (LocalTurn P f) := by
    unfold turnCount eventCount
    calc
      _ = ∑ i ∈ I, ∑ p ∈ P.filter (fun p => f p.1 = i),
          if LocalTurn P f p then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro p hp
        simp only [LocalTurn,(Finset.mem_filter.mp hp).2]
      _ = _ := Finset.sum_fiberwise_of_maps_to hI _
  rw [hfib]
  unfold eventCount
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  have hu := @unbroken_local P f p
  by_cases hU : UnbrokenTurn P f p <;> by_cases hL : LocalTurn P f p <;>
    simp_all [BrokenTurn]

theorem switchCount_zero_keys_equal {P : Finset Point} (hP : Instance P)
    (hzero : switchCount P = 0) {p q : Point} (hp : p ∈ P) (hq : q ∈ P) : p.1 = q.1 := by
  by_contra hn
  rcases lt_trichotomy p.2 q.2 with ht | ht | ht
  · obtain ⟨s,hsq⟩ := exists_previousDifferent hq ⟨p,hp,ht,hn⟩
    have := switchCount_positive_of_previousDifferent hP hsq
    omega
  · exact hn (congrArg Prod.fst (hP p hp q hq ht))
  · obtain ⟨s,hsp⟩ := exists_previousDifferent hp ⟨q,hq,ht,Ne.symm hn⟩
    have := switchCount_positive_of_previousDifferent hP hsp
    omega

theorem depthAlternations_zero_of_constant (P : Finset Point) (f : Int → Int)
    (hc : ∀ p ∈ P, ∀ q ∈ P, f p.1 = f q.1) : depthAlternations P f = 0 := by
  unfold depthAlternations eventCount
  apply Finset.sum_eq_zero
  intro p hp
  have hn : ¬ DepthExit P f p := by
    rintro ⟨s,q,hsp,hscolor,hpq,hout⟩
    exact hout (hc p hp q hpq.2.1)
  simp only [if_neg hn]

theorem mixedTurns_zero_of_constant (P : Finset Point) (f : Int → Int)
    (hc : ∀ p ∈ P, ∀ q ∈ P, f p.1 = f q.1) : mixedTurns P f = 0 := by
  unfold mixedTurns eventCount
  apply Finset.sum_eq_zero
  intro p hp
  have hn : ¬ MixedTurn P f p := by
    rintro ⟨p',q,hnext,hcolor,hq,hout,hrest⟩
    exact hout (hc q hq p hp)
  simp only [if_neg hn]

theorem local_indicator_of_zero_macro_switches {P : Finset Point} (hP : Instance P)
    (f : Int → Int) (I : Finset Int) (hI : ∀ p ∈ P, f p.1 ∈ I)
    (hzero : switchCount (project f P) = 0) :
    switchIndicator P ≤ ∑ i ∈ I, switchIndicator (fiber f i P) := by
  by_cases hpos : 0 < switchCount P
  · have hsum := switch_split_identity hP f I hI
    have hex : ∃ i ∈ I, 0 < switchCount (fiber f i P) := by
      by_contra hn
      have hz : ∀ i ∈ I, switchCount (fiber f i P) = 0 := by
        intro i hi
        by_contra hne
        exact hn ⟨i,hi,by omega⟩
      have heq := Finset.sum_eq_zero hz
      omega
    obtain ⟨i,hi,hsi⟩ := hex
    have hle := Finset.single_le_sum (fun j hj => Nat.zero_le (switchIndicator (fiber f j P))) hi
    simp only [switchIndicator,if_pos hpos]
    simpa only [switchIndicator,if_pos hsi] using hle
  · simp only [switchIndicator,if_neg hpos]
    exact Nat.zero_le _

theorem turn_potential_release {P : Finset Point} (hP : Instance P)
    (f : Int → Int) (hf : Monotone f) (I : Finset Int) (hI : ∀ p ∈ P, f p.1 ∈ I) :
    depthAlternations P f + turnCount P + switchIndicator P ≤
      turnCount (project f P) + switchIndicator (project f P) +
      (∑ i ∈ I, (turnCount (fiber f i P) + switchIndicator (fiber f i P))) +
      2 * (mixedTurns P f + mixedTurns (P.image reversePoint) f) := by
  have hg := global_turn_bound hP f hf
  have hd := depth_exit_bound hP f hf I hI
  have hl := local_turn_partition P f I hI
  rw [Finset.sum_add_distrib]
  by_cases hmacro : 0 < switchCount (project f P)
  · have hi : switchIndicator P ≤ switchIndicator (project f P) := by
      simp only [switchIndicator,if_pos hmacro]
      split <;> omega
    omega
  · have hzero : switchCount (project f P) = 0 := by omega
    have hc : ∀ p ∈ P, ∀ q ∈ P, f p.1 = f q.1 := by
      intro p hp q hq
      exact switchCount_zero_keys_equal (instance_project hP f) hzero
        (Finset.mem_image.mpr ⟨p,hp,rfl⟩) (Finset.mem_image.mpr ⟨q,hq,rfl⟩)
    have hd0 := depthAlternations_zero_of_constant P f hc
    have hm0 := mixedTurns_zero_of_constant P f hc
    have hmr0 : mixedTurns (P.image reversePoint) f = 0 := by
      apply mixedTurns_zero_of_constant
      intro p hp q hq
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hq
      exact hc a ha b hb
    have hi := local_indicator_of_zero_macro_switches hP f I hI hzero
    omega

end ChaCha.Paper20261030.Rectangles
