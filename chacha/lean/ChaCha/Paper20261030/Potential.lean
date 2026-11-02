import ChaCha.Paper20261030.TurnPotentialRelease
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# The concrete split potential

This is Lemma `phi-exists` of the imported manuscript. All three component
inequalities are proved from the input sequence and the interval split.
-/

namespace ChaCha.Paper20261030.Rectangles

open scoped BigOperators

theorem potential_split_release {P : Finset Point} (hP : Instance P)
    (f : Int → Int) (hf : Monotone f) (I : Finset Int) (hI : ∀ p ∈ P, f p.1 ∈ I) :
    (depthAlternations P f : Int) + potential (project f P) +
      ∑ i ∈ I, potential (fiber f i P) ≤ potential P := by
  have hs := switch_split_identity hP f I hI
  have ht := turn_potential_release hP f hf I hI
  have hr := rectangle_potential_release hP f hf I
  have hsZ := congrArg (fun n : Nat => (n : Int)) hs
  have htZ : ((depthAlternations P f + turnCount P + switchIndicator P : Nat) : Int) ≤
      ((turnCount (project f P) + switchIndicator (project f P) +
      (∑ i ∈ I, (turnCount (fiber f i P) + switchIndicator (fiber f i P))) +
      2 * (mixedTurns P f + mixedTurns (P.image reversePoint) f) : Nat) : Int) :=
    Int.ofNat_le.mpr ht
  have hrZ : ((5 * (robustBound (project f P) + ∑ i ∈ I, robustBound (fiber f i P)) +
      2 * (mixedTurns P f + mixedTurns (P.image reversePoint) f) : Nat) : Int) ≤
      ((5 * robustBound P + 4 * doubleSwitchCount P f : Nat) : Int) := Int.ofNat_le.mpr hr
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_sum,
    Finset.sum_add_distrib] at hsZ htZ hrZ
  simp only [potential,Finset.sum_sub_distrib,← Finset.mul_sum]
  omega

/-- Nonnegative potential bounded by five times the ordinary rectangle bound,
with release paying every actual depth exit at every monotone split. -/
theorem concrete_potential_properties {P : Finset Point} (hP : Instance P) :
    0 ≤ potential P ∧ potential P ≤ 5 * (rectangleBound P : Int) ∧
      ∀ (f : Int → Int), Monotone f → ∀ (I : Finset Int),
      (∀ p ∈ P, f p.1 ∈ I) →
      (depthAlternations P f : Int) + potential (project f P) +
        ∑ i ∈ I, potential (fiber f i P) ≤ potential P := by
  exact ⟨potential_nonnegative hP,potential_le_rectangleBound P,
    fun f hf I hI => potential_split_release hP f hf I hI⟩

end ChaCha.Paper20261030.Rectangles
