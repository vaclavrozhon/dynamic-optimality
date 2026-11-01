import Mathlib.Data.Finset.Sum
import Mathlib.Tactic

/-!
Finite arithmetic for the first-winning-residence argument.

This is deliberately a certificate theorem, not a native interface Trace
theorem. The LaTeX companion proves that a legal trace supplies the early
winning budget and the disjoint first-nonexempt-pass frontier certificate.
-/

namespace Splay.Research.FirstWinBinary

/-- The certificate retains separate frontier source sizes and matching
sizes, so the late-activity bound is checked before the final arithmetic. -/
structure FrontierCertificate (e D A F T : ℕ) where
  count : ℕ
  sourceSize : Fin count → ℕ
  matchingSize : Fin count → ℕ
  early : ℕ
  late : ℕ
  partition : A = early + late
  earlyBudget : early ≤ e * F
  terminalInFrontier : ℕ
  lateBudget : late + terminalInFrontier ≤ ∑ x, sourceSize x
  dense : ∀ x, sourceSize x ≤ D * matchingSize x
  distinctWinners : (∑ x, matchingSize x) ≤ F
  terminalBudget : T + (∑ x, matchingSize x) ≤ terminalInFrontier + F

theorem frontier_activity_bound {e D A F T : ℕ}
    (c : FrontierCertificate e D A F T) (densityAtMostOne : 1 ≤ D) :
    A + T ≤ (e + D) * F := by
  have sourceBound : (∑ x, c.sourceSize x) ≤ D * ∑ x, c.matchingSize x := by
    calc
      (∑ x, c.sourceSize x) ≤ ∑ x, D * c.matchingSize x := by
        exact Finset.sum_le_sum fun x _ => c.dense x
      _ = D * ∑ x, c.matchingSize x := by rw [Finset.mul_sum]
  have lateBound := c.lateBudget.trans sourceBound
  have earlyBound := c.earlyBudget
  have partition := c.partition
  have terminalBound := c.terminalBudget
  have winners := c.distinctWinners
  nlinarith

theorem binary_change_budget {F terminal down up I : ℕ}
    (downwardInjection : F ≤ down)
    (upwardInjection : F ≤ up + terminal)
    (terminalInjection : terminal ≤ I) : 2 * F ≤ down + up + I := by
  omega

theorem binary_coefficient_bound {A F I U T : ℕ}
    (activity : A + T ≤ 10 * F) (changes : 2 * F ≤ T + U)
    (terminal : T ≤ I) : A ≤ 4 * I + 5 * U := by omega

theorem binary_frontier_bound {A F I down up terminal : ℕ}
    (c : FrontierCertificate 2 8 A F terminal)
    (downwardInjection : F ≤ down)
    (upwardInjection : F ≤ up + terminal)
    (terminalInjection : terminal ≤ I) :
    A ≤ 9 * down + up ∧ A ≤ 4 * I + 5 * (down + up) := by
  have activity : A + terminal ≤ 10 * F := frontier_activity_bound c (by decide)
  have changes : 2 * F ≤ terminal + (down + up) := by
    have h := binary_change_budget downwardInjection upwardInjection (le_refl terminal)
    omega
  constructor
  · omega
  · exact binary_coefficient_bound activity changes terminalInjection

theorem coefficient_region_upper {A I U a b : ℝ}
    (insertNonnegative : 0 ≤ I) (variationNonnegative : 0 ≤ U)
    (zeroInsertion : A ≤ 9 * U) (sharpVariation : A ≤ 4 * I + 5 * U)
    (aNonnegative : 0 ≤ a) (bLower : 5 ≤ b) (sumLower : 9 ≤ a + b) :
    A ≤ a * I + b * U := by
  by_cases hb : 9 ≤ b
  · nlinarith
  · have hw : 0 ≤ 9 - b := by linarith
    have hw' : 0 ≤ b - 5 := by linarith
    have h₁ := mul_nonneg hw (sub_nonneg.mpr sharpVariation)
    have h₂ := mul_nonneg hw' (sub_nonneg.mpr zeroInsertion)
    have h₃ := mul_nonneg insertNonnegative (show 0 ≤ a + b - 9 by linarith)
    nlinarith

#print axioms frontier_activity_bound
#print axioms binary_frontier_bound
#print axioms coefficient_region_upper

end Splay.Research.FirstWinBinary
