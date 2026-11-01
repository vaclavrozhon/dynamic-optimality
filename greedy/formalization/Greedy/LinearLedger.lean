import Mathlib

/-!
# Numerical closure of the linear complete-consolidation ledger

`K` is the label range; `N`, `I`, `L`, and `P` count records, ordinary
entries, created block instances, and paid label changes. `Vp` and `Vm`
are positive and negative label variation. `g`, `b`, and `J` count good,
boundary, and all internal links. `D` is the total entry deficit. The
three shifts are the winner, loser, and creator terms in the exact entry
identity. This module only closes the numerical inequalities: it does
not claim that an arbitrary Greedy execution supplies those inequalities.
-/

namespace Greedy.LinearLedger

theorem collected (K N I L P Vp Vm g b J D Sw Sl Sc : ℤ)
    (positive : Vp ≤ 4 * L * (K - 1) + P * K)
    (negative : Vm ≤ N * (K - 1) + Vp)
    (good : g ≤ Vm)
    (boundary : b ≤ Vm + (2 * K + 4) * L)
    (deficits : D ≤ K * (N + I) + g + b + 4 * Vm + 5 * (K - 1) * L)
    (internal : J ≤ 4 * D + Sw + Sl + Sc)
    (winner : Sw ≤ 4 * Vm)
    (loser : Sl ≤ (K - 1) * (N + I) + Vm + 13 * (K - 1) * L + Vp)
    (creator : Sc ≤ 9 * (Vp + Vm)) :
    J + b ≤ (44 * K - 40) * N + (5 * K - 1) * I +
      (239 * K - 209) * L + 49 * K * P := by
  nlinarith

theorem linear (K N I L P Vp Vm g b J D Sw Sl Sc : ℤ)
    (hK : 1 ≤ K) (hN : 0 ≤ N) (hI : 0 ≤ I) (hL : 0 ≤ L) (hP : 0 ≤ P)
    (positive : Vp ≤ 4 * L * (K - 1) + P * K)
    (negative : Vm ≤ N * (K - 1) + Vp)
    (good : g ≤ Vm)
    (boundary : b ≤ Vm + (2 * K + 4) * L)
    (deficits : D ≤ K * (N + I) + g + b + 4 * Vm + 5 * (K - 1) * L)
    (internal : J ≤ 4 * D + Sw + Sl + Sc)
    (winner : Sw ≤ 4 * Vm)
    (loser : Sl ≤ (K - 1) * (N + I) + Vm + 13 * (K - 1) * L + Vp)
    (creator : Sc ≤ 9 * (Vp + Vm)) :
    J + b ≤ 239 * K * (N + I + L + P) := by
  have bound := collected K N I L P Vp Vm g b J D Sw Sl Sc
    positive negative good boundary deficits internal winner loser creator
  have nNonneg : 0 ≤ K * N := mul_nonneg (by omega) hN
  have iNonneg : 0 ≤ K * I := mul_nonneg (by omega) hI
  have pNonneg : 0 ≤ K * P := mul_nonneg (by omega) hP
  nlinarith

/-- The current-deficit winner potential includes at most four initial
credits per record. The same linear coefficient absorbs this reserve. -/
theorem with_initial_credit (K N I L P Vp Vm g b J D Sl Sc : ℤ)
    (hK : 1 ≤ K) (hN : 0 ≤ N) (hI : 0 ≤ I) (hL : 0 ≤ L) (hP : 0 ≤ P)
    (positive : Vp ≤ 4 * L * (K - 1) + P * K)
    (negative : Vm ≤ N * (K - 1) + Vp)
    (good : g ≤ Vm)
    (boundary : b ≤ Vm + (2 * K + 4) * L)
    (deficits : D ≤ K * (N + I) + g + b + 4 * Vm + 5 * (K - 1) * L)
    (internal : J ≤ 4 * D + 4 * Vm + Sl + Sc + 4 * N)
    (loser : Sl ≤ (K - 1) * (N + I) + Vm + 13 * (K - 1) * L + Vp)
    (creator : Sc ≤ 9 * (Vp + Vm)) :
    J + b ≤ 239 * K * (N + I + L + P) := by
  have bound := collected K N I L P Vp Vm g b (J-4*N) D (4*Vm) Sl Sc
    positive negative good boundary deficits (by linarith) (le_refl _) loser creator
  have nNonneg : 0 ≤ K * N := mul_nonneg (by omega) hN
  have iNonneg : 0 ≤ K * I := mul_nonneg (by omega) hI
  have pNonneg : 0 ≤ K * P := mul_nonneg (by omega) hP
  nlinarith

end Greedy.LinearLedger
