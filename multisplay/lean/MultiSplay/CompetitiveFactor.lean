import MultiSplay.BalancedReference
import TangoSquared.Paper20261030.ReferenceHeight
import Mathlib.Tactic.Ring

/-!
# The composed MultiSplay factor

For a logarithmic-height reference, the persistent component-splay theorem
contributes `L₃(n) * L₄(n)^2`, and the secondary comparator contributes
`L₃(n)`. Here `Lₖ` is the stabilized iterated binary logarithm. Their product
is `L₃(n)^2 * L₄(n)^2`; neither factor is cancelled in the composition.
-/

namespace MultiSplay

open Splay.Analysis

/-- The factor obtained by composing the two proved comparisons. -/
def competitiveFactor (n : Nat) : Nat :=
  (iteratedLog 3 n)^2 * (iteratedLog 4 n)^2

 theorem competitiveFactor_pos (n : Nat) : 0 < competitiveFactor n := by
  have third : 0 < iteratedLog 3 n := iteratedLog_pos (by decide)
  have fourth : 0 < iteratedLog 4 n := iteratedLog_pos (by decide)
  unfold competitiveFactor
  positivity

/-- Stabilization absorbs a factor of two at every logarithmic level. -/
theorem stabilizedLog_le_two {a b : Nat} (bound : a ≤ 2*b) :
    stabilizedLog a ≤ 2*stabilizedLog b := by
  have power : max 2 b ≤ 2^stabilizedLog b := Nat.le_pow_clog (by decide) _
  have powerPositive : 0 < 2^stabilizedLog b := Nat.two_pow_pos _
  have smaller : b ≤ max 2 b := Nat.le_max_right _ _
  have logBound : stabilizedLog a ≤ stabilizedLog b+1 := by
    apply Nat.clog_le_of_le_pow
    rw [Nat.pow_add_one]
    exact max_le (by omega) (by omega)
  have positive := stabilizedLog_pos b
  omega

 theorem balancedReference_iteratedLog_le (n depth : Nat) :
    iteratedLog depth (balancedReference n).height ≤ 2*iteratedLog (depth+1) n := by
  induction depth with
  | zero => exact balancedReference_height_le_log n
  | succ depth ih => exact stabilizedLog_le_two ih

 theorem balancedReference_splayFactor_le (n : Nat) :
    targetFactor (balancedReference n).height ≤
      8*iteratedLog 3 n*(iteratedLog 4 n)^2 := by
  have second := balancedReference_iteratedLog_le n 2
  have third := balancedReference_iteratedLog_le n 3
  calc
    targetFactor (balancedReference n).height ≤
        (2*iteratedLog 3 n)*(2*iteratedLog 4 n)^2 :=
      Nat.mul_le_mul second (Nat.pow_le_pow_left third 2)
    _ = _ := by ring

/-- A convenient upper bound on the secondary reference's logarithmic
repair factor. It also covers the completed reference's extra level. -/
def comparisonFactor (height : Nat) : Nat :=
  Nat.clog 2 (Nat.clog 2 (height+1)+2)+1

 theorem comparisonFactor_pos (height : Nat) : 0 < comparisonFactor height := by
  unfold comparisonFactor
  omega

 theorem balancedReference_comparisonFactor_le (n : Nat) :
    comparisonFactor (balancedReference n).height ≤ 5*iteratedLog 3 n := by
  let first := iteratedLog 1 n
  let second := iteratedLog 2 n
  let third := iteratedLog 3 n
  have height : (balancedReference n).height ≤ 2*first := balancedReference_height_le_log n
  have firstPower : first ≤ 2^second :=
    (Nat.le_max_right 2 first).trans (Nat.le_pow_clog (by decide) _)
  have secondPower : second ≤ 2^third :=
    (Nat.le_max_right 2 second).trans (Nat.le_pow_clog (by decide) _)
  have secondPositive : 0 < 2^second := Nat.two_pow_pos _
  have inner : Nat.clog 2 ((balancedReference n).height+1) ≤ second+2 := by
    apply Nat.clog_le_of_le_pow
    rw [show second+2 = (second+1)+1 by omega,Nat.pow_add_one,Nat.pow_add_one]
    omega
  have thirdPositive : 0 < 2^third := Nat.two_pow_pos _
  have outer : Nat.clog 2 (Nat.clog 2 ((balancedReference n).height+1)+2) ≤ third+3 := by
    apply Nat.clog_le_of_le_pow
    rw [show third+3 = ((third+1)+1)+1 by omega,
      Nat.pow_add_one,Nat.pow_add_one,Nat.pow_add_one]
    omega
  have positive : 0 < third := iteratedLog_pos (by decide)
  change _+1 ≤ 5*third
  omega

/-- A shared midpoint depth hierarchy, with no requirement that the
original reference be perfect or have uniform leaf depth. -/
noncomputable def balancedHierarchy (n : Nat) : TangoSquared.DepthTree 0 (balancedReference n).height :=
  TangoSquared.DepthTree.midpoint 0 _ (Nat.zero_le _)

 theorem balancedHierarchy_repairFactor_le (n : Nat) :
    Nat.clog 2 ((TangoSquared.Paper20261030.LocalReferences.depthReference
      (balancedHierarchy n)).height+1)+1 ≤ comparisonFactor (balancedReference n).height := by
  have height := TangoSquared.Paper20261030.LocalReferences.midpoint_height_log
    0 (balancedReference n).height (Nat.zero_le _)
  simp only [Nat.sub_zero] at height
  have bound := Nat.clog_mono_right 2 (show
      (TangoSquared.Paper20261030.LocalReferences.depthReference (balancedHierarchy n)).height+1 ≤
        Nat.clog 2 ((balancedReference n).height+1)+2 by exact Nat.le_trans (Nat.add_le_add_right height 1) (by omega))
  exact Nat.add_le_add_right bound 1

/-- The two independent factors multiply to the advertised fourth-log
factor, uniformly including all small and empty universes. -/
theorem balancedReference_composedFactor_le (n : Nat) :
    comparisonFactor (balancedReference n).height * targetFactor (balancedReference n).height ≤
      40*competitiveFactor n := by
  calc
    _ ≤ (5*iteratedLog 3 n)*(8*iteratedLog 3 n*(iteratedLog 4 n)^2) :=
      Nat.mul_le_mul (balancedReference_comparisonFactor_le n)
        (balancedReference_splayFactor_le n)
    _ = _ := by unfold competitiveFactor; ring

end MultiSplay
