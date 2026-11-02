import MultiSplay.Obstructions.ClassicalFamily
import Mathlib.Data.Nat.Log

/-! Failure of a universal per-access third-logarithm potential inequality.
The stabilized factor is 1+floor(log₂(floor(log₂(H+2)))); changing to real
logs alters only universal constants. This is explicitly an obstruction
for arbitrary legal initialized states, not a lower bound on MultiSplay. -/

namespace MultiSplay.Obstructions.Classical

open DynamicOptimality (RawTree)
open DynamicOptimality.SearchRotation
open ChaCha (DepthTree)
open ChaCha.Primary (Key)
open EndpointEncoding ClassicalSwitch Global.Preferred

/-- A convenient integer version of 1+log log(H+2), positive even at H=0. -/
def doubleLogFactor (height : Nat) : Nat := 1+Nat.log 2 (Nat.log 2 (height+2))

 theorem doubleLog_family_bound (s : Nat) (positive : 0 < s) :
    doubleLogFactor (2^(2*s+1)-1) ≤ 1+Nat.log 2 (2*s+2) := by
  have power : 0 < 2^(2*s+1) := by positivity
  have room : 2^(2*s+1)-1+2 ≤ 2^(2*s+2) := by
    rw [show 2*s+2 = (2*s+1)+1 by omega,pow_succ]
    omega
  have inner := Nat.log_mono_right (b := 2) room
  rw [Nat.log_pow (by decide)] at inner
  have outer := Nat.log_mono_right (b := 2) inner
  exact Nat.add_le_add_left outer 1

/-- The rotation count outruns every constant multiple of the proposed
charge, for arbitrarily large members of the exact constructed family. -/
 theorem unbounded_ratio (constant threshold : Nat) :
    ∃ s > threshold, 0 < s ∧
      3*constant*doubleLogFactor (2^(2*s+1)-1) < 3*s-1 := by
  let t := constant+threshold+4
  let s := 2^(4*t)
  have tLarge : 4 ≤ t := by dsimp [t]; omega
  have constantBound : constant ≤ t := by dsimp [t]; omega
  have thresholdBound : threshold < t := by dsimp [t]; omega
  have sPositive : 0 < s := by dsimp [s]; positivity
  have tPower : t < 2^t := Nat.lt_two_pow_self
  have fourth : t^4 < s := by
    dsimp [s]
    rw [show 4*t=t*4 by omega,pow_mul]
    exact pow_lt_pow_left₀ tPower (Nat.zero_le _) (by decide)
  have tSquare : 16 ≤ t*t := by nlinarith
  have fourthBound : 16*(t*t) ≤ t^4 := by
    have bound := Nat.mul_le_mul_right (t*t) tSquare
    nlinarith only [bound]
  have tLess : t < s := by nlinarith
  have small : 2*s+2 ≤ 2^(4*t+2) := by
    dsimp [s]
    rw [pow_add]
    norm_num
    have power : 0 < 2^(4*t) := by positivity
    omega
  have outer := Nat.log_mono_right (b := 2) small
  rw [Nat.log_pow (by decide)] at outer
  have factor := doubleLog_family_bound s sPositive
  have charge : 3*constant*doubleLogFactor (2^(2*s+1)-1) ≤ 3*t*(4*t+3) := by
    exact Nat.mul_le_mul (Nat.mul_le_mul_left 3 constantBound) (by omega)
  refine ⟨s,thresholdBound.trans tLess,sPositive,?_⟩
  have many : 3*t*(4*t+3)+1 < 3*s := by nlinarith
  omega

/-- No nonnegative multiple of the classical sum-log potential, augmented
by any function of the primary preferred partition alone, proves the
specified universal per-request bound. The formal witness uses the
literal physical switch history, shared search-plus-rotations cost,
persistent component inventory, and owner-indexed secondary ledger. -/
 theorem classical_potential_obstruction (constant coefficient : ℝ)
    (coefficientNonnegative : 0 ≤ coefficient)
    (partitionPotential : List (RawTree Nat) → ℝ) (threshold : Nat) :
    ∃ (s : Nat) (_ : threshold < s) (_ : 0 < s),
      let height := 2^(2*s+1)-1
      ∃ (reference before after : RawTree Nat) (trees next : List (RawTree Nat))
        (address : Key) (pivot cost work : Nat),
        reference = perfect height (2^height) ∧ reference.size = 2^height-1 ∧
        before.Ordered ∧ before.inorder = reference.inorder ∧ after.inorder = reference.inorder ∧
        Core allRight reference before trees ∧ Core (nodeStep allRight address) reference after next ∧
        Switches allRight reference (actualEmissions allRight address) before after (3*s-1) work ∧
        Access pivot before after cost ∧
        ancestorEmissions allRight address = [] ∧ actualEmissions allRight address = [address] ∧
        forest (nodeStep allRight address) reference = forest allRight reference ∧
        Secondary.actualLedger (DepthTree.midpoint 0 height (Nat.zero_le height)) (fun _ => true)
          allRight [address] = 1 ∧
        constant*(doubleLogFactor height : ℝ)*(1+1+1) <
          (cost : ℝ)+coefficient*(forestRank next-forestRank trees)+
            (partitionPotential (forest (nodeStep allRight address) reference)-
              partitionPotential (forest allRight reference)) := by
  obtain ⟨integer,bigger⟩ := exists_nat_gt constant
  obtain ⟨s,thresholdBound,positive,charge⟩ := unbounded_ratio integer threshold
  obtain ⟨reference,before,after,trees,next,address,pivot,cost,work,referenceEq,size,ordered,
    beforeWord,afterWord,initial,final,history,access,rotations,gain,ancestors,emissions,partition,ledger⟩ :=
    physical_family s positive
  have logPositive : 0 < Real.logb 2 6 := Real.logb_pos (by norm_num) (by norm_num)
  have increase : 0 ≤ forestRank next-forestRank trees := by
    have nonnegative : 0 ≤ (s : ℝ)*Real.logb 2 6 := mul_nonneg (Nat.cast_nonneg _) (le_of_lt logPositive)
    linarith
  have paid : 0 ≤ coefficient*(forestRank next-forestRank trees) := mul_nonneg coefficientNonnegative increase
  have factorNonnegative : 0 ≤ (doubleLogFactor (2^(2*s+1)-1) : ℝ) := Nat.cast_nonneg _
  have upper := mul_le_mul_of_nonneg_right (le_of_lt bigger) factorNonnegative
  have chargeReal : (3 : ℝ)*integer*doubleLogFactor (2^(2*s+1)-1) < (3*s-1 : Nat) := by
    exact_mod_cast charge
  have costReal : ((3*s-1 : Nat) : ℝ) ≤ cost := by exact_mod_cast rotations
  refine ⟨s,thresholdBound,positive,reference,before,after,trees,next,address,pivot,cost,work,
    referenceEq,size,ordered,beforeWord,afterWord,initial,final,history,access,
    ancestors,emissions,partition,ledger,?_⟩
  rw [partition,sub_self]
  linarith

end MultiSplay.Obstructions.Classical
