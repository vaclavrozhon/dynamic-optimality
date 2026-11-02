import ChaCha.Separation.SparseFragments
import ChaCha.Separation.StaticUpper
import Splay.Analysis.IteratedLog

/-!
# Explicit third-logarithm separation on the original keys

For parameter r >= 2 there are k = 2^r active keys in a universe of
n = 2^(2^(k-1)) keys. The requests repeat bit reversal on those active
keys. The primary reference is the canonical perfect reference and the
depth reference is the full midpoint reference, with no deleted leaf.

The denominator is the manuscript's baseline-inclusive fixed-reference
counter F0 = m + primary alternations + fragment alternations. Both its
upper bound and the robust bound refer to the identical request word.
The final two-sided inequalities give a Theta(L3(n)) ratio, using exactly
the repository's stabilized iterated-logarithm convention.
-/

namespace ChaCha.Separation

open Paper20261030 Paper20261030.Rectangles Paper20261030.Dyadic

def sparseUniverse (parameter : Nat) : Nat := 2^(sparseHeight (2^parameter))

def sparseReference (parameter : Nat) : DepthTree 0 (sparseHeight (2^parameter)-1) :=
  DepthTree.midpoint 0 _ (Nat.zero_le _)

noncomputable def fixedCounter (parameter copies : Nat) : Nat :=
  let requests := sparseRequests parameter copies
  requests.length + (canonical (sparseHeight (2^parameter)) 0).primaryWilber requests +
    fragmentAlternations (sparseReference parameter) (accessPoints requests)

theorem sparseRequests_fragments (parameter copies : Nat) :
    fragmentAlternations (sparseReference parameter) (accessPoints (sparseRequests parameter copies)) ≤
      copies*2^parameter := by
  have positive : 0 < (2:Nat)^parameter := Nat.two_pow_pos _
  have bound := sparse_midpoint_fragments (2^parameter-1) (sparseHeight (2^parameter))
    (by rfl) (accessPoints (sparseRequests parameter copies)) (accessPoints_instance _) (by
      intro point member
      rw [← pointWord_toFinset] at member
      have keyMember : point.1 ∈ (pointWord 0 (sparseRequests parameter copies)).map Prod.fst :=
        List.mem_map.mpr ⟨point,List.mem_toFinset.mp member,rfl⟩
      rw [pointWord_keys] at keyMember
      obtain ⟨rank,present,same⟩ := List.mem_map.mp keyMember
      exact ⟨rank,by have := rankRequests_valid parameter copies rank present; omega,same.symm⟩)
  have start : sparseHeight (2^parameter)-2^(2^parameter-1) = 0 := Nat.sub_self _
  rw [fragment_midpoint_congr start _ (Nat.zero_le _),accessPoints_card,sparseRequests_length] at bound
  exact bound

theorem fixedCounter_linear (parameter copies : Nat) :
    copies*2^parameter ≤ fixedCounter parameter copies ∧
      fixedCounter parameter copies ≤ 4*(copies*2^parameter) := by
  have primary := sparseRequests_primary parameter copies
  have fragments := sparseRequests_fragments parameter copies
  simp only [fixedCounter,sparseRequests_length]
  omega

theorem stabilizedLog_pow {exponent : Nat} (positive : 0 < exponent) :
    Splay.Analysis.stabilizedLog (2^exponent) = exponent := by
  have two : 2 ≤ (2:Nat)^exponent := by
    calc
      2 = 2^1 := by decide
      _ ≤ 2^exponent := Nat.pow_le_pow_right (by decide) positive
  simp only [Splay.Analysis.stabilizedLog,max_eq_right two,Nat.clog_pow 2 exponent (by decide)]

theorem sparseUniverse_third_log {parameter : Nat} (large : 2 ≤ parameter) :
    Splay.Analysis.iteratedLog 3 (sparseUniverse parameter) = parameter := by
  have four : 4 ≤ (2:Nat)^parameter := by
    calc
      4 = 2^2 := by decide
      _ ≤ 2^parameter := Nat.pow_le_pow_right (by decide) large
  have first : Splay.Analysis.iteratedLog 1 (sparseUniverse parameter) = sparseHeight (2^parameter) :=
    stabilizedLog_pow (Nat.two_pow_pos _)
  have second : Splay.Analysis.iteratedLog 2 (sparseUniverse parameter) = 2^parameter-1 := by
    change Splay.Analysis.stabilizedLog (Splay.Analysis.iteratedLog 1 (sparseUniverse parameter)) = _
    rw [first]
    exact stabilizedLog_pow (by omega)
  change Splay.Analysis.stabilizedLog (Splay.Analysis.iteratedLog 2 (sparseUniverse parameter)) = _
  rw [second]
  simp only [Splay.Analysis.stabilizedLog,max_eq_right (show 2 ≤ 2^parameter-1 by omega)]
  apply Nat.le_antisymm
  · exact Nat.clog_le_of_le_pow (Nat.sub_le _ _)
  · have predPositive : 0 < parameter-1 := by omega
    have predPower : 2 ≤ (2:Nat)^(parameter-1) := by
      calc
        2 = 2^1 := by decide
        _ ≤ 2^(parameter-1) := Nat.pow_le_pow_right (by decide) predPositive
    have powers : 2^parameter = 2^(parameter-1)*2 := by
      rw [← pow_succ,Nat.sub_add_cancel (by omega : 1 ≤ parameter)]
    have bound : parameter-1 < Nat.clog 2 (2^parameter-1) :=
      (Nat.lt_clog_iff_pow_lt (by decide)).mpr (by omega)
    omega

/-- Uniform constants, all repeated occurrences retained, and the actual
fixed-reference counters on the same sparse original-key request word. -/
theorem explicit_third_log_separation (parameter copies : Nat)
    (large : 2 ≤ parameter) (nonempty : 0 < copies) :
    Splay.Analysis.iteratedLog 3 (sparseUniverse parameter)*fixedCounter parameter copies ≤
        8*robustBound (accessPoints (sparseRequests parameter copies)) ∧
      robustBound (accessPoints (sparseRequests parameter copies)) ≤
        4*Splay.Analysis.iteratedLog 3 (sparseUniverse parameter)*fixedCounter parameter copies := by
  rw [sparseUniverse_third_log large]
  obtain ⟨counterLower,counterUpper⟩ := fixedCounter_linear parameter copies
  have lower := sparseRequests_robust_lower parameter copies nonempty
  have upper := sparseRequests_robust_upper parameter copies
  have blockBound : 2^parameter ≤ copies*2^parameter := Nat.le_mul_of_pos_left _ nonempty
  have twice : 2*(copies*2^parameter) ≤ parameter*(copies*2^parameter) := Nat.mul_le_mul_right _ large
  have paid : parameter*(copies*2^parameter) ≤
      2*robustBound (accessPoints (sparseRequests parameter copies)) := by omega
  constructor
  · calc
      _ ≤ parameter*(4*(copies*2^parameter)) := Nat.mul_le_mul_left _ counterUpper
      _ = 4*(parameter*(copies*2^parameter)) := by ac_rfl
      _ ≤ 4*(2*robustBound (accessPoints (sparseRequests parameter copies))) := Nat.mul_le_mul_left _ paid
      _ = _ := by simp only [← Nat.mul_assoc]
  · calc
      _ ≤ 2*(parameter+1)*(copies*2^parameter) := upper
      _ ≤ (4*parameter)*(copies*2^parameter) := Nat.mul_le_mul_right _ (by omega)
      _ ≤ _ := Nat.mul_le_mul_left _ counterLower

end ChaCha.Separation
