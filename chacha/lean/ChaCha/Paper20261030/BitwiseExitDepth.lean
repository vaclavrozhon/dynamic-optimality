import ChaCha.Paper20261030.CanonicalPrimary
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.Bitwise

/-! Computing the primary exit from two original key ranks.
For H-bit ranks, the exit depth is H minus the bit length of their XOR.
The specification `lcaDepth` uses a finite supremum; this implementation
uses only the ranks and word arithmetic. The separator test below is
exactly the quotient comparison in the manuscript's AccessExit proof.
-/

namespace ChaCha.Paper20261030.Dyadic

theorem xor_zero_iff (x y : Nat) : x ^^^ y = 0 ↔ x = y := by
  constructor
  · intro same
    have equal := congrArg (fun a => a ^^^ y) same
    simpa only [Nat.xor_assoc,Nat.xor_self,Nat.xor_zero,Nat.zero_xor] using equal
  · intro same
    subst y
    exact Nat.xor_self x

theorem quotient_eq_iff_xor_size (x y exponent : Nat) :
    x / 2^exponent = y / 2^exponent ↔ (x ^^^ y).size ≤ exponent := by
  rw [Nat.size_le,← Nat.div_eq_zero_iff_lt (pow_pos (by decide : (0 : Nat) < 2) exponent),
    Nat.xor_div_two_pow,xor_zero_iff]

def exitDepth (height : Nat) (x z : Int) : Nat :=
  height - (x.toNat ^^^ z.toNat).size

theorem coarsen_toNat (H d : Nat) (x : Int) (nonnegative : 0 ≤ x) :
    coarsen H d x = (x.toNat / 2^(H-d) : Nat) := by
  simp only [coarsen,Int.natCast_ediv,Int.natCast_pow,Int.toNat_of_nonneg nonnegative]
  rfl

theorem valid_toNat {H : Nat} {x : Int} (valid : ValidKey H x) : x.toNat < 2^H := by
  have nonnegative := valid.1
  have bounded : (x.toNat : Int) < ((2^H : Nat) : Int) := by
    rw [Int.toNat_of_nonneg nonnegative,Int.natCast_pow]
    exact valid.2
  exact_mod_cast bounded

theorem xor_size_le {H : Nat} {x z : Int} (hx : ValidKey H x) (hz : ValidKey H z) :
    (x.toNat ^^^ z.toNat).size ≤ H :=
  Nat.size_le.mpr (Nat.xor_lt_two_pow (valid_toNat hx) (valid_toNat hz))

theorem coarsen_eq_iff_le_exit {H d : Nat} {x z : Int}
    (hx : ValidKey H x) (hz : ValidKey H z) (depth : d ≤ H) :
    coarsen H d x = coarsen H d z ↔ d ≤ exitDepth H x z := by
  rw [coarsen_toNat H d x hx.1,coarsen_toNat H d z hz.1,Int.natCast_inj,quotient_eq_iff_xor_size]
  have size := xor_size_le hx hz
  unfold exitDepth
  omega

theorem exitDepth_eq_lcaDepth {H : Nat} {x z : Int} (hx : ValidKey H x) (hz : ValidKey H z) :
    exitDepth H x z = lcaDepth H x z := by
  have bounded : exitDepth H x z ≤ H := Nat.sub_le _ _
  have lcaBound := lcaDepth_le hx hz
  have forward := (ancestor_eq_iff_le_lca hx hz bounded).mp
    ((coarsen_eq_iff_le_exit hx hz bounded).mpr (Nat.le_refl _))
  have backward := (coarsen_eq_iff_le_exit hx hz lcaBound).mp
    ((ancestor_eq_iff_le_lca hx hz lcaBound).mpr (Nat.le_refl _))
  omega

theorem exitDepth_completion {H : Nat} {x z : Int} (hx : ValidKey H x) (hz : ValidKey H z) :
    exitDepth H x z = H ↔ x = z := by
  have same := coarsen_eq_iff_le_exit hx hz (Nat.le_refl H)
  rw [coarsen_self,coarsen_self] at same
  have bounded : exitDepth H x z ≤ H := Nat.sub_le _ _
  omega

/-- The paper's equation `exit-separator-test`, using zero-based ranks. -/
theorem exit_separator_test {H j : Nat} {x z : Int}
    (hx : ValidKey H x) (hz : ValidKey H z) (separator : j < H) :
    j < exitDepth H x z ↔ x / (2 : Int)^(H-j-1) = z / (2 : Int)^(H-j-1) := by
  have test := coarsen_eq_iff_le_exit hx hz (show j+1 ≤ H by omega)
  have exponent : H-(j+1) = H-j-1 := by omega
  simpa only [coarsen,exponent,Nat.add_one_le_iff] using test.symm

theorem exitDepth_eq_referenceLCA {H : Nat} {x z : Int} (hx : ValidKey H x) (hz : ValidKey H z) :
    exitDepth H x z = (canonical H 0).referenceLCA x z :=
  (exitDepth_eq_lcaDepth hx hz).trans (canonical_lca hx hz).symm

end ChaCha.Paper20261030.Dyadic
