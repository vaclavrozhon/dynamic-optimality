import ChaCha.Paper20261030.PrimaryFlipBound
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Histogram quantities for the auxiliary reference

`weight f keys` is the total request multiplicity on a list of keys.
`alternationMass f reference` sums the exact expected binary-switch toll
`2ab/(a+b)` over the internal nodes of the reference. Its probabilistic
interpretation is proved separately from these definitions.

`entropyMass f keys` is the unnormalized empirical entropy in natural-log
units: total weight times its logarithm, minus the sum of the corresponding
individual terms. Division by `Real.log 2` converts it to bits. The convention
`Real.log 0 = 0` makes zero weights and the empty histogram harmless.
-/

namespace ChaCha.Entropy

open PreferredProjection

/-- Total multiplicity, counting each listed key once when `keys` is nodup. -/
def weight (f : Int → Nat) (keys : List Int) : Nat := (keys.map f).sum

/-- Sum of binary switch expectations. This definition does not assert a
probabilistic theorem or supply an unproved expectation as a hypothesis. -/
noncomputable def alternationMass (f : Int → Nat) : PrefRouter Int → ℝ
  | .leaf _ => 0
  | .fork _ left right =>
      2 * (weight f left.leaves : ℝ) * (weight f right.leaves : ℝ) /
        ((weight f left.leaves : ℝ) + (weight f right.leaves : ℝ)) +
      alternationMass f left + alternationMass f right

/-- Total empirical entropy in natural-log units. -/
noncomputable def entropyMass (f : Int → Nat) (keys : List Int) : ℝ :=
  (weight f keys : ℝ) * Real.log (weight f keys : ℝ) -
    (keys.map (fun key => (f key : ℝ) * Real.log (f key : ℝ))).sum

@[simp] theorem weight_nil (f : Int → Nat) : weight f [] = 0 := rfl

@[simp] theorem weight_cons (f : Int → Nat) (key : Int) (keys : List Int) :
    weight f (key :: keys) = f key + weight f keys := rfl

@[simp] theorem weight_append (f : Int → Nat) (left right : List Int) :
    weight f (left ++ right) = weight f left + weight f right := by
  simp only [weight,List.map_append,List.sum_append]

@[simp] theorem entropyMass_nil (f : Int → Nat) : entropyMass f [] = 0 := by
  simp [entropyMass]

@[simp] theorem entropyMass_singleton (f : Int → Nat) (key : Int) :
    entropyMass f [key] = 0 := by
  simp [entropyMass]

end ChaCha.Entropy
