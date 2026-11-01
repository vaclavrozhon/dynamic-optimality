import MultiSplay.Competitive

/-! # The composed bound at the exact logarithmic capacity

The balanced reference has height at most `ceil(log₂(n+1))`. Keeping this
integer logarithm avoids a constant-factor enlargement inside an arbitrary
Splay factor. Only monotonicity, not a doubling property, is used.
-/

namespace MultiSplay

/-- The exact integer-logarithmic version of `L₃(n) * g(log n)`. -/
def logarithmicFactor (factor : Nat → Nat) (n : Nat) : Nat :=
  Splay.Analysis.iteratedLog 3 n * factor (Nat.clog 2 (n+1))

namespace Online

open DynamicOptimality

/-- The strongest existing Splay factor at the balanced reference's precise
logarithmic capacity. There is no multiplicative enlargement inside `g`. -/
theorem competitive_logarithmic :
    Competitive cost (logarithmicFactor Splay.Analysis.egTargetFactor) := by
  obtain ⟨constant,positive,bound⟩ := composed_bound
  refine ⟨5*constant,by omega,?_⟩
  intro n _ before requests
  have factor := Nat.mul_le_mul (balancedReference_comparisonFactor_le n)
    (Splay.Analysis.egTargetFactor_mono (balancedReference_height_le n))
  calc
    cost before requests ≤ constant*(OPT requests+n)*
        (comparisonFactor (balancedReference n).height *
          Splay.Analysis.egTargetFactor (balancedReference n).height) := bound before requests
    _ ≤ constant*(OPT requests+n)*((5*Splay.Analysis.iteratedLog 3 n)*
        Splay.Analysis.egTargetFactor (Nat.clog 2 (n+1))) := Nat.mul_le_mul_left _ factor
    _ = _ := by unfold logarithmicFactor; ring

/-- Every monotone factor supported by the persistent Splay interface gives
`L₃(n) * g(ceil(log₂(n+1)))` for the same actual classical algorithm. -/
theorem competitive_generic_logarithmic (factor : Nat → Nat)
    (valid : AdmissibleForestFactor factor) (monotone : Monotone factor) :
    Competitive cost (logarithmicFactor factor) := by
  obtain ⟨constant,positive,bound⟩ := cost_bound_of_factor comparator_estimate factor valid
  refine ⟨5*constant,by omega,?_⟩
  intro n _ before requests
  have comparison := Nat.mul_le_mul (balancedReference_comparisonFactor_le n)
    (monotone (balancedReference_height_le n))
  calc
    cost before requests ≤ constant*(OPT requests+n)*
        (comparisonFactor (balancedReference n).height * factor (balancedReference n).height) :=
      bound before requests
    _ ≤ constant*(OPT requests+n)*((5*Splay.Analysis.iteratedLog 3 n)*
        factor (Nat.clog 2 (n+1))) := Nat.mul_le_mul_left _ comparison
    _ = _ := by unfold logarithmicFactor; ring

end Online
end MultiSplay
