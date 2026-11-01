import MultiSplay.GlobalPreferredGenericBound
import MultiSplay.InitializedComparatorBound

/-! # A generic factor from every original initial BST

A valid split/join interface factor `g` yields `comparisonFactor H * g H`
at reference height `H`. The actual comparator estimate remains explicit,
so this numerical adapter cannot conceal a missing local comparator proof.
-/

namespace MultiSplay.Online

open DynamicOptimality
open CommonForest ClassicalSwitch EndpointEncoding

/-- The initialization is performed once and charged from the supplied
initial tree. The constant is uniform over all universe sizes and words. -/
theorem cost_bound_of_factor {scale : Nat} (estimate : ComparatorEstimate scale)
    (factor : Nat → Nat) (valid : AdmissibleForestFactor factor) :
    ∃ constant : Nat, 0 < constant ∧
      ∀ {n : Nat} (before : BST 0 n) (requests : List (Fin n)),
        cost before requests ≤ constant * (OPT requests+n) *
          (comparisonFactor (balancedReference n).height * factor (balancedReference n).height) := by
  obtain ⟨constant,positive,bound⟩ :=
    Global.Preferred.Online.initial_run_comparator_bound_of_factor factor valid
  refine ⟨constant*(scale+1)+20,by omega,?_⟩
  intro n before requests
  obtain ⟨sources,targets,budget,domains,program,paid⟩ := estimate n requests
  have physical := bound (balancedReference n) (fun _ => true) requests domains program
  have setup := cost_le_canonical before requests
  change ((canonicalStrategy n).run (canonicalState n) requests).2 ≤
    constant*(n+budget)*factor (balancedReference n).height+requests.length at physical
  obtain ⟨_,_,rotations,_,optimum⟩ := OPT_attained requests
  have requestsPaid : requests.length ≤ OPT requests+n := by omega
  have comparatorPositive := comparisonFactor_pos (balancedReference n).height
  have factorPositive := valid.positive (balancedReference n).height
  have productPositive : 1 ≤ comparisonFactor (balancedReference n).height *
      factor (balancedReference n).height := Nat.mul_pos comparatorPositive factorPositive
  have initialScaled : n ≤ comparisonFactor (balancedReference n).height * (OPT requests+n) := by
    nlinarith
  have volume : n+budget ≤ (scale+1) * comparisonFactor (balancedReference n).height *
      (OPT requests+n) := by nlinarith
  have comparison := Nat.mul_le_mul_right (factor (balancedReference n).height)
    (Nat.mul_le_mul_left constant volume)
  have small := Nat.mul_le_mul_left (20*(OPT requests+n)) productPositive
  calc
    cost before requests ≤ 19*n+
        (constant*(n+budget)*factor (balancedReference n).height+requests.length) := by omega
    _ ≤ 20*(OPT requests+n)+
        constant*((scale+1)*comparisonFactor (balancedReference n).height*(OPT requests+n))*
          factor (balancedReference n).height := by omega
    _ ≤ 20*(OPT requests+n)*(comparisonFactor (balancedReference n).height*factor (balancedReference n).height)+
        constant*((scale+1)*comparisonFactor (balancedReference n).height*(OPT requests+n))*
          factor (balancedReference n).height := by omega
    _ = _ := by ring

/-- This transfer assumes an admissible common-forest interface factor;
plain query-only Splay competitiveness is not substituted for it. -/
theorem competitive_of_factor {scale : Nat} (estimate : ComparatorEstimate scale)
    (factor : Nat → Nat) (valid : AdmissibleForestFactor factor) :
    Competitive cost (fun n =>
      comparisonFactor (balancedReference n).height * factor (balancedReference n).height) := by
  obtain ⟨constant,positive,bound⟩ := cost_bound_of_factor estimate factor valid
  exact ⟨constant,positive,fun _ _ before requests => bound before requests⟩

/-- For a monotone admissible factor the balanced height is at most twice
the stabilized logarithm, giving the literal weaker shifted target. -/
theorem competitive_shifted_of_factor {scale : Nat} (estimate : ComparatorEstimate scale)
    (factor : Nat → Nat) (valid : AdmissibleForestFactor factor) (monotone : Monotone factor) :
    Competitive cost (fun n => Splay.Analysis.iteratedLog 3 n *
      factor (2 * Splay.Analysis.iteratedLog 1 n)) := by
  obtain ⟨constant,positive,bound⟩ := cost_bound_of_factor estimate factor valid
  refine ⟨5*constant,by omega,?_⟩
  intro n _ before requests
  have comparison := Nat.mul_le_mul (balancedReference_comparisonFactor_le n)
    (monotone (balancedReference_height_le_log n))
  calc
    cost before requests ≤ constant*(OPT requests+n)*
        (comparisonFactor (balancedReference n).height * factor (balancedReference n).height) :=
      bound before requests
    _ ≤ constant*(OPT requests+n)*((5*Splay.Analysis.iteratedLog 3 n)*
        factor (2*Splay.Analysis.iteratedLog 1 n)) := Nat.mul_le_mul_left _ comparison
    _ = _ := by ring

end MultiSplay.Online
