import MultiSplay.InitializedOnline
import MultiSplay.GlobalPreferredForestBound
import MultiSplay.CompetitiveEGFactor

/-! # The last numerical reduction for the initialized classical algorithm

This file isolates the final use of a uniform, exact-word comparator
estimate. The estimate is a genuine remaining premise here; no competitive
claim is made until a concrete comparator construction discharges it.
-/

namespace MultiSplay.Online

open DynamicOptimality
open CommonForest ClassicalSwitch EndpointEncoding

def ComparatorEstimate (scale : Nat) : Prop :=
  ∀ n (requests : List (Fin n)),
    ∃ sources targets budget,
      domains sources = domains (forest (fun _ => true) (balancedReference n).toRaw) ∧
      Program sources
        (historyWord (balancedReference n).toRaw (fun _ => true)
          (requests.map fun key => nodeAddress (balancedReference n) key.val)) targets budget ∧
      budget ≤ scale * comparisonFactor (balancedReference n).height * (OPT requests+n)

theorem cost_bound_of_comparator_estimate {scale : Nat} (estimate : ComparatorEstimate scale) :
    ∃ constant : Nat, 0 < constant ∧
      ∀ {n : Nat} (before : BST 0 n) (requests : List (Fin n)),
        cost before requests ≤ constant * (OPT requests+n) *
          (comparisonFactor (balancedReference n).height *
            Splay.Analysis.egTargetFactor (balancedReference n).height) := by
  obtain ⟨constant,positive,bound⟩ := Global.Preferred.Online.initial_run_comparator_bound_eg
  refine ⟨constant*(scale+1)+20,by omega,?_⟩
  intro n before requests
  obtain ⟨sources,targets,budget,domains,program,paid⟩ := estimate n requests
  have physical := bound (balancedReference n) (fun _ => true) requests domains program
  have setup := cost_le_canonical before requests
  change ((canonicalStrategy n).run (canonicalState n) requests).2 ≤
    constant*(n+budget)*Splay.Analysis.egTargetFactor (balancedReference n).height + requests.length at physical
  obtain ⟨_,_,rotations,_,optimum⟩ := OPT_attained requests
  have requestsPaid : requests.length ≤ OPT requests+n := by omega
  have initialPaid : n ≤ OPT requests+n := by omega
  have comparatorPositive : 0 < comparisonFactor (balancedReference n).height := comparisonFactor_pos _
  have splayPositive : 0 < Splay.Analysis.egTargetFactor (balancedReference n).height :=
    Splay.Analysis.egTargetFactor_pos _
  have factorPositive : 1 ≤ comparisonFactor (balancedReference n).height *
      Splay.Analysis.egTargetFactor (balancedReference n).height :=
    Nat.mul_pos comparatorPositive splayPositive
  have initialScaled : n ≤ comparisonFactor (balancedReference n).height * (OPT requests+n) := by
    nlinarith
  have volume : n+budget ≤ (scale+1) * comparisonFactor (balancedReference n).height *
      (OPT requests+n) := by
    nlinarith
  have comparison := Nat.mul_le_mul_right (Splay.Analysis.egTargetFactor (balancedReference n).height)
    (Nat.mul_le_mul_left constant volume)
  have small := Nat.mul_le_mul_left (20*(OPT requests+n)) factorPositive
  calc
    cost before requests ≤ 19*n +
        (constant*(n+budget)*Splay.Analysis.egTargetFactor (balancedReference n).height + requests.length) := by omega
    _ ≤ 20*(OPT requests+n) +
        constant*((scale+1)*comparisonFactor (balancedReference n).height*(OPT requests+n))*
          Splay.Analysis.egTargetFactor (balancedReference n).height := by omega
    _ ≤ 20*(OPT requests+n)*(comparisonFactor (balancedReference n).height*
          Splay.Analysis.egTargetFactor (balancedReference n).height) +
        constant*((scale+1)*comparisonFactor (balancedReference n).height*(OPT requests+n))*
          Splay.Analysis.egTargetFactor (balancedReference n).height := by omega
    _ = _ := by ring

/-- The precise shifted bound is `L₃(n) * g(2 L₁(n))`, with the strongest
currently proved Splay factor `g`. The constant is uniform in the initial
tree, request word, and universe size. -/
theorem competitive_of_comparator_estimate {scale : Nat} (estimate : ComparatorEstimate scale) :
    Competitive cost shiftedEGFactor := by
  obtain ⟨constant,positive,bound⟩ := cost_bound_of_comparator_estimate estimate
  refine ⟨5*constant,by omega,?_⟩
  intro n _ before requests
  calc
    cost before requests ≤ constant*(OPT requests+n)*
        (comparisonFactor (balancedReference n).height *
          Splay.Analysis.egTargetFactor (balancedReference n).height) := bound before requests
    _ ≤ constant*(OPT requests+n)*(5*shiftedEGFactor n) :=
      Nat.mul_le_mul_left _ (balancedReference_composedEGFactor_le_shifted n)
    _ = _ := by ring

end MultiSplay.Online
