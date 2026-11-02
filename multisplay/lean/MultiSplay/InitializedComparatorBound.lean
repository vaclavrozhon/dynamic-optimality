import MultiSplay.InitializedGenericBound
import MultiSplay.GlobalPreferredForestBound

/-! # The last numerical reduction for the initialized classical algorithm

This file isolates the final use of a uniform, exact-word comparator
estimate. The estimate is a genuine remaining premise here; no competitive
claim is made until a concrete comparator construction discharges it.
-/

namespace MultiSplay.Online

open DynamicOptimality
/-- Specialize the shared initialization argument to the proved admissible
Splay factor. The exact-word comparator remains an explicit premise. -/
theorem cost_bound_of_comparator_estimate {scale : Nat} (estimate : ComparatorEstimate scale) :
    ∃ constant : Nat, 0 < constant ∧
      ∀ {n : Nat} (before : BST 0 n) (requests : List (Fin n)),
        cost before requests ≤ constant * (OPT requests+n) *
          (comparisonFactor (balancedReference n).height *
            Splay.Analysis.egTargetFactor (balancedReference n).height) :=
  cost_bound_of_factor estimate Splay.Analysis.egTargetFactor admissible_egTargetFactor

/-- The precise shifted bound is `L₃(n) * g(2 L₁(n))`, with the strongest
currently proved Splay factor `g`. The constant is uniform in the initial
tree, request word, and universe size. -/
theorem competitive_of_comparator_estimate {scale : Nat} (estimate : ComparatorEstimate scale) :
    Competitive cost shiftedEGFactor :=
  competitive_shifted_of_factor estimate Splay.Analysis.egTargetFactor
    admissible_egTargetFactor Splay.Analysis.egTargetFactor_mono

end MultiSplay.Online
