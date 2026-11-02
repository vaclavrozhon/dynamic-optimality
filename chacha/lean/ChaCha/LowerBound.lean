import ChaCha.GadgetLocalBound
import ChaCha.Transfer

/-!
# The dynamic BST lower bound

This module closes the proof from the actual sequence counts to ordinary
root-starting pointer executions. Its public lower bound has no charging,
normalization, simulation, or occurrence-injection hypothesis: these are proved
from the supplied execution. The numerical constant is deliberately unoptimized.
-/

namespace ChaCha

open Primary MTR MTR.Tree

/-- A closed normalized move-to-root execution pays the actual primary and
secondary counts, including one unit for every original query. -/
theorem normalized_dynamic_lower_bound {H : Nat} {t : Tree Key} {xs : List Key}
    (normal : AmbientNormalized H t xs) (successful : Successful t xs)
    (leaves : OnLeaves H xs) (closed : run t xs = t) :
    xs.length + secondaryDemands H xs + primaryCount H xs ≤ 8 * runCost t xs := by
  have normal4 : NormalizedWords.Normalized (initialPreference H t) H
      (xs ++ (xs ++ (xs ++ xs))) := by
    simpa only [repeatWord, List.append_nil] using
      history_normalized_repeatWord normal successful leaves closed 4
  apply normalized_bound_of_four_period_comparison normal successful leaves closed
  exact aggregate_local_demand_bounds_window H xs [] (xs ++ (xs ++ (xs ++ xs))) leaves
    (fun _ hq => gadget_local_bound hq (initialPreference H t) leaves normal4)

/-- Every ordinary dynamic BST pointer execution pays a constant fraction of
`|X| + D(X) + P(X)`, for the concrete midpoint gadgets and their actual access
histories. The reference leaves are binary keys of one fixed height. -/
theorem dynamic_bst_lower_bound {H : Nat} {t u : Tree Key} {xs : List Key} {cost : Nat}
    (execution : Pointer.Execution t xs u cost) (ordered : Ordered t)
    (height : ∀ x ∈ inorder t, x.length = H) :
    xs.length + secondaryDemands H xs + primaryCount H xs ≤ 2888 * cost := by
  exact pointer_transfer (factor := 8)
    (fun _ _ hn hs hl hc => normalized_dynamic_lower_bound hn hs hl hc)
    execution ordered height

end ChaCha
