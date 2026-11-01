import TangoSquared.Simulation
import TangoSquared.EventAggregation

/-!
# Final arithmetic and subsequence transfer

These arithmetic and subsequence-transfer helpers take local comparisons as
explicit arguments. `GadgetLocalBound.lean` proves the concrete comparison;
`LowerBound.lean` supplies it here and obtains the unconditional lower bound
for actual pointer executions.
-/

namespace TangoSquared
open Primary MTR MTR.Tree

/-- Convert a proved demand/period comparison into an actual MTR cost bound. -/
theorem normalized_bound_of_demand_comparison {H : Nat} {t : Tree Key} {xs : List Key}
    (hn : AmbientNormalized H t xs) (hs : Successful t xs) (hl : OnLeaves H xs)
    (hc : run t xs = t)
    (hd : secondaryDemands H xs ≤ cyclicPrimary H xs + 2 * threePeriodEvents H xs) :
    xs.length + secondaryDemands H xs + primaryCount H xs ≤ 6 * runCost t xs := by
  have hp := primary_le_cyclic H xs
  have he := threePeriodEvents_budget hn hs hl hc
  have hpay := cyclicPrimary_add_internalSearchVisits_le_rotations hn hs hl hc
  have hcost := runCost_eq_length_add_rotationCount t xs
  omega

/-- Assemble actual per-fragment occurrence bounds for a closed normalized word. -/
theorem normalized_bound_of_local_comparisons {H : Nat} {t : Tree Key} {xs : List Key}
    (hn : AmbientNormalized H t xs) (hs : Successful t xs) (hl : OnLeaves H xs)
    (hc : run t xs = t)
    (hlocal : ∀ q ∈ allGadgets H,
      (q.count xs : ℤ) ≤ q.potentialDifference H xs +
        2 * (eventSum H {q} xs (xs ++ (xs ++ xs)) : ℤ)) :
    xs.length + secondaryDemands H xs + primaryCount H xs ≤ 6 * runCost t xs :=
  normalized_bound_of_demand_comparison hn hs hl hc
    (aggregate_local_demand_bounds H xs hl hlocal)

/-- The four-copy occurrence window costs only a larger absolute constant. -/
theorem normalized_bound_of_four_period_comparison {H : Nat} {t : Tree Key} {xs : List Key}
    (hn : AmbientNormalized H t xs) (hs : Successful t xs) (hl : OnLeaves H xs)
    (hc : run t xs = t)
    (hd : secondaryDemands H xs ≤ cyclicPrimary H xs + 2 * fourPeriodEvents H xs) :
    xs.length + secondaryDemands H xs + primaryCount H xs ≤ 8 * runCost t xs := by
  have hp := primary_le_cyclic H xs
  have he := fourPeriodEvents_budget hn hs hl hc
  have hpay := cyclicPrimary_add_internalSearchVisits_le_rotations hn hs hl hc
  have hcost := runCost_eq_length_add_rotationCount t xs
  omega

/-- Monotonicity transfers an already established normalized-word bound through
the actual constant-cost simulation of an ordinary BST pointer execution. -/
theorem pointer_transfer {H factor : Nat}
    (normalized_estimate : ∀ (t : Tree Key) (zs : List Key),
      AmbientNormalized H t zs → Successful t zs → OnLeaves H zs → run t zs = t →
        zs.length + secondaryDemands H zs + primaryCount H zs ≤ factor * runCost t zs)
    {t u : Tree Key} {xs : List Key} {cost : Nat}
    (execution : Pointer.Execution t xs u cost) (ordered : Ordered t)
    (height : ∀ x ∈ inorder t, x.length = H) :
    xs.length + secondaryDemands H xs + primaryCount H xs ≤ (factor * 361) * cost := by
  obtain ⟨zs, hsub, hclosed, hcost, hnorm, hsuccess, hleaves⟩ :=
    execution.closed_normalized_supersequence ordered height
  have hmono := total_sublist hsub hleaves
  have hbound := normalized_estimate t zs hnorm hsuccess hleaves hclosed
  exact hmono.trans (hbound.trans (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left factor hcost))

end TangoSquared
