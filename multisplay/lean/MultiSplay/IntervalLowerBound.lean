import MultiSplay.IntervalLocalBound
import MultiSplay.IntervalEventBudget
import MultiSplay.IntervalMonotonicity
import TangoSquared.Transfer

/-!
# The dynamic BST lower bound for an arbitrary binary interval hierarchy

This extension uses the shared actual BST pointer execution and its proved
closed normalized supersequence. Local occurrence records, their joint
injection, global potential telescoping, and subsequence monotonicity are all
proved for the supplied hierarchy. No charging or simulation hypothesis is
left in the public theorem, and no Tango-squared upper bound is used.
-/

namespace MultiSplay.IntervalLower

open TangoSquared
open TangoSquared.Primary TangoSquared.MTR TangoSquared.MTR.Tree

theorem secondaryDemands_le_allGadgets {H : Nat} (hierarchy : DepthTree 0 H) (xs : List Key) :
    secondaryDemands hierarchy xs ≤ ∑ q ∈ allGadgets hierarchy, q.count xs := by
  exact Finset.sum_le_sum_of_subset (gadgets_subset_all hierarchy)


theorem aggregate_local_demand_bounds_window {H : Nat} (hierarchy : DepthTree 0 H) (xs history window : List Key)
    (hleaves : OnLeaves H xs)
    (local_bound : ∀ q ∈ allGadgets hierarchy,
      (q.count xs : ℤ) ≤ q.potentialDifference H xs +
        2 * (eventSum H {q} history window : ℤ)) :
    secondaryDemands hierarchy xs ≤ cyclicPrimary H xs + 2 * eventSum H (allGadgets hierarchy) history window := by
  have hsum := Finset.sum_le_sum local_bound
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  have hevents : (∑ q ∈ allGadgets hierarchy,
      (eventSum H {q} history window : ℤ)) = (eventSum H (allGadgets hierarchy) history window : ℤ) := by
    rw [← Nat.cast_sum, sum_singleton_eventSum]
  rw [hevents] at hsum
  have hpot := allGadgets_potential_le_primary hierarchy xs hleaves
  have hd := secondaryDemands_le_allGadgets hierarchy xs
  have hd' : (secondaryDemands hierarchy xs : ℤ) ≤ ∑ q ∈ allGadgets hierarchy, (q.count xs : ℤ) := by
    exact_mod_cast hd
  have hout : (secondaryDemands hierarchy xs : ℤ) ≤
      (cyclicPrimary H xs : ℤ) + 2 * (eventSum H (allGadgets hierarchy) history window : ℤ) := by omega
  exact_mod_cast hout


/-- The concrete normalized execution pays all interval-owner demands. -/
theorem normalized_dynamic_lower_bound {H : Nat} (hierarchy : DepthTree 0 H)
    {tree : Tree Key} {word : List Key}
    (normal : AmbientNormalized H tree word) (successful : Successful tree word)
    (leaves : OnLeaves H word) (closed : run tree word = tree) :
    word.length + secondaryDemands hierarchy word + primaryCount H word ≤ 8 * runCost tree word := by
  have normal4 : NormalizedWords.Normalized (initialPreference H tree) H (word++(word++(word++word))) := by
    simpa only [repeatWord, List.append_nil] using history_normalized_repeatWord normal successful leaves closed 4
  have demands := aggregate_local_demand_bounds_window hierarchy word [] (word++(word++(word++word))) leaves
    (fun gadget member => gadget_local_bound member (initialPreference H tree) leaves normal4)
  have events := four_period_budget (allGadgets hierarchy) (fun _ member => allGadgets_valid member)
    normal successful leaves closed
  have primary := primary_le_cyclic H word
  have combined := cyclicPrimary_add_internalSearchVisits_le_rotations normal successful leaves closed
  have cost := runCost_eq_length_add_rotationCount tree word
  omega

/-- Every actual root-starting pointer execution pays the secondary demands
of any supplied binary hierarchy on depths 0 through H. -/
theorem dynamic_bst_lower_bound {H : Nat} (hierarchy : DepthTree 0 H)
    {before after : Tree Key} {word : List Key} {cost : Nat}
    (execution : Pointer.Execution before word after cost) (ordered : Ordered before)
    (height : ∀ key ∈ inorder before, key.length = H) :
    word.length + secondaryDemands hierarchy word + primaryCount H word ≤ 2888 * cost := by
  obtain ⟨normalized, subsequence, closed, paid, normal, successful, leaves⟩ :=
    execution.closed_normalized_supersequence ordered height
  have monotone := total_sublist (hierarchy := hierarchy) subsequence leaves
  have bound := normalized_dynamic_lower_bound hierarchy normal successful leaves closed
  omega

end MultiSplay.IntervalLower
