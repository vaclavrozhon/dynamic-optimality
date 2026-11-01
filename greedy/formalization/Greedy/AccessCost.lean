import Greedy.Algorithm
import AccessDegree

/-!
# The constructed consolidation has the actual Greedy cost

The row touched by geometric Greedy is exactly the search path in the
canonical surface refinement. The access factory's literal event list
therefore has twice the row size minus two links. This bridge relates
the structural accounting to the algorithm definition used by the shared
competitiveness target.
-/

namespace Greedy

open Splay.Tree GreedyMerge.Surface GreedyMerge.Geometry
open GreedyMerge.SearchGaps GreedyMerge.PathPlateau GreedyMerge.ActualLinks

theorem row_eq_path {n access : ℕ} (height : Surface) (rank owner : ℕ → ℕ)
    (tree : BST 0 n) (owners : Owners height rank owner n)
    (global : UniqueGlobalMinimum rank n access)
    (canonical : Canonical height (fun key => rank (owner key)) tree) :
    GreedyRow height n access = PathKeys access tree := by
  have exactOwners := full_refinement_exactOwners height rank owner tree owners
    (canonical_refines height rank owner tree canonical)
  ext key
  by_cases inside : key < n
  · exact mem_greedyRow.trans (neighborhood_iff_pathKeys height rank owner tree owners global
      exactOwners (le_refl _) (Nat.zero_le _) global.1 (Nat.zero_le _) inside)
  · have noRow : key ∉ GreedyRow height n access := fun member => inside (mem_greedyRow.mp member).1
    have noPath : key ∉ PathKeys access tree := fun member => inside (pathKeys_bounds tree member).2
    simp only [noRow, noPath]

theorem decomposition_count {n access : ℕ} (tree : BST 0 n) (decomposition : Decomposition tree access) :
    decomposition.count = (PathKeys access tree).card := by
  have imageEq : (Finset.range decomposition.count).image decomposition.separator = PathKeys access tree := by
    ext key
    constructor
    · intro member
      obtain ⟨i, before, rfl⟩ := Finset.mem_image.mp member
      exact decomposition.member i (Finset.mem_range.mp before)
    · intro member
      obtain ⟨i, before, same⟩ := decomposition.complete key member
      exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr before, same.symm⟩
  rw [← imageEq, Finset.card_image_of_injective _ decomposition.increasing.injective, Finset.card_range]

theorem actual_access_link_count {n access : ℕ} (height : Surface)
    (comparator oldTree newTree : BST 0 n) (owner : ℕ → ℕ)
    (owners : Owners height comparator.depth owner n)
    (global : UniqueGlobalMinimum comparator.depth n access)
    (canonical : Canonical height (fun key => comparator.depth (owner key)) oldTree)
    (decomposition : Decomposition oldTree access)
    (data : AccessScheduleData comparator oldTree newTree decomposition) :
    data.events.length = 2 * ((GreedyRow height n access).card - 1) := by
  rw [data.event_count, decomposition_count oldTree decomposition, ← row_eq_path height comparator.depth owner oldTree
    owners global canonical]
  omega

/-- A canonical refinement exists for every comparator and every finite
surface. These are concrete choices, with no supplied owner oracle. -/
structure Refinement {n : ℕ} (height : Surface) (comparator : BST 0 n) where
  owner : ℕ → ℕ
  owners : Owners height comparator.depth owner n
  tree : BST 0 n
  canonical : Canonical height (fun key => comparator.depth (owner key)) tree

noncomputable def refinement {n : ℕ} (height : Surface) (comparator : BST 0 n) :
    Refinement height comparator := by
  let owner := Classical.choose (exists_owners height comparator.depth n)
  have owners := Classical.choose_spec (exists_owners height comparator.depth n)
  let witness := exists_canonical height (fun key => comparator.depth (owner key)) 0 n (Nat.zero_le _)
  exact ⟨owner, owners, Classical.choose witness, Classical.choose_spec witness⟩

end Greedy
