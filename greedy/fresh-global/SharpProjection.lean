import ProjectionRotation
import AtomRotationMin

/-!
The actual sharp port-projection theorem. An input BST on alternating atoms
[2*lo,2*hi] is projected to a fixed-left-tie Cartesian BST on separators
[lo,hi), using the minimum of the three neighboring atom depths as priority.
An arbitrary-depth input rotation changes the projection by at most two
ordinary BST rotations. No assumed common-fringe or oracle-locality property
occurs in the final theorem's hypotheses.
-/
namespace GreedyMerge.SharpProjection
open Splay.Tree
open Splay.Tree.BST
open GreedyMerge.IntervalRootOracle
open GreedyMerge.ProjectionRotation
open GreedyMerge.PortCases

theorem uniqueMin_of_unique {rank : ℕ → ℕ} {lo hi owner : ℕ}
    (hm : IsIntervalMin rank lo hi owner)
    (hu : ∀ other, IsIntervalMin rank lo hi other → other = owner) :
    UniqueMin rank lo hi owner := by
  refine ⟨hm, ?_⟩
  intro other hl hh hne
  have hle := hm.2.2 other hl hh
  by_contra hnot
  have heq : rank other = rank owner := by omega
  have hother : IsIntervalMin rank lo hi other := by
    refine ⟨hl, hh, ?_⟩
    intro key hkl hkh
    rw [heq]
    exact hm.2.2 key hkl hkh
  exact hne (hu other hother)

theorem exists_uniqueMin_depth {treeLo treeHi lo hi : ℕ}
    (tree : BST treeLo treeHi) (hl : treeLo ≤ lo) (hne : lo ≤ hi)
    (hu : hi < treeHi) : ∃ owner, UniqueMin tree.depth lo hi owner := by
  obtain ⟨owner, hm, hu⟩ := tree.existsUnique_intervalDepthMin hl hne hu
  exact ⟨owner, uniqueMin_of_unique hm hu⟩

theorem eq_of_isMin {rank : ℕ → ℕ} {lo hi owner other : ℕ}
    (hm : UniqueMin rank lo hi owner) (ho : IsIntervalMin rank lo hi other) :
    other = owner := by
  by_contra hne
  have hlt := hm.2 other ho.1 ho.2.1 hne
  have hle := ho.2.2 owner hm.1.1 hm.1.2.1
  omega

/-- Concrete BST rotations supply exactly the previously formalized oracle
interface, uniformly over every expanded separator interval. -/
theorem changesOnly_of_rotation {treeLo treeHi lo hi depth : ℕ}
    {before after : BST treeLo treeHi} (step : RotationAt depth before after)
    (hl : treeLo ≤ 2 * lo) (hu : 2 * hi < treeHi) :
    ∃ a b, ChangesOnly before.depth after.depth lo hi a b := by
  obtain ⟨a, b, hchange⟩ := AtomRotationMin.rotation_intervalMin_changes step
  refine ⟨a, b, ?_⟩
  intro l u hll hlu huu
  obtain ⟨old, ho⟩ := exists_uniqueMin_depth before (by omega : treeLo ≤ 2 * l)
    (by omega : 2 * l ≤ 2 * u) (by omega : 2 * u < treeHi)
  obtain ⟨new, hn⟩ := exists_uniqueMin_depth after (by omega : treeLo ≤ 2 * l)
    (by omega : 2 * l ≤ 2 * u) (by omega : 2 * u < treeHi)
  refine ⟨old, new, ho, hn, ?_⟩
  rcases hchange (2 * l) (2 * u) old ho.1 with hs | ⟨ha, hb⟩
  · exact Or.inl (eq_of_isMin hn hs)
  · exact Or.inr ⟨ha, (eq_of_isMin hn hb).symm⟩

theorem atom_rotation_projection {treeLo treeHi lo hi depth : ℕ}
    {before after : BST treeLo treeHi} (step : RotationAt depth before after)
    (hl : treeLo ≤ 2 * lo) (hu : 2 * hi < treeHi)
    (first second : BST lo hi) (hf : Canonical before.depth first)
    (hs : Canonical after.depth second) :
    ∃ steps, steps ≤ 2 ∧ RotationSteps steps first second := by
  obtain ⟨a, b, hchange⟩ := changesOnly_of_rotation step hl hu
  exact projection_rotations first second hf hs hchange

theorem exists_projection {treeLo treeHi lo hi : ℕ}
    (tree : BST treeLo treeHi) (h : lo ≤ hi)
    (hl : treeLo ≤ 2 * lo) (hu : 2 * hi < treeHi) :
    ∃ output : BST lo hi, Canonical tree.depth output := by
  apply exists_canonical tree.depth lo hi h
  intro l u hll hlu huu
  obtain ⟨owner, hm⟩ := exists_uniqueMin_depth tree (by omega : treeLo ≤ 2 * l)
    (by omega : 2 * l ≤ 2 * u) (by omega : 2 * u < treeHi)
  exact ⟨owner, hm, hm⟩

/-- The canonical fixed-left-tie separator projection as a total map on
alternating-atom BSTs. Its defining property uniquely determines the output. -/
noncomputable def project {lo hi : ℕ} (input : BST (2 * lo) (2 * hi + 1)) : BST lo hi :=
  Classical.choose (exists_projection input
    (by have h := input.lower_le_upper; omega) (by omega) (by omega))

theorem project_canonical {lo hi : ℕ} (input : BST (2 * lo) (2 * hi + 1)) :
    Canonical input.depth (project input) :=
  Classical.choose_spec (exists_projection input
    (by have h := input.lower_le_upper; omega) (by omega) (by omega))

/-- Complete sharp projection locality for an actual input rotation at any
depth, with all surrounding output context and fringe inferred by the proof. -/
theorem project_rotation {lo hi depth : ℕ}
    {before after : BST (2 * lo) (2 * hi + 1)}
    (step : RotationAt depth before after) :
    ∃ steps, steps ≤ 2 ∧ RotationSteps steps (project before) (project after) :=
  atom_rotation_projection step (by omega) (by omega)
    (project before) (project after) (project_canonical before) (project_canonical after)

end GreedyMerge.SharpProjection

#print axioms GreedyMerge.SharpProjection.changesOnly_of_rotation
#print axioms GreedyMerge.SharpProjection.atom_rotation_projection
#print axioms GreedyMerge.SharpProjection.project_rotation
