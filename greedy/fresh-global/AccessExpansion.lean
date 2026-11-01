import PathPlateau
import CanonicalBridge

/-!
The actual raised canonical tree is a Cartesian separator refinement of
exactly the old search-path keys, with the identical old off-path subtrees
substituted in their original inorder gap slots. No persistence premise
for supplied gaps is assumed; all gaps are extracted from the old tree.
-/
namespace GreedyMerge.AccessExpansion
open Splay.Tree
open Splay.Tree.BST
open GreedyMerge.SearchGaps
open GreedyMerge.PathPlateau
open GreedyMerge.IntervalRootOracle
open GreedyMerge.ExpansionRotations
open GreedyMerge.HierarchyLocality
open GreedyMerge.HierarchyExistence
open GreedyMerge.SurfaceHierarchy
open GreedyMerge.ComparatorAtoms
open GreedyMerge.PlateauBridge
open GreedyMerge.CanonicalBridge

private theorem canonical_castUpper {height : ℕ → ℤ} {priority : ℕ → ℕ}
    {lo hi finish : ℕ} (equal : hi = finish) (tree : BST lo hi)
    (canonical : GreedyMerge.Surface.Canonical height priority tree) :
    GreedyMerge.Surface.Canonical height priority (castUpper equal tree) := by
  cases equal
  exact canonical

/-- Concrete full access expansion, using the exact actual strict-height
neighborhood and deterministic canonical definitions. -/
theorem canonical_after_raise_is_expansion {n access : ℕ}
    (height : ℕ → ℤ) (time : ℤ) (comparator oldTree newTree : BST 0 n)
    (oldOwner newOwner : ℕ → ℕ)
    (oldOwners : GreedyMerge.Surface.Owners height comparator.depth oldOwner n)
    (newOwners : GreedyMerge.Surface.Owners
      (GreedyMerge.Surface.RaiseSurface height n access time) comparator.depth newOwner n)
    (global : GreedyMerge.Surface.UniqueGlobalMinimum comparator.depth n access)
    (fresh : ∀ key, key < n → height key < time)
    (oldCanonical : GreedyMerge.Surface.Canonical height
      (fun key => comparator.depth (oldOwner key)) oldTree)
    (newCanonical : GreedyMerge.Surface.Canonical
      (GreedyMerge.Surface.RaiseSurface height n access time)
      (fun key => comparator.depth (newOwner key)) newTree)
    (p : Decomposition oldTree access) :
    ∃ (gapOwner : ℕ → ℕ) (skeleton : BST 0 p.count),
      (∀ i, i ≤ p.count → UniqueMin comparator.externalDepth
        (2 * GapLower 0 p.separator i) (2 * p.separator i) (gapOwner i)) ∧
      GreedyMerge.IntervalRootOracle.Canonical
        (fun atom => comparator.externalDepth (AtomOwner p.separator gapOwner atom)) skeleton ∧
      newTree = p.expand skeleton := by
  classical
  let raised := GreedyMerge.Surface.RaiseSurface height n access time
  let priority := fun key => comparator.depth (newOwner key)
  have refines := GreedyMerge.Surface.canonical_refines height comparator.depth oldOwner oldTree oldCanonical
  have exactOwners := GreedyMerge.Surface.full_refinement_exactOwners
    height comparator.depth oldOwner oldTree oldOwners refines
  have touchPath : ∀ key, key < n →
      (GreedyMerge.Surface.Neighborhood height n key access ↔ key ∈ PathKeys access oldTree) := by
    intro key hk
    exact neighborhood_iff_pathKeys height comparator.depth oldOwner oldTree oldOwners global
      exactOwners (Nat.le_refl n) (Nat.zero_le access) global.1 (Nat.zero_le key) hk
  have sepHeight : ∀ i, i < p.count → raised (p.separator i) = time := by
    intro i hi
    have hmem := p.member i hi
    have hb := pathKeys_bounds oldTree hmem
    have touch := (touchPath _ hb.2).2 hmem
    simp only [raised, GreedyMerge.Surface.RaiseSurface, if_pos touch]
  have upperHeight : ∀ key, key < n → raised key ≤ time := by
    intro key hk
    unfold raised GreedyMerge.Surface.RaiseSurface
    split_ifs
    · exact le_rfl
    · exact le_of_lt (fresh key hk)
  let children := fun i (_ : i ≤ p.count) =>
    ofSurface raised (GapLower 0 p.separator i) (p.separator i) (p.gaps i).lower_le_upper
  have rep : Represents raised (Hierarchy.node p.separator p.tail children) := by
    refine ⟨p.positive, ?_, ?_, ?_⟩
    · intro i hi key hklo hkhi
      rw [sepHeight i hi]
      exact upperHeight key (by rw [p.endpoint] at hkhi; exact hkhi)
    · intro key hklo hkhi heq
      have hkey : key < n := by rwa [p.endpoint] at hkhi
      have htop : raised key = time := heq.trans (sepHeight 0 p.positive)
      have touch := (GreedyMerge.Surface.raised_top_iff_touched height time (fresh key hkey)).1 htop
      exact p.complete key ((touchPath key hkey).1 touch)
    · intro i hi
      exact ofSurface_represents raised _ _ (p.gaps i).lower_le_upper
  have gapCanonical : ∀ i, i ≤ p.count →
      GreedyMerge.Surface.Canonical raised priority (p.gaps i) := by
    intro i hi
    obtain ⟨depth, occurrence⟩ := (p.actualGap i hi).occurrence
    obtain ⟨newGap, hnew⟩ := GreedyMerge.Surface.exists_canonical raised priority
      (GapLower 0 p.separator i) (p.separator i) (p.gaps i).lower_le_upper
    have heq := GreedyMerge.Surface.disjoint_subtree_shape_preserved height comparator.depth
      oldOwner newOwner oldTree (p.gaps i) newGap time occurrence
      (GreedyMerge.Surface.comparator_intervalUnique comparator) oldOwners newOwners global
      oldCanonical hnew (p.actualGap i hi).outside fresh
    exact heq ▸ hnew
  have ownerExists : ∀ i, i ≤ p.count → ∃ record, UniqueMin comparator.externalDepth
      (2 * GapLower 0 p.separator i) (2 * p.separator i) record := by
    intro i hi
    have hgap := (p.gaps i).lower_le_upper
    have hupper := p.increasing.monotone hi
    rw [p.endpoint] at hupper
    exact exists_uniqueMin_external comparator (by omega) (by omega) (by omega)
  let gapOwner := fun i => if hi : i ≤ p.count then Classical.choose (ownerExists i hi) else 0
  have minima : ∀ i, i ≤ p.count → UniqueMin comparator.externalDepth
      (2 * GapLower 0 p.separator i) (2 * p.separator i) (gapOwner i) := by
    intro i hi
    dsimp only [gapOwner]
    rw [dif_pos hi]
    exact Classical.choose_spec (ownerExists i hi)
  obtain ⟨skeleton, skeletonCanonical⟩ := exists_skeleton comparator p.separator gapOwner p.gaps
    (Nat.le_refl 0) (by rw [p.endpoint]) minima
  have priorities : ∀ i, i < p.count → priority (p.separator i) =
      Priority (fun atom => comparator.externalDepth (AtomOwner p.separator gapOwner atom)) i := by
    intro i hi
    exact (plateau_priority_eq comparator p.separator gapOwner newOwner p.tail children rep
      newOwners hi (by rw [p.endpoint]) (Or.inl rfl) (Or.inl p.endpoint) minima).symm
  have expandedCanonical := expand_canonical p.separator p.tail children rep p.gaps
    gapCanonical priorities skeleton (Nat.le_refl p.count) skeletonCanonical
  have fullCanonical : GreedyMerge.Surface.Canonical raised priority (p.expand skeleton) :=
    canonical_castUpper p.endpoint _ expandedCanonical
  exact ⟨gapOwner, skeleton, minima, skeletonCanonical,
    GreedyMerge.Surface.canonical_unique raised priority newTree (p.expand skeleton)
      newCanonical fullCanonical⟩

end GreedyMerge.AccessExpansion
#print axioms GreedyMerge.AccessExpansion.canonical_after_raise_is_expansion
