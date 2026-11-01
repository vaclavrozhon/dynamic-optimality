import OrderedAtoms
import RotationIntervalMin

/-!
A concrete comparator BST rotation induces the ordered-atom oracle changes.
This connects the actual external-record depths to the sharp projection
bound, without assuming a Cartesian quotient rotation or invariant fringe.
-/
namespace GreedyMerge.ComparatorAtoms
open Splay.Tree
open Splay.Tree.BST
open GreedyMerge.IntervalRootOracle
open GreedyMerge.ProjectionRotation
open GreedyMerge.SharpProjection
open GreedyMerge.OrderedAtoms
open GreedyMerge.PortCases

theorem exists_uniqueMin_external {treeLo treeHi lo hi : ℕ}
    (tree : BST treeLo treeHi) (hl : 2 * treeLo ≤ lo) (hne : lo ≤ hi)
    (hu : hi ≤ 2 * treeHi) : ∃ owner, UniqueMin tree.externalDepth lo hi owner := by
  obtain ⟨owner, hm, hu⟩ := tree.existsUnique_intervalExternalDepthMin hl hne hu
  exact ⟨owner, uniqueMin_of_unique hm hu⟩

theorem recordChanges_of_keyRotation {treeLo treeHi lo hi a b depth : ℕ}
    {before after : BST treeLo treeHi}
    (step : GreedyMerge.KeyRotationAt a b depth before after)
    (hl : 2 * treeLo ≤ lo) (hu : hi ≤ 2 * treeHi) :
    RecordChanges before.externalDepth after.externalDepth lo hi (2 * a + 1) (2 * b + 1) := by
  intro l u hll hlu huu
  obtain ⟨old, ho⟩ := exists_uniqueMin_external before (by omega : 2 * treeLo ≤ l)
    hlu (by omega : u ≤ 2 * treeHi)
  obtain ⟨new, hn⟩ := exists_uniqueMin_external after (by omega : 2 * treeLo ≤ l)
    hlu (by omega : u ≤ 2 * treeHi)
  refine ⟨old, new, ho, hn, ?_⟩
  rcases step.intervalMin ho.1 with hs | ⟨ha, hb⟩
  · exact Or.inl (eq_of_isMin hn hs)
  · exact Or.inr ⟨ha, (eq_of_isMin hn hb).symm⟩

/-- The separator projection of any fixed ordered record partition changes
by at most two rotations under an actual comparator rotation. -/
theorem comparator_projection_rotations
    {treeLo treeHi a b depth n : ℕ} {before after : BST treeLo treeHi}
    (step : GreedyMerge.KeyRotationAt a b depth before after)
    (cut owner owner' : ℕ → ℕ) (hcut : StrictMono cut)
    (hl : 2 * treeLo ≤ cut 0) (hu : cut (2 * n + 1) - 1 ≤ 2 * treeHi)
    (owners : AtomOwners before.externalDepth cut owner (2 * n + 1))
    (owners' : AtomOwners after.externalDepth cut owner' (2 * n + 1))
    (first second : BST 0 n)
    (hf : Canonical (fun atom => before.externalDepth (owner atom)) first)
    (hs : Canonical (fun atom => after.externalDepth (owner' atom)) second) :
    ∃ steps, steps ≤ 2 ∧ RotationSteps steps first second :=
  contracted_projection_rotations hcut owners owners'
    (recordChanges_of_keyRotation step hl hu) first second hf hs

/-- The entire separator tree is fixed when the comparator's two rotated
keys occupy one atom, even if that atom's representative changes. -/
theorem comparator_same_atom_projection
    {treeLo treeHi a b depth n : ℕ} {before after : BST treeLo treeHi}
    (step : GreedyMerge.KeyRotationAt a b depth before after)
    (cut owner owner' : ℕ → ℕ) (hcut : StrictMono cut)
    (hl : 2 * treeLo ≤ cut 0) (hu : cut (2 * n + 1) - 1 ≤ 2 * treeHi)
    (owners : AtomOwners before.externalDepth cut owner (2 * n + 1))
    (owners' : AtomOwners after.externalDepth cut owner' (2 * n + 1))
    (hsame : locate cut hcut (2 * a + 1) = locate cut hcut (2 * b + 1))
    (first second : BST 0 n)
    (hf : Canonical (fun atom => before.externalDepth (owner atom)) first)
    (hs : Canonical (fun atom => after.externalDepth (owner' atom)) second) :
    first = second :=
  same_atom_projection_eq hcut owners owners'
    (recordChanges_of_keyRotation step hl hu) hsame first second hf hs

end GreedyMerge.ComparatorAtoms

#print axioms GreedyMerge.ComparatorAtoms.comparator_projection_rotations
#print axioms GreedyMerge.ComparatorAtoms.comparator_same_atom_projection
