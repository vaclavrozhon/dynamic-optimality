import ComparatorAtoms
import AtomRotationMin

/-!
The external-record convention introduces no new owner in a nonempty real
key interval. Its unique minimum record is precisely the odd record of the
ordinary comparator minimum. This identifies the ranks in the canonical
hierarchy formalization with the candidate's real-key neighborhood ranks.
-/
namespace GreedyMerge.ExternalRealMin
open Splay.Tree
open Splay.Tree.BST
open GreedyMerge.IntervalRootOracle
open GreedyMerge.ComparatorAtoms

@[simp] theorem externalDepth_real {lo hi : ℕ} (tree : BST lo hi) (key : ℕ) :
    tree.externalDepth (2 * key + 1) = tree.depth key := by
  induction tree with
  | empty => rfl
  | @node lo root hi left right ihLeft ihRight =>
      by_cases hl : key < root
      · rw [externalDepth_node_of_lt_root left right (by omega),
          depth_node_of_lt_root left right hl, ihLeft]
      · by_cases heq : key = root
        · subst key
          simp
        · rw [externalDepth_node_of_root_lt left right (by omega),
            depth_node_of_root_lt left right (by omega), ihRight]

/-- Adding the null records of a nonempty real interval preserves its
minimum owner, including nulls at both ends of that interval. -/
theorem intervalMin_external_of_real {treeLo treeHi lo hi key : ℕ}
    (tree : BST treeLo treeHi) (hl : treeLo ≤ lo) (hu : hi ≤ treeHi)
    (hne : lo < hi) (hmin : IsIntervalMin tree.depth lo (hi - 1) key) :
    IsIntervalMin tree.externalDepth (2 * lo) (2 * hi) (2 * key + 1) := by
  induction tree with
  | empty => omega
  | @node treeLo root treeHi left right ihLeft ihRight =>
      by_cases hleft : hi ≤ root
      · apply (GreedyMerge.intervalMin_node_left_iff left right (by omega)).2
        exact ihLeft hl hleft
          ((GreedyMerge.AtomRotationMin.intervalMin_node_left_iff left right (by omega)).1 hmin)
      · by_cases hright : root < lo
        · apply (GreedyMerge.intervalMin_node_right_iff left right (by omega)).2
          exact ihRight (by omega) hu
            ((GreedyMerge.AtomRotationMin.intervalMin_node_right_iff left right hright).1 hmin)
        · have heq := GreedyMerge.AtomRotationMin.intervalMin_node_eq_root
            left right (by omega) (by omega) hmin
          subst key
          exact GreedyMerge.intervalMin_node_root left right (by omega) (by omega)

theorem intervalMin_real_of_external {treeLo treeHi lo hi key : ℕ}
    (tree : BST treeLo treeHi)
    (hmin : IsIntervalMin tree.externalDepth (2 * lo) (2 * hi) (2 * key + 1)) :
    IsIntervalMin tree.depth lo (hi - 1) key := by
  have hkl := hmin.1
  have hku := hmin.2.1
  refine ⟨by omega, by omega, ?_⟩
  intro other hol hou
  have h := hmin.2.2 (2 * other + 1) (by omega) (by omega)
  simpa only [externalDepth_real] using h

theorem uniqueMin_external_of_real {treeLo treeHi lo hi key : ℕ}
    (tree : BST treeLo treeHi) (hl : treeLo ≤ lo) (hu : hi ≤ treeHi)
    (hne : lo < hi) (hmin : IsIntervalMin tree.depth lo (hi - 1) key) :
    UniqueMin tree.externalDepth (2 * lo) (2 * hi) (2 * key + 1) := by
  obtain ⟨record, hm⟩ := exists_uniqueMin_external tree (by omega : 2 * treeLo ≤ 2 * lo)
    (by omega : 2 * lo ≤ 2 * hi) (by omega : 2 * hi ≤ 2 * treeHi)
  have hr := intervalMin_external_of_real tree hl hu hne hmin
  have heq : record = 2 * key + 1 := (GreedyMerge.SharpProjection.eq_of_isMin hm hr).symm
  exact heq ▸ hm

/-- Every external owner on a nonempty real interval is a real owner. -/
theorem external_min_is_real {treeLo treeHi lo hi record : ℕ}
    (tree : BST treeLo treeHi) (hl : treeLo ≤ lo) (hu : hi ≤ treeHi)
    (hne : lo < hi) (hm : IsIntervalMin tree.externalDepth (2 * lo) (2 * hi) record) :
    ∃ key, IsIntervalMin tree.depth lo (hi - 1) key ∧ record = 2 * key + 1 := by
  obtain ⟨key, hkey, _⟩ := tree.existsUnique_intervalDepthMin hl (by omega : lo ≤ hi - 1)
    (by omega : hi - 1 < treeHi)
  have hx := uniqueMin_external_of_real tree hl hu hne hkey
  exact ⟨key, hkey, GreedyMerge.SharpProjection.eq_of_isMin hx hm⟩

end GreedyMerge.ExternalRealMin
#print axioms GreedyMerge.ExternalRealMin.intervalMin_external_of_real
#print axioms GreedyMerge.ExternalRealMin.external_min_is_real
