import SurfaceOwners
import Splay.Tree.ExternalDepthMin

/-!
The real-key/null rank interface. A real value record inherits exactly its
ordinary comparator depth; either neighboring null is strictly deeper.
Thus the minimum real key of a nonempty key interval is also the minimum
of its complete external interval, including both boundary nulls.
-/

namespace GreedyMerge.ValueNull

open Splay.Tree
open Splay.Tree.BST

theorem value_depth_eq {lo hi : ℕ} (tree : BST lo hi) (key : ℕ) :
    tree.externalDepth (2 * key + 1) = tree.depth key := by
  induction tree with
  | empty => rfl
  | @node lo root hi left right ihLeft ihRight =>
      by_cases heq : key = root
      · subst key
        simp
      · by_cases hleft : key < root
        · rw [externalDepth_node_of_lt_root left right (by omega),
            depth_node_of_lt_root left right hleft, ihLeft]
        · have hright : root < key := by omega
          rw [externalDepth_node_of_root_lt left right (by omega),
            depth_node_of_root_lt left right hright, ihRight]

theorem before_null_deeper {lo hi key : ℕ} (tree : BST lo hi)
    (hklo : lo ≤ key) (hkhi : key < hi) :
    tree.depth key < tree.externalDepth (2 * key) := by
  induction tree with
  | empty => omega
  | @node lo root hi left right ihLeft ihRight =>
      by_cases heq : key = root
      · subst key
        rw [depth_root, externalDepth_node_of_lt_root left right (by omega)]
        omega
      · by_cases hleft : key < root
        · rw [depth_node_of_lt_root left right hleft,
            externalDepth_node_of_lt_root left right (by omega)]
          have h := ihLeft hklo hleft
          omega
        · have hright : root < key := by omega
          rw [depth_node_of_root_lt left right hright,
            externalDepth_node_of_root_lt left right (by omega)]
          have h := ihRight (by omega) hkhi
          omega

theorem after_null_deeper {lo hi key : ℕ} (tree : BST lo hi)
    (hklo : lo ≤ key) (hkhi : key < hi) :
    tree.depth key < tree.externalDepth (2 * key + 2) := by
  induction tree with
  | empty => omega
  | @node lo root hi left right ihLeft ihRight =>
      by_cases heq : key = root
      · subst key
        rw [depth_root, externalDepth_node_of_root_lt left right (by omega)]
        omega
      · by_cases hleft : key < root
        · rw [depth_node_of_lt_root left right hleft,
            externalDepth_node_of_lt_root left right (by omega)]
          have h := ihLeft hklo hleft
          omega
        · have hright : root < key := by omega
          rw [depth_node_of_root_lt left right hright,
            externalDepth_node_of_root_lt left right (by omega)]
          have h := ihRight (by omega) hkhi
          omega

theorem real_interval_min_is_external {n lo hi minimum : ℕ}
    (comparator : BST 0 n) (hne : lo < hi) (hhi : hi ≤ n)
    (hmin : IsIntervalMin comparator.depth lo (hi - 1) minimum) :
    IsIntervalMin comparator.externalDepth (2 * lo) (2 * hi) (2 * minimum + 1) := by
  have hmlo := hmin.1
  have hmhi := hmin.2.1
  refine ⟨by omega, by omega, ?_⟩
  intro position hposLo hposHi
  rw [value_depth_eq]
  by_cases heven : position % 2 = 0
  · have hposition : position = 2 * (position / 2) := by omega
    by_cases hedge : position / 2 < hi
    · have hkeyLo : lo ≤ position / 2 := by omega
      have hrank := hmin.2.2 (position / 2) hkeyLo (by omega)
      have hnull := before_null_deeper comparator (Nat.zero_le (position / 2)) (by omega)
      rw [hposition]
      omega
    · have hquot : position / 2 = hi := by omega
      have hlastLo : lo ≤ hi - 1 := by omega
      have hrank := hmin.2.2 (hi - 1) hlastLo (Nat.le_refl _)
      have hnull := after_null_deeper comparator (Nat.zero_le (hi - 1)) (by omega)
      have hlastPosition : position = 2 * (hi - 1) + 2 := by omega
      rw [hlastPosition]
      omega
  · have hposition : position = 2 * (position / 2) + 1 := by omega
    have hkeyLo : lo ≤ position / 2 := by omega
    have hkeyHi : position / 2 ≤ hi - 1 := by omega
    rw [hposition, value_depth_eq]
    exact hmin.2.2 (position / 2) hkeyLo hkeyHi

def ExactExternalOwners (externalRank owner : ℕ → ℕ) {lo hi : ℕ} : BST lo hi → Prop
  | .empty _ => True
  | .node (root := root) left right =>
      IsIntervalMin externalRank (2 * lo) (2 * hi) (2 * owner root + 1) ∧
        ExactExternalOwners externalRank owner left ∧
        ExactExternalOwners externalRank owner right

theorem exactOwners_external {n lo hi : ℕ} (comparator : BST 0 n)
    (owner : ℕ → ℕ) (tree : BST lo hi) (hhi : hi ≤ n)
    (exactOwners : Surface.ExactOwners comparator.depth owner tree) :
    ExactExternalOwners comparator.externalDepth owner tree := by
  induction tree with
  | empty => trivial
  | @node lo root hi left right ihLeft ihRight =>
      have hlo := left.lower_le_upper
      have hrhi := right.lower_le_upper
      exact ⟨real_interval_min_is_external comparator (by omega) hhi exactOwners.1,
        ihLeft (by omega) exactOwners.2.1, ihRight hhi exactOwners.2.2⟩

/-- Actual comparator depths on real and null records realize every
strict-neighborhood owner as the full ternary-subtree minimum. -/
theorem full_refinement_externalOwners {n : ℕ}
    (height : ℕ → ℤ) (comparator : BST 0 n) (owner : ℕ → ℕ) (refinement : BST 0 n)
    (owners : Surface.Owners height comparator.depth owner n)
    (refines : Surface.Refines height comparator.depth owner refinement) :
    ExactExternalOwners comparator.externalDepth owner refinement := by
  exact exactOwners_external comparator owner refinement (Nat.le_refl n)
    (Surface.full_refinement_exactOwners height comparator.depth owner refinement owners refines)

end GreedyMerge.ValueNull

#print axioms GreedyMerge.ValueNull.full_refinement_externalOwners
