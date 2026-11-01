import CanonicalActiveRepresentatives
import Splay.Tree.SplayExecution

namespace Splay.Research.CanonicalActive

open Splay.Rank Splay.Tree Splay.Tree.BST Splay.Lazy.Canonical

theorem activeAt_of_zero {n : ℕ} (snapshot : Snapshot n) (node : AtNode n)
    (key : Fin n) (rankZero : snapshot.rank (valuePos key) = 0)
    (insideLower : node.lower ≤ key.val) (insideUpper : key.val < node.upper) :
    activeAt ⟨node.root, lt_of_lt_of_le node.root_lt_upper node.upper_le_n⟩
      (node.heavyBranch snapshot) = if node.root = key.val then {key} else ∅ := by
  have inside : node.wholeLower ≤ valuePos key ∧ valuePos key ≤ node.wholeUpper := by
    change 2*node.lower ≤ 2*key.val+1 ∧ 2*key.val+1 ≤ 2*node.upper
    omega
  by_cases equal : node.root = key.val
  · have heavy := node.heavyBranch_eq_of_rank_eq_zero snapshot .middle (valuePos key)
      rankZero inside (by change 2*key.val+1 = 2*node.root+1; omega)
    simp only [heavy, activeAt, ite_true, equal]
  · by_cases left : key.val < node.root
    · have heavy := node.heavyBranch_eq_of_rank_eq_zero snapshot .left (valuePos key)
        rankZero inside (by change 2*key.val+1 ≤ 2*node.root; omega)
      simp [heavy, activeAt, equal]
    · have heavy := node.heavyBranch_eq_of_rank_eq_zero snapshot .right (valuePos key)
        rankZero inside (by change 2*node.root+2 ≤ 2*key.val+1; omega)
      simp [heavy, activeAt, equal]

theorem activeFrom_node_of_zero {n lower root upper : ℕ} (snapshot : Snapshot n)
    (key : Fin n) (rankZero : snapshot.rank (valuePos key) = 0)
    (left : BST lower root) (right : BST (root+1) upper) (upper_le_n : upper ≤ n)
    (insideLower : lower ≤ key.val) (insideUpper : key.val < upper) :
    activeFrom snapshot (.node left right) upper_le_n =
      (if root = key.val then {key} else ∅) ∪
        (activeFrom snapshot left (by have := right.lower_le_upper; omega) ∪
         activeFrom snapshot right upper_le_n) := by
  let node : AtNode n := { lower, root, upper, left, right, upper_le_n }
  have head := activeAt_of_zero snapshot node key rankZero insideLower insideUpper
  simpa only [activeFrom] using congrArg
    (fun head => head ∪ (activeFrom snapshot left (by have := right.lower_le_upper; omega) ∪
      activeFrom snapshot right upper_le_n)) head

theorem doubleRotation_active_monotone {n lower upper : ℕ} (snapshot : Snapshot n)
    (key : Fin n) (rankZero : snapshot.rank (valuePos key) = 0)
    {before after : BST lower upper} (step : DoubleRotation key.val before after)
    (upper_le_n : upper ≤ n) :
    activeFrom snapshot before upper_le_n ⊆ activeFrom snapshot after upper_le_n := by
  cases step with
  | zigZigLeft a b c d | zigZigRight a b c d | zigZagLeftRight a b c d | zigZagRightLeft a b c d =>
    have ha := a.lower_le_upper
    have hb := b.lower_le_upper
    have hc := c.lower_le_upper
    have hd := d.lower_le_upper
    simp (discharger := omega) only [activeFrom_node_of_zero snapshot key rankZero]
    simp (discharger := omega) only [ite_true, ite_false]
    simp only [activeFrom]
    intro element member
    simp only [Finset.mem_union, Finset.mem_singleton, Finset.notMem_empty] at member ⊢
    aesop

theorem zig_active_monotone {n lower upper : ℕ} (snapshot : Snapshot n)
    (key : Fin n) (rankZero : snapshot.rank (valuePos key) = 0)
    {before after : BST lower upper} (step : Zig key.val before after)
    (upper_le_n : upper ≤ n) :
    activeFrom snapshot before upper_le_n ⊆ activeFrom snapshot after upper_le_n := by
  cases step with
  | fromLeft a b c | fromRight a b c =>
    have ha := a.lower_le_upper
    have hb := b.lower_le_upper
    have hc := c.lower_le_upper
    simp (discharger := omega) only [activeFrom_node_of_zero snapshot key rankZero]
    simp (discharger := omega) only [ite_true, ite_false]
    simp only [activeFrom]
    intro element member
    simp only [Finset.mem_union, Finset.mem_singleton, Finset.notMem_empty] at member ⊢
    aesop

theorem activeFrom_leftContext_mono {n lower root upper : ℕ} (snapshot : Snapshot n)
    {before after : BST lower root} (right : BST (root+1) upper) (upper_le_n : upper ≤ n)
    (child : activeFrom snapshot before (by have := right.lower_le_upper; omega) ⊆
      activeFrom snapshot after (by have := right.lower_le_upper; omega)) :
    activeFrom snapshot (.node before right) upper_le_n ⊆
      activeFrom snapshot (.node after right) upper_le_n := by
  simp only [activeFrom]
  exact Finset.union_subset_union (le_refl _) (Finset.union_subset_union child (le_refl _))

theorem activeFrom_rightContext_mono {n lower root upper : ℕ} (snapshot : Snapshot n)
    (left : BST lower root) {before after : BST (root+1) upper} (upper_le_n : upper ≤ n)
    (child : activeFrom snapshot before upper_le_n ⊆ activeFrom snapshot after upper_le_n) :
    activeFrom snapshot (.node left before) upper_le_n ⊆
      activeFrom snapshot (.node left after) upper_le_n := by
  simp only [activeFrom]
  exact Finset.union_subset_union (le_refl _) (Finset.union_subset_union (le_refl _) child)

theorem doubleRotationAt_active_monotone {n lower upper depth : ℕ} (snapshot : Snapshot n)
    (key : Fin n) (rankZero : snapshot.rank (valuePos key) = 0)
    {before after : BST lower upper} (step : DoubleRotationAt depth key.val before after)
    (upper_le_n : upper ≤ n) :
    activeFrom snapshot before upper_le_n ⊆ activeFrom snapshot after upper_le_n := by
  generalize keyEq : key.val = queried at step
  induction step with
  | root step =>
    exact doubleRotation_active_monotone snapshot key rankZero (by simpa only [keyEq] using step) upper_le_n
  | leftContext step right ih =>
    exact activeFrom_leftContext_mono snapshot right upper_le_n (ih (by
      have := right.lower_le_upper
      omega) keyEq)
  | rightContext left step ih =>
    exact activeFrom_rightContext_mono snapshot left upper_le_n (ih upper_le_n keyEq)

theorem splayStep_active_monotone {n lower upper : ℕ} (snapshot : Snapshot n)
    (key : Fin n) (rankZero : snapshot.rank (valuePos key) = 0)
    {before after : BST lower upper} (step : SplayStep key.val before after)
    (upper_le_n : upper ≤ n) :
    activeFrom snapshot before upper_le_n ⊆ activeFrom snapshot after upper_le_n := by
  cases step with
  | zig step => exact zig_active_monotone snapshot key rankZero step upper_le_n
  | double step => exact doubleRotationAt_active_monotone snapshot key rankZero step upper_le_n

/-- The full actual bottom-up splay trace preserves every previously active key. -/
theorem splayExecution_active_monotone {n lower upper : ℕ} (snapshot : Snapshot n)
    (key : Fin n) (rankZero : snapshot.rank (valuePos key) = 0)
    {before after : BST lower upper} (execution : SplayExecution key.val before after)
    (upper_le_n : upper ≤ n) :
    activeFrom snapshot before upper_le_n ⊆ activeFrom snapshot after upper_le_n := by
  induction execution with
  | done root => exact le_refl _
  | next head tail ih =>
    exact (splayStep_active_monotone snapshot key rankZero head upper_le_n).trans ih

end Splay.Research.CanonicalActive

#print axioms Splay.Research.CanonicalActive.doubleRotation_active_monotone
#print axioms Splay.Research.CanonicalActive.zig_active_monotone
#print axioms Splay.Research.CanonicalActive.splayExecution_active_monotone
