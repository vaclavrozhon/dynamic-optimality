import Splay.Accounting.ComparisonRotationJunctionBound
import Splay.Accounting.ComparisonRotationSupport
import Mathlib.Tactic

/-! The actual canonical active representatives and their comparison-rotation turnover.
This branch is independent of the already complete improved-factor endpoint. -/

namespace Splay.Research.CanonicalActive

open Splay.Rank Splay.Tree Splay.Lazy.Canonical
open Splay.Accounting.JunctionBendReduction

def activeAt {n : ℕ} (key : Fin n) (branch : TernaryBranch) : Finset (Fin n) :=
  if branch = .middle then {key} else ∅

noncomputable def activeFrom {n lower upper : ℕ} (snapshot : Snapshot n)
    (tree : BST lower upper) (upper_le_n : upper ≤ n) : Finset (Fin n) :=
  match tree with
  | .empty _ => ∅
  | .node (root := root) left right =>
      let node : AtNode n := { lower, root, upper, left, right, upper_le_n }
      let key : Fin n := ⟨root, by have := right.lower_le_upper; omega⟩
      activeAt key (node.heavyBranch snapshot) ∪
        (activeFrom snapshot left (by have := right.lower_le_upper; omega) ∪
         activeFrom snapshot right upper_le_n)
termination_by tree.size
decreasing_by all_goals simp [BST.size] <;> omega

noncomputable def active {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n) : Finset (Fin n) :=
  activeFrom snapshot tree (le_refl n)

theorem card_union_sdiff_union_le {α : Type*} [DecidableEq α]
    (a b c d : Finset α) :
    ((a ∪ b) \ (c ∪ d)).card ≤ (a \ c).card + (b \ d).card := by
  have subset : (a ∪ b) \ (c ∪ d) ⊆ (a \ c) ∪ (b \ d) := by
    intro x member
    simp only [Finset.mem_sdiff, Finset.mem_union] at member ⊢
    tauto
  exact (Finset.card_le_card subset).trans (Finset.card_union_le _ _)

theorem activeAt_difference_le_change {n : ℕ} (key : Fin n) (before after : TernaryBranch) :
    (activeAt key before \ activeAt key after).card ≤
      if before = after then 0 else 1 := by
  by_cases equal : before = after
  · simp [equal]
  · rw [if_neg equal]
    have subset : activeAt key before \ activeAt key after ⊆ activeAt key before := Finset.sdiff_subset
    have one : (activeAt key before).card ≤ 1 := by
      unfold activeAt
      split_ifs <;> simp
    exact (Finset.card_le_card subset).trans one

theorem activeFrom_difference_le_junctionCount {n lower upper : ℕ}
    (before after : Snapshot n) (tree : BST lower upper) (upper_le_n : upper ≤ n) :
    (activeFrom before tree upper_le_n \ activeFrom after tree upper_le_n).card ≤
      junctionCountFrom before after tree upper_le_n := by
  induction tree with
  | empty boundary => simp [activeFrom, junctionCountFrom]
  | @node lower root upper left right ihLeft ihRight =>
      let node : AtNode n := { lower, root, upper, left, right, upper_le_n }
      let key : Fin n := ⟨root, by have := right.lower_le_upper; omega⟩
      have left_le_n : root ≤ n := by have := right.lower_le_upper; omega
      have localBound := activeAt_difference_le_change key (node.heavyBranch before) (node.heavyBranch after)
      have leftBound := ihLeft left_le_n
      have rightBound := ihRight upper_le_n
      have childrenBound := card_union_sdiff_union_le
        (activeFrom before left left_le_n) (activeFrom before right upper_le_n)
        (activeFrom after left left_le_n) (activeFrom after right upper_le_n)
      have unionBound := card_union_sdiff_union_le
        (activeAt key (node.heavyBranch before))
        (activeFrom before left left_le_n ∪ activeFrom before right upper_le_n)
        (activeAt key (node.heavyBranch after))
        (activeFrom after left left_le_n ∪ activeFrom after right upper_le_n)
      simp only [activeFrom, junctionCountFrom]
      change ((activeAt key (node.heavyBranch before) ∪
          (activeFrom before left left_le_n ∪ activeFrom before right upper_le_n)) \
        (activeAt key (node.heavyBranch after) ∪
          (activeFrom after left left_le_n ∪ activeFrom after right upper_le_n))).card ≤
        (if node.heavyBranch before = node.heavyBranch after then 0 else 1) +
          junctionCountFrom before after left left_le_n +
          junctionCountFrom before after right upper_le_n
      omega

theorem comparison_rotation_loses_at_most_one {n depth : ℕ}
    {before after tree : BST 0 n} (rotation : BST.RotationAt depth before after) :
    (active (Snapshot.ofTree before) tree \ active (Snapshot.ofTree after) tree).card ≤ 1 := by
  exact (activeFrom_difference_le_junctionCount _ _ tree (le_refl n)).trans
    (Splay.Accounting.ComparisonRotationJunctionBound.RotationAt.junctionCount_le_one rotation)

theorem doubled_comparison_rotation_loses_at_most_one {n depth : ℕ}
    {before after tree : BST 0 n} (rotation : BST.RotationAt depth before after) :
    (active (Snapshot.ofTree before).withTruePriority tree \
      active (Snapshot.ofTree after).withTruePriority tree).card ≤ 1 := by
  exact (activeFrom_difference_le_junctionCount _ _ tree (le_refl n)).trans
    (Splay.Accounting.ComparisonRotationJunctionBound.RotationAt.doubled_junctionCount_le_one rotation)

end Splay.Research.CanonicalActive

#print axioms Splay.Research.CanonicalActive.comparison_rotation_loses_at_most_one
#print axioms Splay.Research.CanonicalActive.doubled_comparison_rotation_loses_at_most_one
