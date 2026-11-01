import Splay.Tree.Basic
import Lean.Elab.Tactic.Omega

/-!
Concrete ordered-tree version of the active-record part of the harmful-link
lemma. All records in a contiguous interval have rank at least a fixed base.
In a rank min-heap BST, at most one edge can enter that interval from a parent
whose rank is below the base. The tree may itself have an external parent;
its incoming edge is included, so the induction proves the stronger statement.

This file does not construct the active Cartesian tree, handle inactive
separator leaves, or prove the dynamic block-lifetime bound.
-/

namespace GreedyMerge.HarmfulBoundary

open Splay.Tree
open Splay.Tree.BST

def Heap (rank : ℕ → ℕ) {lo hi : ℕ} : BST lo hi → Prop
  | .empty _ => True
  | .node (root := root) left right =>
      (∀ key, lo ≤ key → key < hi → rank root ≤ rank key) ∧
        Heap rank left ∧ Heap rank right

def EntryCount (rank : ℕ → ℕ) (a z base parentRank : ℕ)
    {lo hi : ℕ} : BST lo hi → ℕ
  | .empty _ => 0
  | .node (root := root) left right =>
      (if a ≤ root ∧ root < z ∧ parentRank < base then 1 else 0) +
        EntryCount rank a z base (rank root) left +
        EntryCount rank a z base (rank root) right

theorem entryCount_zero_of_left {lo hi a z base parentRank : ℕ}
    (rank : ℕ → ℕ) (tree : BST lo hi) (hoff : hi ≤ a) :
    EntryCount rank a z base parentRank tree = 0 := by
  induction tree generalizing parentRank with
  | empty => rfl
  | @node lo root hi left right ihLeft ihRight =>
      have hbound := right.lower_le_upper
      have hnot : ¬(a ≤ root ∧ root < z ∧ parentRank < base) := by omega
      simp only [EntryCount, if_neg hnot, ihLeft (by omega), ihRight hoff]

theorem entryCount_zero_of_right {lo hi a z base parentRank : ℕ}
    (rank : ℕ → ℕ) (tree : BST lo hi) (hoff : z ≤ lo) :
    EntryCount rank a z base parentRank tree = 0 := by
  induction tree generalizing parentRank with
  | empty => rfl
  | @node lo root hi left right ihLeft ihRight =>
      have hbound := left.lower_le_upper
      have hnot : ¬(a ≤ root ∧ root < z ∧ parentRank < base) := by omega
      simp only [EntryCount, if_neg hnot, ihLeft hoff, ihRight (by omega)]

theorem entryCount_zero_of_ranks_ge {lo hi a z base parentRank : ℕ}
    (rank : ℕ → ℕ) (tree : BST lo hi) (hp : base ≤ parentRank)
    (lower : ∀ key, lo ≤ key → key < hi → base ≤ rank key) :
    EntryCount rank a z base parentRank tree = 0 := by
  induction tree generalizing parentRank with
  | empty => rfl
  | @node lo root hi left right ihLeft ihRight =>
      have hlo := left.lower_le_upper
      have hhi := right.lower_le_upper
      have hr : base ≤ rank root := lower root hlo (by omega)
      have lowerLeft : ∀ key, lo ≤ key → key < root → base ≤ rank key := by
        intro key hklo hkhi
        exact lower key hklo (by omega)
      have lowerRight : ∀ key, root + 1 ≤ key → key < hi → base ≤ rank key := by
        intro key hklo hkhi
        exact lower key (by omega) hkhi
      have hnot : ¬(a ≤ root ∧ root < z ∧ parentRank < base) := by omega
      simp only [EntryCount, if_neg hnot,
        ihLeft hr lowerLeft, ihRight hr lowerRight]

/-- There is at most one incoming edge into an inorder interval from below
its rank floor. An arbitrary incoming edge of the whole tree is included. -/
theorem entryCount_le_one {lo hi a z base parentRank : ℕ}
    (rank : ℕ → ℕ) (tree : BST lo hi) (heap : Heap rank tree)
    (floor : ∀ key, lo ≤ key → key < hi → a ≤ key → key < z →
      base ≤ rank key) :
    EntryCount rank a z base parentRank tree ≤ 1 := by
  induction tree generalizing parentRank with
  | empty => simp [EntryCount]
  | @node lo root hi left right ihLeft ihRight =>
      obtain ⟨hmin, heapLeft, heapRight⟩ := heap
      have hlo := left.lower_le_upper
      have hhi := right.lower_le_upper
      have floorLeft : ∀ key, lo ≤ key → key < root → a ≤ key → key < z →
          base ≤ rank key := by
        intro key hklo hkhi hka hkz
        exact floor key hklo (by omega) hka hkz
      have floorRight : ∀ key, root + 1 ≤ key → key < hi → a ≤ key → key < z →
          base ≤ rank key := by
        intro key hklo hkhi hka hkz
        exact floor key (by omega) hkhi hka hkz
      by_cases hr : base ≤ rank root
      · have lowerLeft : ∀ key, lo ≤ key → key < root → base ≤ rank key := by
          intro key hklo hkhi
          have := hmin key hklo (by omega)
          omega
        have lowerRight : ∀ key, root + 1 ≤ key → key < hi → base ≤ rank key := by
          intro key hklo hkhi
          have := hmin key (by omega) hkhi
          omega
        have hleft := entryCount_zero_of_ranks_ge (a := a) (z := z) rank left hr lowerLeft
        have hright := entryCount_zero_of_ranks_ge (a := a) (z := z) rank right hr lowerRight
        simp only [EntryCount, hleft, hright, Nat.add_zero]
        split <;> omega
      · have hnot : ¬(a ≤ root ∧ root < z ∧ parentRank < base) := by
          intro h
          exact hr (floor root hlo (by omega) h.1 h.2.1)
        by_cases hleft : root < a
        · have off := entryCount_zero_of_left (a := a) (z := z)
            (base := base) (parentRank := rank root) rank left (by omega)
          have bound := ihRight heapRight floorRight (parentRank := rank root)
          simp only [EntryCount, if_neg hnot, off, Nat.zero_add]
          exact bound
        · have hright : z ≤ root := by
            by_contra h
            exact hr (floor root hlo (by omega) (by omega) (by omega))
          have off := entryCount_zero_of_right (a := a) (z := z)
            (base := base) (parentRank := rank root) rank right (by omega)
          have bound := ihLeft heapLeft floorLeft (parentRank := rank root)
          simp only [EntryCount, if_neg hnot, off, Nat.zero_add, Nat.add_zero]
          exact bound

end GreedyMerge.HarmfulBoundary

#print axioms GreedyMerge.HarmfulBoundary.entryCount_le_one
