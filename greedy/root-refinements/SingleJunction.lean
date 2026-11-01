import Splay.Tree.Basic
import Lean.Elab.Tactic.Omega

/-!
The geometric part of the one-junction comparator update. A fixed ternary
expansion of an ordinary BST has at most one node that separates two given
external atoms into different child branches while containing both atoms.
Consequently, if every interval owner either stays put or changes from the
same atom a to the same atom b, at most one outgoing heavy branch changes.

The interval-owner update premise is proved for concrete comparator rotations
in RotationIntervalMin.lean. This file first proves the geometry independently.
-/

namespace GreedyMerge.Junction

open Splay.Tree
open Splay.Tree.BST

def Within (lo hi position : ℕ) : Prop :=
  2 * lo ≤ position ∧ position ≤ 2 * hi

instance (lo hi position : ℕ) : Decidable (Within lo hi position) :=
  inferInstanceAs (Decidable (2 * lo ≤ position ∧ position ≤ 2 * hi))

def Branch (root position : ℕ) : ℕ :=
  if position < 2 * root + 1 then 0
  else if position = 2 * root + 1 then 1 else 2

def ForkCount (a b : ℕ) {lo hi : ℕ} : BST lo hi → ℕ
  | .empty _ => 0
  | .node (root := root) left right =>
      (if Within lo hi a ∧ Within lo hi b ∧ Branch root a ≠ Branch root b
        then 1 else 0) + ForkCount a b left + ForkCount a b right

theorem forkCount_zero_of_outside {lo hi a b : ℕ} (tree : BST lo hi)
    (hout : ¬Within lo hi a ∨ ¬Within lo hi b) :
    ForkCount a b tree = 0 := by
  induction tree with
  | empty => rfl
  | @node lo root hi left right ihLeft ihRight =>
      have hlo := left.lower_le_upper
      have hhi := right.lower_le_upper
      have hroot : ¬(Within lo hi a ∧ Within lo hi b ∧
          Branch root a ≠ Branch root b) := by
        intro hboth
        rcases hout with h | h
        · exact h hboth.1
        · exact h hboth.2.1
      have houtLeft : ¬Within lo root a ∨ ¬Within lo root b := by
        unfold Within at *
        omega
      have houtRight : ¬Within (root + 1) hi a ∨ ¬Within (root + 1) hi b := by
        unfold Within at *
        omega
      simp only [ForkCount, if_neg hroot, ihLeft houtLeft, ihRight houtRight]

theorem forkCount_le_one {lo hi a b : ℕ} (tree : BST lo hi) :
    ForkCount a b tree ≤ 1 := by
  induction tree with
  | empty => simp [ForkCount]
  | @node lo root hi left right ihLeft ihRight =>
      by_cases hleft : a ≤ 2 * root ∧ b ≤ 2 * root
      · have hsame : Branch root a = Branch root b := by
          simp [Branch, show a < 2 * root + 1 by omega,
            show b < 2 * root + 1 by omega]
        have hoff : ¬Within (root + 1) hi a := by
          unfold Within
          omega
        have hzero := forkCount_zero_of_outside (b := b) right (Or.inl hoff)
        simp only [ForkCount, hsame, ne_eq, not_true_eq_false, and_false,
          if_false, hzero, Nat.zero_add, Nat.add_zero]
        exact ihLeft
      · by_cases hright : 2 * root + 2 ≤ a ∧ 2 * root + 2 ≤ b
        · have hsame : Branch root a = Branch root b := by
            simp [Branch, show ¬a < 2 * root + 1 by omega,
              show ¬b < 2 * root + 1 by omega,
              show a ≠ 2 * root + 1 by omega,
              show b ≠ 2 * root + 1 by omega]
          have hoff : ¬Within lo root a := by
            unfold Within
            omega
          have hzero := forkCount_zero_of_outside (b := b) left (Or.inl hoff)
          simp only [ForkCount, hsame, ne_eq, not_true_eq_false, and_false,
            if_false, hzero, Nat.zero_add]
          exact ihRight
        · have hoffLeft : ¬Within lo root a ∨ ¬Within lo root b := by
            unfold Within
            omega
          have hoffRight : ¬Within (root + 1) hi a ∨ ¬Within (root + 1) hi b := by
            unfold Within
            omega
          have hzLeft := forkCount_zero_of_outside left hoffLeft
          have hzRight := forkCount_zero_of_outside right hoffRight
          simp only [ForkCount, hzLeft, hzRight, Nat.add_zero]
          split <;> omega

def JunctionCount (before after : ℕ → ℕ → ℕ) {lo hi : ℕ} : BST lo hi → ℕ
  | .empty _ => 0
  | .node (root := root) left right =>
      (if Branch root (before lo hi) ≠ Branch root (after lo hi) then 1 else 0) +
        JunctionCount before after left + JunctionCount before after right

/-- A single possible owner replacement controls every actual branch
junction in a fixed refinement, regardless of how many owners change. -/
theorem junctionCount_le_forkCount {lo hi n a b : ℕ}
    (tree : BST lo hi) (before after : ℕ → ℕ → ℕ) (hhi : hi ≤ n)
    (insideBefore : ∀ l u, l ≤ u → u ≤ n → Within l u (before l u))
    (insideAfter : ∀ l u, l ≤ u → u ≤ n → Within l u (after l u))
    (swap : ∀ l u, l ≤ u → u ≤ n →
      before l u = after l u ∨ (before l u = a ∧ after l u = b)) :
    JunctionCount before after tree ≤ ForkCount a b tree := by
  induction tree with
  | empty => simp [JunctionCount, ForkCount]
  | @node lo root hi left right ihLeft ihRight =>
      have hlo := left.lower_le_upper
      have hrhi := right.lower_le_upper
      have horder : lo ≤ hi := by omega
      have boundLeft := ihLeft (by omega : root ≤ n)
      have boundRight := ihRight hhi
      have hhead :
          (if Branch root (before lo hi) ≠ Branch root (after lo hi) then 1 else 0) ≤
          (if Within lo hi a ∧ Within lo hi b ∧ Branch root a ≠ Branch root b
            then 1 else 0) := by
        by_cases hchange : Branch root (before lo hi) ≠ Branch root (after lo hi)
        · rcases swap lo hi horder hhi with hsame | ⟨ha, hb⟩
          · exact False.elim (hchange (congrArg (Branch root) hsame))
          · have hba := insideBefore lo hi horder hhi
            have hbb := insideAfter lo hi horder hhi
            rw [ha] at hba
            rw [hb] at hbb
            have hbranches : Branch root a ≠ Branch root b := by
              simpa [ha, hb] using hchange
            simp [hchange, hba, hbb, hbranches]
        · simp [hchange]
      simp only [JunctionCount, ForkCount]
      omega

theorem junctionCount_le_one {lo hi n a b : ℕ}
    (tree : BST lo hi) (before after : ℕ → ℕ → ℕ) (hhi : hi ≤ n)
    (insideBefore : ∀ l u, l ≤ u → u ≤ n → Within l u (before l u))
    (insideAfter : ∀ l u, l ≤ u → u ≤ n → Within l u (after l u))
    (swap : ∀ l u, l ≤ u → u ≤ n →
      before l u = after l u ∨ (before l u = a ∧ after l u = b)) :
    JunctionCount before after tree ≤ 1 := by
  exact Nat.le_trans
    (junctionCount_le_forkCount tree before after hhi insideBefore insideAfter swap)
    (forkCount_le_one tree)

end GreedyMerge.Junction

#print axioms GreedyMerge.Junction.junctionCount_le_one
