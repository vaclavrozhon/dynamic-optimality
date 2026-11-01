import Splay.Tree.Basic
import Lean.Elab.Tactic.Omega

/-!
The Cartesian boundary-path part of the Greedy candidate. The trees here are
ordinary ordered BSTs with weakly heap-ordered integer labels. They may be
the active-record Cartesian tree after order-preserving renumbering.
This file does not formalize the construction of that Cartesian tree.
-/

namespace GreedyMerge.Boundary

open Splay.Tree
open Splay.Tree.BST

def Crosses (cut parent child : ℕ) : Prop :=
  (parent < cut ∧ cut ≤ child) ∨ (child < cut ∧ cut ≤ parent)

instance (cut parent child : ℕ) : Decidable (Crosses cut parent child) :=
  inferInstanceAs (Decidable ((parent < cut ∧ cut ≤ child) ∨
    (child < cut ∧ cut ≤ parent)))

def HeadBad (label : ℕ → ℕ) (cut parent : ℕ) {lo hi : ℕ} : BST lo hi → ℕ
  | .empty _ => 0
  | .node (root := root) _ _ =>
      if Crosses cut parent root ∧ label parent < label root then 1 else 0

def BadCount (label : ℕ → ℕ) (cut : ℕ) {lo hi : ℕ} : BST lo hi → ℕ
  | .empty _ => 0
  | .node (root := root) left right =>
      BadCount label cut left + BadCount label cut right +
        HeadBad label cut root left + HeadBad label cut root right

def MinHeap (label : ℕ → ℕ) {lo hi : ℕ} : BST lo hi → Prop
  | .empty _ => True
  | .node (root := root) left right =>
      (∀ key, lo ≤ key → key < hi → label root ≤ label key) ∧
        MinHeap label left ∧ MinHeap label right

def RootLabel (label : ℕ → ℕ) (emptyLabel : ℕ) {lo hi : ℕ} : BST lo hi → ℕ
  | .empty _ => emptyLabel
  | .node (root := root) _ _ => label root

theorem headBad_zero_of_left {lo hi cut parent : ℕ}
    (label : ℕ → ℕ) (tree : BST lo hi)
    (hp : parent < cut) (hhi : hi ≤ cut) :
    HeadBad label cut parent tree = 0 := by
  cases tree with
  | empty => rfl
  | @node lo root hi left right =>
      have hroot := right.lower_le_upper
      have hnot : ¬Crosses cut parent root := by
        unfold Crosses
        omega
      simp [HeadBad, hnot]

theorem headBad_zero_of_right {lo hi cut parent : ℕ}
    (label : ℕ → ℕ) (tree : BST lo hi)
    (hp : cut ≤ parent) (hlo : cut ≤ lo) :
    HeadBad label cut parent tree = 0 := by
  cases tree with
  | empty => rfl
  | @node lo root hi left right =>
      have hroot := left.lower_le_upper
      have hnot : ¬Crosses cut parent root := by
        unfold Crosses
        omega
      simp [HeadBad, hnot]

theorem badCount_zero_of_left {lo hi cut : ℕ}
    (label : ℕ → ℕ) (tree : BST lo hi) (hhi : hi ≤ cut) :
    BadCount label cut tree = 0 := by
  induction tree with
  | empty => rfl
  | @node lo root hi left right ihLeft ihRight =>
      have hrange := right.lower_le_upper
      have hr : root < cut := by omega
      have hl : root ≤ cut := by omega
      simp only [BadCount, ihLeft hl, ihRight hhi,
        headBad_zero_of_left label left hr hl,
        headBad_zero_of_left label right hr hhi]

theorem badCount_zero_of_right {lo hi cut : ℕ}
    (label : ℕ → ℕ) (tree : BST lo hi) (hlo : cut ≤ lo) :
    BadCount label cut tree = 0 := by
  induction tree with
  | empty => rfl
  | @node lo root hi left right ihLeft ihRight =>
      have hrange := left.lower_le_upper
      have hr : cut ≤ root := by omega
      have hright : cut ≤ root + 1 := by omega
      simp only [BadCount, ihLeft hlo, ihRight hright,
        headBad_zero_of_right label left hr hlo,
        headBad_zero_of_right label right hr hright]

theorem headBad_le_label_difference
    {lo root hi cut parent : ℕ} (label : ℕ → ℕ)
    (left : BST lo root) (right : BST (root + 1) hi) :
    HeadBad label cut parent (.node left right) ≤ label root - label parent := by
  change (if Crosses cut parent root ∧ label parent < label root then 1 else 0) ≤
    label root - label parent
  split
  · omega
  · omega

/-- Weak heap order limits the number of strictly label-increasing edges
crossing any one inorder cut to the available label range. -/
theorem badCount_le_range {lo hi : ℕ} (label : ℕ → ℕ) (cut K : ℕ)
    (tree : BST lo hi) (heap : MinHeap label tree)
    (upper : ∀ key, lo ≤ key → key < hi → label key ≤ K) :
    BadCount label cut tree ≤ K - RootLabel label K tree := by
  induction tree with
  | empty => simp [BadCount, RootLabel]
  | @node lo root hi left right ihLeft ihRight =>
      obtain ⟨hmin, heapLeft, heapRight⟩ := heap
      have hlo := left.lower_le_upper
      have hhi := right.lower_le_upper
      have upperLeft : ∀ key, lo ≤ key → key < root → label key ≤ K := by
        intro key hklo hkhi
        exact upper key hklo (by omega)
      have upperRight : ∀ key, root + 1 ≤ key → key < hi → label key ≤ K := by
        intro key hklo hkhi
        exact upper key (by omega) hkhi
      have boundLeft := ihLeft heapLeft upperLeft
      have boundRight := ihRight heapRight upperRight
      by_cases hcut : cut ≤ root
      · have offCount := badCount_zero_of_right label right (by omega : cut ≤ root + 1)
        have offHead := headBad_zero_of_right label right hcut (by omega : cut ≤ root + 1)
        simp only [BadCount, RootLabel, offCount, offHead, Nat.add_zero]
        cases left with
        | empty => simp [BadCount, HeadBad]
        | @node lo child root a b =>
            have hclo := a.lower_le_upper
            have hchi := b.lower_le_upper
            have hcmin : label root ≤ label child := hmin child hclo (by omega)
            have hcmax : label child ≤ K := upper child hclo (by omega)
            have hhead := headBad_le_label_difference (cut := cut) (parent := root) label a b
            simp only [RootLabel] at boundLeft
            omega
      · have hcut' : root < cut := by omega
        have offCount := badCount_zero_of_left label left (by omega : root ≤ cut)
        have offHead := headBad_zero_of_left label left hcut' (by omega : root ≤ cut)
        simp only [BadCount, RootLabel, offCount, offHead, Nat.zero_add, Nat.add_zero]
        cases right with
        | empty => simp [BadCount, HeadBad]
        | @node lower child hi a b =>
            have hclo := a.lower_le_upper
            have hchi := b.lower_le_upper
            have hcmin : label root ≤ label child := hmin child (by omega) (by omega)
            have hcmax : label child ≤ K := upper child (by omega) (by omega)
            have hhead := headBad_le_label_difference (cut := cut) (parent := root) label a b
            simp only [RootLabel] at boundRight
            omega

theorem badCount_le {lo hi : ℕ} (label : ℕ → ℕ) (cut K : ℕ)
    (tree : BST lo hi) (heap : MinHeap label tree)
    (upper : ∀ key, lo ≤ key → key < hi → label key ≤ K) :
    BadCount label cut tree ≤ K := by
  have h := badCount_le_range label cut K tree heap upper
  omega

end GreedyMerge.Boundary

#print axioms GreedyMerge.Boundary.badCount_le_range
