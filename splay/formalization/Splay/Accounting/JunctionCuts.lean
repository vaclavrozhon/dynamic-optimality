import Splay.Accounting.JunctionEdgeCorrespondence
import Splay.Lazy.CanonicalAttachmentLocation

namespace Splay.Accounting.JunctionBendReduction

open Splay.Rank Splay.Tree Splay.Lazy.Canonical

/-- Four symmetric-order cuts per junction separate its external interval
from its surroundings and separate its three outgoing ternary branches. -/
noncomputable def junctionCutsFrom {n lower upper : ℕ} (before after : Snapshot n)
    (tree : BST lower upper) (upper_le_n : upper ≤ n) : Finset ℕ := by
  classical
  exact match tree with
  | .empty _ => ∅
  | .node (root := root) left right =>
      let node : AtNode n := ⟨lower, root, upper, left, right, upper_le_n⟩
      (if node.heavyBranch before = node.heavyBranch after then ∅
        else {2 * lower, 2 * root + 1, 2 * root + 2, 2 * upper + 1}) ∪
        junctionCutsFrom before after left (by have := right.lower_le_upper; omega) ∪
        junctionCutsFrom before after right upper_le_n

theorem junctionCutsFrom_card_le {n lower upper : ℕ} (before after : Snapshot n)
    (tree : BST lower upper) (upper_le_n : upper ≤ n) :
    (junctionCutsFrom before after tree upper_le_n).card ≤ 4 * junctionCountFrom before after tree upper_le_n := by
  classical
  induction tree with
  | empty => simp [junctionCutsFrom, junctionCountFrom]
  | @node lower root upper left right ihLeft ihRight =>
      let node : AtNode n := ⟨lower, root, upper, left, right, upper_le_n⟩
      have leftBound : root ≤ n := by have := right.lower_le_upper; omega
      let localCuts : Finset ℕ := if node.heavyBranch before = node.heavyBranch after then ∅
        else {2 * lower, 2 * root + 1, 2 * root + 2, 2 * upper + 1}
      have localBound : localCuts.card ≤ 4 * (if node.heavyBranch before = node.heavyBranch after then 0 else 1) := by
        unfold localCuts
        split
        · simp
        · have a := Finset.card_insert_le (2 * lower) {2 * root + 1, 2 * root + 2, 2 * upper + 1}
          have b := Finset.card_insert_le (2 * root + 1) {2 * root + 2, 2 * upper + 1}
          have c := Finset.card_insert_le (2 * root + 2) {2 * upper + 1}
          simp only [Finset.card_singleton] at c
          omega
      have unionBound := Finset.card_union_le (localCuts ∪ junctionCutsFrom before after left leftBound)
        (junctionCutsFrom before after right upper_le_n)
      have prefixBound := Finset.card_union_le localCuts (junctionCutsFrom before after left leftBound)
      have l := ihLeft leftBound
      have r := ihRight upper_le_n
      rw [junctionCountFrom]
      change (localCuts ∪ junctionCutsFrom before after left leftBound ∪ junctionCutsFrom before after right upper_le_n).card ≤
        4 * ((if node.heavyBranch before = node.heavyBranch after then 0 else 1) +
          junctionCountFrom before after left leftBound + junctionCountFrom before after right upper_le_n)
      omega

theorem junctionCutsFrom_comm {n lower upper : ℕ} (before after : Snapshot n)
    (tree : BST lower upper) (upper_le_n : upper ≤ n) :
    junctionCutsFrom before after tree upper_le_n = junctionCutsFrom after before tree upper_le_n := by
  classical
  induction tree with
  | empty => rfl
  | @node lower root upper left right ihLeft ihRight =>
      simp only [junctionCutsFrom, ihLeft, ihRight]
      split_ifs <;> grind

/-- External positions belong to the same cell of a finite numerical cut
set precisely when every cut is on the same side of both positions. -/
def SameCutCell {n : ℕ} (cuts : Finset ℕ) (first second : External n) : Prop :=
  ∀ cut ∈ cuts, first.val < cut ↔ second.val < cut

namespace SameCutCell

theorem symm {n : ℕ} {cuts : Finset ℕ} {first second : External n}
    (same : SameCutCell cuts first second) : SameCutCell cuts second first :=
  fun cut member => (same cut member).symm

theorem mono {n : ℕ} {small large : Finset ℕ} {first second : External n}
    (same : SameCutCell large first second) (subset : small ⊆ large) : SameCutCell small first second :=
  fun cut member => same cut (subset member)

/-- A cut cell contains every numerical position between two of its members. -/
theorem between {n : ℕ} {cuts : Finset ℕ} {first second middle : External n}
    (same : SameCutCell cuts first second)
    (inside : first.val ≤ middle.val ∧ middle.val ≤ second.val ∨
      second.val ≤ middle.val ∧ middle.val ≤ first.val) :
    SameCutCell cuts first middle := by
  intro cut member
  have endpoints := same cut member
  omega

end SameCutCell

/-- An external reference and an internal child in the same junction cut
cell rule out a junction at the subtree root. Its outer cut would separate
those two positions. -/
theorem heavyBranch_eq_of_sameCutCell_outside {n lower root upper : ℕ}
    (before after : Snapshot n) (left : BST lower root) (right : BST (root + 1) upper)
    (upper_le_n : upper ≤ n) {reference child : External n}
    (outside : reference.val < 2 * lower ∨ 2 * upper < reference.val)
    (inside : 2 * lower ≤ child.val ∧ child.val ≤ 2 * upper)
    (same : SameCutCell (junctionCutsFrom before after (.node left right) upper_le_n) reference child) :
    let node : AtNode n := ⟨lower, root, upper, left, right, upper_le_n⟩
    node.heavyBranch before = node.heavyBranch after := by
  classical
  dsimp only
  let node : AtNode n := ⟨lower, root, upper, left, right, upper_le_n⟩
  by_contra junction
  have localSubset : ({2 * lower, 2 * root + 1, 2 * root + 2, 2 * upper + 1} : Finset ℕ) ⊆
      junctionCutsFrom before after (.node left right) upper_le_n := by
    intro cut member
    apply Finset.mem_union_left
    apply Finset.mem_union_left
    change cut ∈ (if node.heavyBranch before = node.heavyBranch after then ∅ else _)
    rw [if_neg junction]
    exact member
  rcases outside with low | high
  · have separates := same (2 * lower) (localSubset (by simp))
    omega
  · have separates := same (2 * upper + 1) (localSubset (by simp))
    omega

end Splay.Accounting.JunctionBendReduction
