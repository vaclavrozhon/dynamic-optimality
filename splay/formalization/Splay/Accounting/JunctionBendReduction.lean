import Splay.Accounting.LocalBendGeometry
import Splay.Rank.Junction

namespace Splay.Accounting.JunctionBendReduction

open Splay.Rank
open Splay.Tree
open Splay.Lazy.Canonical
open Splay.Accounting.LocalBendGeometry

/--
Number of splay-tree nodes whose canonical outgoing heavy branch changes
between two rank snapshots.

This is the exact finite junction count relevant to one fixed splay-tree
shape.  It deliberately counts branch changes, not merely changes of interval
minima; `Snapshot.IsJunction.intervalMin_ne` proves the former is the
stronger, operational event.
-/
noncomputable def junctionCountFrom
    {n lower upper : ℕ} (before after : Snapshot n)
    (tree : BST lower upper) (upper_le_n : upper ≤ n) : ℕ :=
  match tree with
  | .empty _ => 0
  | .node (root := root) left right =>
      let node : AtNode n := {
        lower := lower
        root := root
        upper := upper
        left := left
        right := right
        upper_le_n := upper_le_n
      }
      (if node.heavyBranch before = node.heavyBranch after
        then 0 else 1) +
        junctionCountFrom before after left (by
          have hRight := right.lower_le_upper
          omega) +
        junctionCountFrom before after right upper_le_n
termination_by tree.size
decreasing_by
  all_goals simp [BST.size] <;> omega

/-- Complete-tree junction count. -/
noncomputable def junctionCount
    {n : ℕ} (before after : Snapshot n)
    (tree : BST 0 n) : ℕ :=
  junctionCountFrom before after tree (Nat.le_refl n)

/--
A set difference through an intermediate set is bounded by the two
successive differences.
-/
theorem card_sdiff_trans_le
    {α : Type*} [DecidableEq α]
    (first middle final : Finset α) :
    (final \ first).card ≤
      (final \ middle).card + (middle \ first).card := by
  have subset :
      final \ first ⊆
        (final \ middle) ∪ (middle \ first) := by
    intro element member
    simp only [Finset.mem_sdiff, Finset.mem_union] at member ⊢
    by_cases inMiddle : element ∈ middle
    · exact Or.inr ⟨inMiddle, member.2⟩
    · exact Or.inl ⟨member.1, inMiddle⟩
  exact
    (Finset.card_le_card subset).trans
      (Finset.card_union_le _ _)

/--
Changing the rank snapshot can create at most three bends per actual heavy
branch junction.

At one junction, at most the node's own bend and the incoming-edge status of
its two children change.  The latter two changes cost at most one bend each;
all deeper changes are charged recursively to deeper junctions.
-/
theorem created_le_three_mul_junctionCountFrom
    {n lower upper : ℕ} (before after : Snapshot n)
    (tree : BST lower upper) (upper_le_n : upper ≤ n)
    (incoming : Option TernaryBranch) :
    ((bendsFrom after tree upper_le_n incoming) \
      (bendsFrom before tree upper_le_n incoming)).card ≤
        3 * junctionCountFrom before after tree upper_le_n := by
  induction tree generalizing incoming with
  | empty boundary =>
      simp [bendsFrom, junctionCountFrom]
  | @node lower root upper left right ihLeft ihRight =>
      let node : AtNode n := {
        lower := lower
        root := root
        upper := upper
        left := left
        right := right
        upper_le_n := upper_le_n
      }
      let beforeBranch := node.heavyBranch before
      let afterBranch := node.heavyBranch after
      let key : Fin n := ⟨root, by
        have hRight := right.lower_le_upper
        omega⟩
      have left_le_n : root ≤ n := by
        have hRight := right.lower_le_upper
        omega
      by_cases branchEq : beforeBranch = afterBranch
      · have leftBound :=
          ihLeft left_le_n (childIncoming beforeBranch .left)
        have rightBound :=
          ihRight upper_le_n (childIncoming beforeBranch .right)
        simp only [bendsFrom, junctionCountFrom]
        change
          ((bendAt key incoming afterBranch ∪
                (bendsFrom after left left_le_n
                    (childIncoming afterBranch .left) ∪
                  bendsFrom after right upper_le_n
                    (childIncoming afterBranch .right))) \
            (bendAt key incoming beforeBranch ∪
                (bendsFrom before left left_le_n
                    (childIncoming beforeBranch .left) ∪
                  bendsFrom before right upper_le_n
                    (childIncoming beforeBranch .right)))).card ≤
            3 *
              ((if beforeBranch = afterBranch then 0 else 1) +
                junctionCountFrom before after left left_le_n +
                junctionCountFrom before after right upper_le_n)
        rw [branchEq]
        simp only [ite_true, zero_add]
        rw [branchEq] at leftBound rightBound
        have commonBound :
            ((bendAt key incoming afterBranch ∪
                  (bendsFrom after left left_le_n
                      (childIncoming afterBranch .left) ∪
                    bendsFrom after right upper_le_n
                      (childIncoming afterBranch .right))) \
              (bendAt key incoming afterBranch ∪
                  (bendsFrom before left left_le_n
                      (childIncoming afterBranch .left) ∪
                    bendsFrom before right upper_le_n
                      (childIncoming afterBranch .right)))).card ≤
              ((bendsFrom after left left_le_n
                    (childIncoming afterBranch .left) ∪
                  bendsFrom after right upper_le_n
                    (childIncoming afterBranch .right)) \
                (bendsFrom before left left_le_n
                    (childIncoming afterBranch .left) ∪
                  bendsFrom before right upper_le_n
                    (childIncoming afterBranch .right))).card := by
          simpa only [Finset.union_comm] using
            card_sdiff_union_same_le
              (bendsFrom after left left_le_n
                  (childIncoming afterBranch .left) ∪
                bendsFrom after right upper_le_n
                  (childIncoming afterBranch .right))
              (bendsFrom before left left_le_n
                  (childIncoming afterBranch .left) ∪
                bendsFrom before right upper_le_n
                  (childIncoming afterBranch .right))
              (bendAt key incoming afterBranch)
        have children :=
          card_sdiff_union_le_add
            (bendsFrom after left left_le_n
              (childIncoming afterBranch .left))
            (bendsFrom after right upper_le_n
              (childIncoming afterBranch .right))
            (bendsFrom before left left_le_n
              (childIncoming afterBranch .left))
            (bendsFrom before right upper_le_n
              (childIncoming afterBranch .right))
        exact commonBound.trans (children.trans (by omega))
      · have branchNe : beforeBranch ≠ afterBranch := branchEq
        have leftIncoming :=
          bendsFrom_sdiff_le_one after left left_le_n
            (childIncoming afterBranch .left)
            (childIncoming beforeBranch .left)
        have rightIncoming :=
          bendsFrom_sdiff_le_one after right upper_le_n
            (childIncoming afterBranch .right)
            (childIncoming beforeBranch .right)
        have leftSnapshot :=
          ihLeft left_le_n (childIncoming beforeBranch .left)
        have rightSnapshot :=
          ihRight upper_le_n (childIncoming beforeBranch .right)
        have leftBound :=
          (card_sdiff_trans_le
            (bendsFrom before left left_le_n
              (childIncoming beforeBranch .left))
            (bendsFrom after left left_le_n
              (childIncoming beforeBranch .left))
            (bendsFrom after left left_le_n
              (childIncoming afterBranch .left))).trans
            (Nat.add_le_add leftIncoming leftSnapshot)
        have rightBound :=
          (card_sdiff_trans_le
            (bendsFrom before right upper_le_n
              (childIncoming beforeBranch .right))
            (bendsFrom after right upper_le_n
              (childIncoming beforeBranch .right))
            (bendsFrom after right upper_le_n
              (childIncoming afterBranch .right))).trans
            (Nat.add_le_add rightIncoming rightSnapshot)
        simp only [bendsFrom, junctionCountFrom]
        change
          ((bendAt key incoming afterBranch ∪
                (bendsFrom after left left_le_n
                    (childIncoming afterBranch .left) ∪
                  bendsFrom after right upper_le_n
                    (childIncoming afterBranch .right))) \
            (bendAt key incoming beforeBranch ∪
                (bendsFrom before left left_le_n
                    (childIncoming beforeBranch .left) ∪
                  bendsFrom before right upper_le_n
                    (childIncoming beforeBranch .right)))).card ≤
            3 *
              ((if beforeBranch = afterBranch then 0 else 1) +
                junctionCountFrom before after left left_le_n +
                junctionCountFrom before after right upper_le_n)
        simp only [branchNe, ite_false]
        have rootAndChildren :=
          card_sdiff_union_le_add
            (bendAt key incoming afterBranch)
            (bendsFrom after left left_le_n
                (childIncoming afterBranch .left) ∪
              bendsFrom after right upper_le_n
                (childIncoming afterBranch .right))
            (bendAt key incoming beforeBranch)
            (bendsFrom before left left_le_n
                (childIncoming beforeBranch .left) ∪
              bendsFrom before right upper_le_n
                (childIncoming beforeBranch .right))
        have rootBound :
            (bendAt key incoming afterBranch \
              bendAt key incoming beforeBranch).card ≤ 1 :=
          (card_sdiff_le_card_left _ _).trans
            (bendAt_card_le_one _ _ _)
        have children :=
          card_sdiff_union_le_add
            (bendsFrom after left left_le_n
              (childIncoming afterBranch .left))
            (bendsFrom after right upper_le_n
              (childIncoming afterBranch .right))
            (bendsFrom before left left_le_n
              (childIncoming beforeBranch .left))
            (bendsFrom before right upper_le_n
              (childIncoming beforeBranch .right))
        exact rootAndChildren.trans
          ((Nat.add_le_add rootBound
            (children.trans (Nat.add_le_add leftBound rightBound))).trans
              (by omega))

/-- Complete-tree form of the three-bends-per-junction reduction. -/
theorem created_le_three_mul_junctionCount
    {n : ℕ} (before after : Snapshot n)
    (tree : BST 0 n) :
    ((bends after tree) \ (bends before tree)).card ≤
      3 * junctionCount before after tree := by
  simpa [bends, junctionCount] using
    created_le_three_mul_junctionCountFrom
      before after tree (Nat.le_refl n) none

end Splay.Accounting.JunctionBendReduction
