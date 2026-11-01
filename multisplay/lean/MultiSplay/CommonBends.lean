import MultiSplay.JoinRanks
import Splay.Accounting.LocalBendGeometry

/-!
# Exact bend conservation at common roots

A bend is a change between left and right directions along one heavy path.
At a common comparison/splay root the heavy branch is the root's own key, so
both children start fresh heavy paths. Joining and splitting therefore preserve
the sum of the two child bend counts exactly.
-/

namespace MultiSplay.CommonBends

open Splay.Rank (Snapshot TernaryBranch)
open Splay.Lazy.Canonical
open Splay.Accounting.LocalBendGeometry

variable {n m l r : Nat}

def keyEmbedding (offset : Nat) (fits : offset+n ≤ m) : Fin n ↪ Fin m where
  toFun := fun key => ⟨offset + key.val, by omega⟩
  inj' := by intro x y same; apply Fin.ext; have := congrArg Fin.val same; dsimp at this; omega

theorem bendAt_map (offset : Nat) (fits : offset+n ≤ m) (key : Fin n)
    (incoming : Option TernaryBranch) (outgoing : TernaryBranch) :
    (bendAt key incoming outgoing).map (keyEmbedding offset fits) =
      bendAt (keyEmbedding offset fits key) incoming outgoing := by
  unfold bendAt
  split <;> simp

theorem bendsFrom_map (offset delta : Nat) (fits : offset+n ≤ m)
    (before : Snapshot n) (after : Snapshot m)
    (ranks : ∀ position, after.rank (RankEmbedding.external offset fits position) = before.rank position + delta)
    {lower upper : Nat} (source : Splay.Tree.BST lower upper) (inside : upper ≤ n)
    (incoming : Option TernaryBranch) :
    bendsFrom after (OrdinalShift.tree offset source) (by omega) incoming =
      (bendsFrom before source inside incoming).map (keyEmbedding offset fits) := by
  induction source generalizing incoming with
  | empty => simp [OrdinalShift.tree, bendsFrom]
  | @node lower root upper left right ihl ihr =>
      let current : AtNode n := ⟨lower, root, upper, left, right, inside⟩
      have bound : root ≤ n := by have := right.lower_le_upper; omega
      have heavy := RankEmbedding.heavyBranch offset delta fits before after ranks current
      simp only [OrdinalShift.tree, bendsFrom, Finset.map_union, bendAt_map]
      change bendAt _ incoming ((RankEmbedding.node offset fits current).heavyBranch after) ∪
        (bendsFrom after (OrdinalShift.tree offset left) _ (childIncoming ((RankEmbedding.node offset fits current).heavyBranch after) .left) ∪
         bendsFrom after (OrdinalShift.tree offset right) _ (childIncoming ((RankEmbedding.node offset fits current).heavyBranch after) .right)) = _
      rw [heavy, ihl bound, ihr inside]
      rfl

theorem join_bends (left : Splay.Tree.BST 0 l) (right : Splay.Tree.BST 0 r)
    (sl : Splay.Tree.BST 0 l) (sr : Splay.Tree.BST 0 r) :
    bends (Snapshot.ofTree (JoinRanks.tree left right)) (JoinRanks.tree sl sr) =
      (bends (Snapshot.ofTree left) sl).map (keyEmbedding 0 (by omega)) ∪
        (bends (Snapshot.ofTree right) sr).map (keyEmbedding (0+l+1) (by omega)) := by
  have heavy := JoinRanks.root_heavy left right sl sr
  unfold bends JoinRanks.tree
  simp only [bendsFrom]
  change bendAt _ none ((JoinRanks.rootNode sl sr).heavyBranch (Snapshot.ofTree (JoinRanks.tree left right))) ∪
    (bendsFrom (Snapshot.ofTree (JoinRanks.tree left right)) (OrdinalShift.tree 0 sl) _
      (childIncoming ((JoinRanks.rootNode sl sr).heavyBranch (Snapshot.ofTree (JoinRanks.tree left right))) .left) ∪
     bendsFrom (Snapshot.ofTree (JoinRanks.tree left right)) (OrdinalShift.tree (0+l+1) sr) _
      (childIncoming ((JoinRanks.rootNode sl sr).heavyBranch (Snapshot.ofTree (JoinRanks.tree left right))) .right)) = _
  rw [heavy]
  simp only [bendAt, Turns, reduceCtorEq, false_and, or_self, if_false, childIncoming, Finset.empty_union]
  rw [bendsFrom_map 0 1 (by omega) (Snapshot.ofTree left) _ (JoinRanks.left_ranks left right),
    bendsFrom_map (0+l+1) 1 (by omega) (Snapshot.ofTree right) _ (JoinRanks.right_ranks left right)]

theorem join_card (left : Splay.Tree.BST 0 l) (right : Splay.Tree.BST 0 r)
    (sl : Splay.Tree.BST 0 l) (sr : Splay.Tree.BST 0 r) :
    (bends (Snapshot.ofTree (JoinRanks.tree left right)) (JoinRanks.tree sl sr)).card =
      (bends (Snapshot.ofTree left) sl).card + (bends (Snapshot.ofTree right) sr).card := by
  rw [join_bends, Finset.card_union_of_disjoint, Finset.card_map, Finset.card_map]
  apply Finset.disjoint_left.mpr
  intro key leftMem rightMem
  obtain ⟨x, _, xEq⟩ := Finset.mem_map.mp leftMem
  obtain ⟨y, _, yEq⟩ := Finset.mem_map.mp rightMem
  have same := congrArg Fin.val (xEq.trans yEq.symm)
  dsimp [keyEmbedding] at same
  omega

end MultiSplay.CommonBends
