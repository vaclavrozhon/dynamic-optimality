import MultiSplay.RankEmbedding
import Splay.Rank.FromTree
import Splay.Lazy.CanonicalHeapView

/-!
# Comparison ranks at a common root join

A new common pivot has rank zero. Every old external position moves down by one
in the comparison tree, including the null position of an empty component.
Thus all internal rank differences are preserved, and each former heap root
has new gap exactly one. The splay child shapes can be entirely arbitrary.
-/

namespace MultiSplay.JoinRanks

open Splay.Tree (BST)
open Splay.Rank (External Snapshot)
open Splay.Lazy.Canonical (canonicalRoot)
open RankEmbedding (external)

/-- Shifting ordinal keys translates external positions by twice the offset. -/
theorem shifted_depth (offset : Nat) {lower upper : Nat} (source : BST lower upper) (position : Nat) :
    (OrdinalShift.tree offset source).externalDepth (2 * offset + position) = source.externalDepth position := by
  induction source with
  | empty => rfl
  | @node lower root upper left right ihl ihr =>
      have less : (2 * offset + position < 2 * (offset + root) + 1) ↔ (position < 2 * root + 1) := by omega
      have equal : (2 * offset + position = 2 * (offset + root) + 1) ↔ (position = 2 * root + 1) := by omega
      simp only [OrdinalShift.tree, BST.externalDepth, less, equal, ihl, ihr]

/-- Both shifts are explicit so that all later transport statements use the
same embedding theorem, including the left component at offset zero. -/
def tree {leftSize rightSize : Nat} (left : BST 0 leftSize) (right : BST 0 rightSize) :
    BST 0 (0 + leftSize + 1 + rightSize) :=
  .node (OrdinalShift.tree 0 left) (OrdinalShift.tree (0 + leftSize + 1) right)

theorem left_ranks {leftSize rightSize : Nat} (left : BST 0 leftSize) (right : BST 0 rightSize)
    (position : External leftSize) :
    (Snapshot.ofTree (tree left right)).rank (external 0 (by omega) position) =
      (Snapshot.ofTree left).rank position + 1 := by
  change (tree left right).externalDepth (2 * 0 + position.val) = left.externalDepth position.val + 1
  unfold tree
  rw [BST.externalDepth_node_of_lt_root]
  · rw [shifted_depth]
  · have := position.isLt
    omega

theorem right_ranks {leftSize rightSize : Nat} (left : BST 0 leftSize) (right : BST 0 rightSize)
    (position : External rightSize) :
    (Snapshot.ofTree (tree left right)).rank (external (0 + leftSize + 1) (by omega) position) =
      (Snapshot.ofTree right).rank position + 1 := by
  change (tree left right).externalDepth (2 * (0 + leftSize + 1) + position.val) =
    right.externalDepth position.val + 1
  unfold tree
  rw [BST.externalDepth_node_of_root_lt]
  · rw [shifted_depth]
  · omega

def pivot (leftSize rightSize : Nat) : External (0 + leftSize + 1 + rightSize) :=
  ⟨2 * (0 + leftSize) + 1, by omega⟩

@[simp] theorem pivot_rank {leftSize rightSize : Nat} (left : BST 0 leftSize) (right : BST 0 rightSize) :
    (Snapshot.ofTree (tree left right)).rank (pivot leftSize rightSize) = 0 := by
  exact BST.externalDepth_root (OrdinalShift.tree 0 left) (OrdinalShift.tree (0 + leftSize + 1) right)

/-- The statement is independent of the algorithm's left child shape. -/
theorem left_root_gap {leftSize rightSize : Nat} (left : BST 0 leftSize) (right : BST 0 rightSize)
    (splayLeft : BST 0 leftSize) :
    ((Snapshot.ofTree (tree left right)).rank
        (external 0 (by omega) (canonicalRoot (Snapshot.ofTree left) splayLeft)) : Int) -
      (Snapshot.ofTree (tree left right)).rank (pivot leftSize rightSize) = 1 := by
  rw [left_ranks, Splay.Lazy.Canonical.rank_canonicalRoot_eq_zero, pivot_rank]
  decide

theorem right_root_gap {leftSize rightSize : Nat} (left : BST 0 leftSize) (right : BST 0 rightSize)
    (splayRight : BST 0 rightSize) :
    ((Snapshot.ofTree (tree left right)).rank
        (external (0 + leftSize + 1) (by omega) (canonicalRoot (Snapshot.ofTree right) splayRight)) : Int) -
      (Snapshot.ofTree (tree left right)).rank (pivot leftSize rightSize) = 1 := by
  rw [right_ranks, Splay.Lazy.Canonical.rank_canonicalRoot_eq_zero, pivot_rank]
  decide

/-- The full old light-edge list survives inside the left component, with
attachment depths increased by one and every history address retained. -/
theorem left_edges {leftSize rightSize : Nat} (left : BST 0 leftSize) (right : BST 0 rightSize)
    (splayLeft : BST 0 leftSize) :
    Splay.Lazy.Canonical.treeEdges (Snapshot.ofTree (tree left right))
        (OrdinalShift.tree 0 splayLeft) (by omega) 1 =
      (Splay.Lazy.Canonical.fullEdges (Snapshot.ofTree left) splayLeft).map
        (RankEmbedding.edge 0 1 (by omega)) := by
  exact RankEmbedding.treeEdges 0 1 1 (by omega) (Snapshot.ofTree left)
    (Snapshot.ofTree (tree left right)) (left_ranks left right) splayLeft le_rfl 0

theorem right_edges {leftSize rightSize : Nat} (left : BST 0 leftSize) (right : BST 0 rightSize)
    (splayRight : BST 0 rightSize) :
    Splay.Lazy.Canonical.treeEdges (Snapshot.ofTree (tree left right))
        (OrdinalShift.tree (0 + leftSize + 1) splayRight) (by omega) 1 =
      (Splay.Lazy.Canonical.fullEdges (Snapshot.ofTree right) splayRight).map
        (RankEmbedding.edge (0 + leftSize + 1) 1 (by omega)) := by
  exact RankEmbedding.treeEdges (0 + leftSize + 1) 1 1 (by omega) (Snapshot.ofTree right)
    (Snapshot.ofTree (tree left right)) (right_ranks left right) splayRight le_rfl 0

def rootNode {leftSize rightSize : Nat} (left : BST 0 leftSize) (right : BST 0 rightSize) :
    Splay.Lazy.Canonical.AtNode (0 + leftSize + 1 + rightSize) :=
  ⟨0, 0 + leftSize, 0 + leftSize + 1 + rightSize,
    OrdinalShift.tree 0 left, OrdinalShift.tree (0 + leftSize + 1) right, le_rfl⟩

theorem root_owner {leftSize rightSize : Nat} (left : BST 0 leftSize) (right : BST 0 rightSize)
    (splayLeft : BST 0 leftSize) (splayRight : BST 0 rightSize) :
    (rootNode splayLeft splayRight).owner (Snapshot.ofTree (tree left right)) = pivot leftSize rightSize := by
  symm
  apply (Snapshot.ofTree (tree left right)).intervalMin_unique
  refine ⟨?_, ?_, ?_⟩
  · change 2 * 0 ≤ 2 * (0 + leftSize) + 1
    omega
  · change 2 * (0 + leftSize) + 1 ≤ 2 * (0 + leftSize + 1 + rightSize)
    omega
  · intro candidate _ _
    rw [pivot_rank]
    exact Nat.zero_le _

theorem root_heavy {leftSize rightSize : Nat} (left : BST 0 leftSize) (right : BST 0 rightSize)
    (splayLeft : BST 0 leftSize) (splayRight : BST 0 rightSize) :
    (rootNode splayLeft splayRight).heavyBranch (Snapshot.ofTree (tree left right)) = .middle := by
  apply Splay.Lazy.Canonical.AtNode.heavyBranch_eq_of_rank_eq_zero
    (Snapshot.ofTree (tree left right)) (rootNode splayLeft splayRight) .middle (pivot leftSize rightSize)
    (pivot_rank left right)
  · constructor
    · change 2 * 0 ≤ 2 * (0 + leftSize) + 1
      omega
    · change 2 * (0 + leftSize) + 1 ≤ 2 * (0 + leftSize + 1 + rightSize)
      omega
  · rfl

theorem root_left_child {leftSize rightSize : Nat} (left : BST 0 leftSize) (right : BST 0 rightSize)
    (splayLeft : BST 0 leftSize) (splayRight : BST 0 rightSize) :
    (rootNode splayLeft splayRight).branchMin (Snapshot.ofTree (tree left right)) .left =
      external 0 (by omega) (canonicalRoot (Snapshot.ofTree left) splayLeft) := by
  exact RankEmbedding.subtreeOwner 0 1 (by omega) (Snapshot.ofTree left)
    (Snapshot.ofTree (tree left right)) (left_ranks left right) splayLeft le_rfl

theorem root_right_child {leftSize rightSize : Nat} (left : BST 0 leftSize) (right : BST 0 rightSize)
    (splayLeft : BST 0 leftSize) (splayRight : BST 0 rightSize) :
    (rootNode splayLeft splayRight).branchMin (Snapshot.ofTree (tree left right)) .right =
      external (0 + leftSize + 1) (by omega) (canonicalRoot (Snapshot.ofTree right) splayRight) := by
  exact RankEmbedding.subtreeOwner (0 + leftSize + 1) 1 (by omega) (Snapshot.ofTree right)
    (Snapshot.ofTree (tree left right)) (right_ranks left right) splayRight le_rfl

/-- The two new records are precisely the light edges to the two old heap
roots. The middle branch contains the new comparison minimum. -/
theorem root_edges {leftSize rightSize : Nat} (left : BST 0 leftSize) (right : BST 0 rightSize)
    (splayLeft : BST 0 leftSize) (splayRight : BST 0 rightSize) :
    Splay.Lazy.Canonical.edgesAtNode (Snapshot.ofTree (tree left right)) (rootNode splayLeft splayRight) 0 =
      [Splay.Lazy.Canonical.edgeFor (Snapshot.ofTree (tree left right)) (rootNode splayLeft splayRight) 0 .left,
       Splay.Lazy.Canonical.edgeFor (Snapshot.ofTree (tree left right)) (rootNode splayLeft splayRight) 0 .right] := by
  simp only [Splay.Lazy.Canonical.edgesAtNode, Splay.Lazy.Canonical.lightBranches,
    root_heavy left right splayLeft splayRight]
  rfl

/-- Exact join decomposition: two new root edges followed by the unchanged
light-edge histories of both children, with their embedded addresses. -/
theorem full_edges {leftSize rightSize : Nat} (left : BST 0 leftSize) (right : BST 0 rightSize)
    (splayLeft : BST 0 leftSize) (splayRight : BST 0 rightSize) :
    Splay.Lazy.Canonical.fullEdges (Snapshot.ofTree (tree left right)) (tree splayLeft splayRight) =
      [Splay.Lazy.Canonical.edgeFor (Snapshot.ofTree (tree left right)) (rootNode splayLeft splayRight) 0 .left,
       Splay.Lazy.Canonical.edgeFor (Snapshot.ofTree (tree left right)) (rootNode splayLeft splayRight) 0 .right] ++
      (Splay.Lazy.Canonical.fullEdges (Snapshot.ofTree left) splayLeft).map
        (RankEmbedding.edge 0 1 (by omega)) ++
      (Splay.Lazy.Canonical.fullEdges (Snapshot.ofTree right) splayRight).map
        (RankEmbedding.edge (0 + leftSize + 1) 1 (by omega)) := by
  change Splay.Lazy.Canonical.edgesAtNode (Snapshot.ofTree (tree left right)) (rootNode splayLeft splayRight) 0 ++
    Splay.Lazy.Canonical.treeEdges (Snapshot.ofTree (tree left right)) (OrdinalShift.tree 0 splayLeft) _ 1 ++
    Splay.Lazy.Canonical.treeEdges (Snapshot.ofTree (tree left right))
      (OrdinalShift.tree (0 + leftSize + 1) splayRight) _ 1 = _
  rw [root_edges, left_edges, right_edges]

end MultiSplay.JoinRanks
