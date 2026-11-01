import Splay.Accounting.CanonicalEdgeUnbroken
import Splay.Accounting.JunctionUnbrokenCorridor
import Splay.Tree.SubtreeAt

namespace Splay.Accounting

open Splay.Rank Splay.Tree Splay.Tree.BST Splay.Lazy Splay.Lazy.Canonical

/-- A literal subtree contributes its exact edges, with the common depth
offset of its occurrence in the larger tree. -/
theorem subtreeAt_treeEdges_subset {n innerLower innerUpper lower upper level : ℕ}
    {inner : BST innerLower innerUpper} {tree : BST lower upper}
    (occurrence : SubtreeAt inner level tree) (snapshot : Snapshot n) (bound : upper ≤ n) (depth : ℕ) :
    ∀ edge ∈ treeEdges snapshot inner (occurrence.bounds.2.trans bound) (depth + level),
      edge ∈ treeEdges snapshot tree bound depth := by
  induction occurrence generalizing depth with
  | here => simpa only [Nat.add_zero] using (fun _ member => member)
  | @left lower root upper level left occurrence right ih =>
      have leftBound : root ≤ n := by have := right.lower_le_upper; omega
      intro edge member
      have inside : edge ∈ treeEdges snapshot inner (occurrence.bounds.2.trans leftBound) ((depth + 1) + level) := by
        simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using member
      exact List.mem_append_left _ (List.mem_append_right _ (ih leftBound (depth + 1) edge inside))
  | @right lower root upper level left right occurrence ih =>
      intro edge member
      have inside : edge ∈ treeEdges snapshot inner (occurrence.bounds.2.trans bound) ((depth + 1) + level) := by
        simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using member
      exact List.mem_append_right _ (ih bound (depth + 1) edge inside)

/-- An edge owned inside a literal subtree is either internal to that
subtree or attached strictly above its root. Disjoint hanging subtrees
cannot contribute an edge with that owner. -/
theorem subtreeAt_edge_mem_or_above {n innerLower innerUpper lower upper level : ℕ}
    {inner : BST innerLower innerUpper} {tree : BST lower upper}
    (occurrence : SubtreeAt inner level tree) (snapshot : Snapshot n) (bound : upper ≤ n) (depth : ℕ)
    {edge : Edge n} (member : edge ∈ treeEdges snapshot tree bound depth)
    (ownerLow : 2 * innerLower ≤ edge.owner.val) (ownerHigh : edge.owner.val ≤ 2 * innerUpper) :
    edge ∈ treeEdges snapshot inner (occurrence.bounds.2.trans bound) (depth + level) ∨
      edge.attachmentDepth < depth + level := by
  induction occurrence generalizing depth with
  | here => exact Or.inl (by simpa only [Nat.add_zero] using member)
  | @left lower root upper level left occurrence right ih =>
      have leftBound : root ≤ n := by have := right.lower_le_upper; omega
      rcases List.mem_append.mp member with localOrLeft | inRight
      · rcases List.mem_append.mp localOrLeft with localEdge | inLeft
        · have atDepth := (mem_edgesAtNode_valid snapshot ⟨lower, root, upper, left, right, bound⟩ depth localEdge).2.2.2.2.2.1
          exact Or.inr (by omega)
        · have result := ih leftBound (depth + 1) inLeft
          simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using result
      · have rightLow : 2 * (root + 1) ≤ edge.owner.val := (mem_treeEdges_inside snapshot right bound inRight).1
        have innerHigh := occurrence.bounds.2
        omega
  | @right lower root upper level left right occurrence ih =>
      have leftBound : root ≤ n := by have := right.lower_le_upper; omega
      rcases List.mem_append.mp member with localOrLeft | inRight
      · rcases List.mem_append.mp localOrLeft with localEdge | inLeft
        · have atDepth := (mem_edgesAtNode_valid snapshot ⟨lower, root, upper, left, right, bound⟩ depth localEdge).2.2.2.2.2.1
          exact Or.inr (by omega)
        · have leftHigh : edge.owner.val ≤ 2 * root := (mem_treeEdges_inside snapshot left leftBound inLeft).2.1
          have innerLow := occurrence.bounds.1
          omega
      · have result := ih bound (depth + 1) inRight
        simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using result

end Splay.Accounting
