import Splay.Lazy.Canonical

namespace Splay.Lazy.Canonical

open Splay.Rank

/-- The attachment key determines exactly which part of a node's edge list
contains an edge. This transports recursion locations between snapshots. -/
theorem treeEdge_location_iff {n lower root upper : ℕ} (snapshot : Snapshot n)
    (left : Tree.BST lower root) (right : Tree.BST (root + 1) upper)
    (upper_le_n : upper ≤ n) (depth : ℕ) {edge : Edge n}
    (member : edge ∈ treeEdges snapshot (.node left right) upper_le_n depth) :
    let node : AtNode n := ⟨lower, root, upper, left, right, upper_le_n⟩
    let leftBound : root ≤ n := by have := right.lower_le_upper; omega
    (edge ∈ edgesAtNode snapshot node depth ↔ edge.attachmentKey = root) ∧
      (edge ∈ treeEdges snapshot left leftBound (depth + 1) ↔ edge.attachmentKey < root) ∧
      (edge ∈ treeEdges snapshot right upper_le_n (depth + 1) ↔ root < edge.attachmentKey) := by
  dsimp only
  let node : AtNode n := ⟨lower, root, upper, left, right, upper_le_n⟩
  have leftBound : root ≤ n := by have := right.lower_le_upper; omega
  have localKey : edge ∈ edgesAtNode snapshot node depth → edge.attachmentKey = root :=
    mem_edgesAtNode_attachmentKey snapshot node depth
  have leftKey : edge ∈ treeEdges snapshot left leftBound (depth + 1) → edge.attachmentKey < root :=
    fun inside => (mem_treeEdges_attachmentKey_bounds snapshot left leftBound inside).2
  have rightKey : edge ∈ treeEdges snapshot right upper_le_n (depth + 1) → root < edge.attachmentKey := by
    intro inside
    have lowerBound := (mem_treeEdges_attachmentKey_bounds snapshot right upper_le_n inside).1
    omega
  simp only [treeEdges, List.mem_append] at member
  grind

end Splay.Lazy.Canonical
