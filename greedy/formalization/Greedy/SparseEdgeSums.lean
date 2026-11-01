import SparseActiveTree

/-! Finite sums over the actual edges of an ordered sparse BST. -/

namespace Greedy.SparseEdgeSums

open GreedyForest.ActiveTree
open scoped BigOperators

theorem edgeTo_members {tree : Sparse} {parent a b : ℕ}
    (member : (a, b) ∈ tree.edgeTo parent) : a = parent ∧ b ∈ tree.keys := by
  cases tree with
  | empty => simp [Sparse.edgeTo] at member
  | node root left right =>
      have eq : a = parent ∧ b = root := by simpa [Sparse.edgeTo] using member
      exact ⟨eq.1, eq.2 ▸ Sparse.root_mem root left right⟩

theorem edge_members (tree : Sparse) (edge : ℕ × ℕ) (member : edge ∈ tree.edges) :
    edge.1 ∈ tree.keys ∧ edge.2 ∈ tree.keys := by
  induction tree with
  | empty => simp [Sparse.edges] at member
  | node root left right il ir =>
      simp only [Sparse.edges, Finset.mem_union] at member
      rcases member with ((h | h) | h) | h
      · obtain ⟨a, b⟩ := il h
        constructor <;> simp [Sparse.keys, a, b]
      · obtain ⟨a, b⟩ := ir h
        constructor <;> simp [Sparse.keys, a, b]
      · obtain ⟨a, b⟩ := edgeTo_members h
        constructor <;> simp [Sparse.keys, a, b]
      · obtain ⟨a, b⟩ := edgeTo_members h
        constructor <;> simp [Sparse.keys, a, b]

theorem node_sum (f : ℕ × ℕ → ℤ) (root : ℕ) (left right : Sparse)
    (ordered : (Sparse.node root left right).Ordered) :
    ∑ edge ∈ (Sparse.node root left right).edges, f edge =
      (∑ edge ∈ left.edges, f edge) + (∑ edge ∈ right.edges, f edge) +
      (∑ edge ∈ left.edgeTo root, f edge) + (∑ edge ∈ right.edgeTo root, f edge) := by
  have lr : Disjoint left.edges right.edges := by
    apply Finset.disjoint_left.mpr
    intro edge hl hr
    have l := ordered.2.2.1 edge.1 (edge_members left edge hl).1
    have r := ordered.2.2.2 edge.1 (edge_members right edge hr).1
    omega
  have childrenRoot : ∀ tree, tree = left ∨ tree = right → ∀ edge ∈ tree.edges, edge.1 ≠ root := by
    intro tree which edge member
    rcases which with eq | eq
    · subst tree
      have bound := ordered.2.2.1 edge.1 (edge_members left edge member).1
      omega
    · subst tree
      have bound := ordered.2.2.2 edge.1 (edge_members right edge member).1
      omega
  have toLeft : Disjoint (left.edges ∪ right.edges) (left.edgeTo root) := by
    apply Finset.disjoint_left.mpr
    intro edge child top
    have eq := (edgeTo_members top).1
    rcases Finset.mem_union.mp child with hl | hr
    · exact childrenRoot left (Or.inl rfl) edge hl eq
    · exact childrenRoot right (Or.inr rfl) edge hr eq
  have toRight : Disjoint (left.edges ∪ right.edges ∪ left.edgeTo root) (right.edgeTo root) := by
    apply Finset.disjoint_left.mpr
    intro edge child top
    have eq := (edgeTo_members top).1
    rcases Finset.mem_union.mp child with child | fromLeft
    · rcases Finset.mem_union.mp child with hl | hr
      · exact childrenRoot left (Or.inl rfl) edge hl eq
      · exact childrenRoot right (Or.inr rfl) edge hr eq
    · have l := ordered.2.2.1 edge.2 (edgeTo_members fromLeft).2
      have r := ordered.2.2.2 edge.2 (edgeTo_members top).2
      omega
  rw [Sparse.edges, Finset.sum_union toRight, Finset.sum_union toLeft, Finset.sum_union lr]

def sumTo (f : ℕ × ℕ → ℤ) (parent : ℕ) : Sparse → ℤ
  | .empty => 0
  | .node key _ _ => f (parent, key)

theorem edgeTo_sum (f : ℕ × ℕ → ℤ) (parent : ℕ) (tree : Sparse) :
    (∑ edge ∈ tree.edgeTo parent, f edge) = sumTo f parent tree := by
  cases tree <;> simp [Sparse.edgeTo, sumTo]

end Greedy.SparseEdgeSums
