import Greedy.WeightedCut
import Greedy.SparseEdgeSums
import SparseCutGeometry

/-! The weighted cut-path estimate for the literal active-tree edges. -/

namespace Greedy.WeightedActiveCut

open GreedyForest GreedyForest.ActiveTree GreedyForest.HistoricalCuts
open Greedy.SparseEdgeSums
open scoped BigOperators

def weight (label : ℕ → ℤ) (cut : ℕ) (edge : ℕ × ℕ) : ℤ :=
  if KeyCrosses cut edge.1 edge.2 then label edge.2 - label edge.1 else 0

theorem sumTo_eq (label : ℕ → ℤ) (cut parent : ℕ) (tree : Sparse) :
    sumTo (weight label cut) parent tree =
      WeightedCut.edgeWeight (decide (cut ≤ parent)) (label parent) (cutView label cut tree) := by
  cases tree with
  | empty => rfl
  | node key left right =>
      simp only [sumTo, weight, cutView, WeightedCut.edgeWeight, opposite_sides_iff]

theorem sum_eq (label : ℕ → ℤ) (cut : ℕ) (tree : Sparse) (ordered : tree.Ordered) :
    (∑ edge ∈ tree.edges, weight label cut edge) = WeightedCut.weight (cutView label cut tree) := by
  induction tree with
  | empty => simp [Sparse.edges, cutView, WeightedCut.weight]
  | node root left right il ir =>
      rw [node_sum _ root left right ordered, il ordered.1, ir ordered.2.1,
        edgeTo_sum, edgeTo_sum, sumTo_eq, sumTo_eq]
      rfl

theorem edge_rank_le (rank : ℕ → ℕ) (tree : Sparse) (heap : tree.Heap rank)
    (edge : ℕ × ℕ) (member : edge ∈ tree.edges) : rank edge.1 ≤ rank edge.2 := by
  induction tree with
  | empty => simp [Sparse.edges] at member
  | node root left right il ir =>
      simp only [Sparse.edges, Finset.mem_union] at member
      rcases member with ((hl | hr) | hl) | hr
      · exact il heap.1 hl
      · exact ir heap.2.1 hr
      · obtain ⟨eq, child⟩ := edgeTo_members hl
        rw [eq]
        exact heap.2.2.1 _ child
      · obtain ⟨eq, child⟩ := edgeTo_members hr
        rw [eq]
        exact heap.2.2.2 _ child

theorem weight_nonneg (rank : ℕ → ℕ) (label : ℕ → ℤ) (cut : ℕ)
    (tree : Sparse) (heap : tree.Heap rank)
    (monotone : ∀ a b, rank a ≤ rank b → label a ≤ label b)
    (edge : ℕ × ℕ) (member : edge ∈ tree.edges) : 0 ≤ weight label cut edge := by
  have order := monotone _ _ (edge_rank_le rank tree heap edge member)
  unfold weight
  split_ifs <;> omega

theorem sum_le_range (rank : ℕ → ℕ) (label : ℕ → ℤ) (cut : ℕ)
    (tree : Sparse) (K lower : ℤ) (ordered : tree.Ordered) (heap : tree.Heap rank)
    (range : lower ≤ K) (monotone : ∀ a b, rank a ≤ rank b → label a ≤ label b)
    (labels : ∀ key ∈ tree.keys, lower ≤ label key ∧ label key ≤ K) :
    (∑ edge ∈ tree.edges, weight label cut edge) ≤ K - lower := by
  rw [sum_eq label cut tree ordered]
  exact WeightedCut.weight_le_range K lower _ range (ordered_cutView label cut tree ordered)
    (bounded_cutView rank label cut tree K lower heap monotone labels)

end Greedy.WeightedActiveCut
