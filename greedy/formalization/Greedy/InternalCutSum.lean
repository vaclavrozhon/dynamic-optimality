import Greedy.IntervalCancellation
import Greedy.SparseEdgeSums

/-! Signed cancellation for the literal finite edge set of an ordered
sparse tree, restricted to edges whose endpoints lie in one source interval. -/

namespace Greedy.IntervalCancellation

open GreedyForest.ActiveTree Greedy.SparseEdgeSums
open scoped BigOperators

theorem internalWeight_abs (cut lo hi a b : ℕ) : |internalWeight cut lo hi a b| ≤ 1 := by
  have ha := side_bounds cut a
  have hb := side_bounds cut b
  unfold internalWeight
  split_ifs <;> rw [abs_le] <;> omega

theorem edge_sum_same (cut lo hi : ℕ) (tree : Sparse) (value : ℤ)
    (same : ∀ key ∈ tree.keys, side cut key = value) :
    (∑ edge ∈ tree.edges, internalWeight cut lo hi edge.1 edge.2) = 0 := by
  apply Finset.sum_eq_zero
  intro edge member
  obtain ⟨parentMem, childMem⟩ := edge_members tree edge member
  simp [internalWeight, same edge.1 parentMem, same edge.2 childMem]

theorem edgeTo_sum_same (cut lo hi parent : ℕ) (tree : Sparse)
    (same : ∀ key ∈ tree.keys, side cut key = side cut parent) :
    (∑ edge ∈ tree.edgeTo parent, internalWeight cut lo hi edge.1 edge.2) = 0 := by
  apply Finset.sum_eq_zero
  intro edge member
  obtain ⟨parentEq, childMem⟩ := edgeTo_members member
  simp [internalWeight, parentEq, same edge.2 childMem]

theorem sumTo_eq_headWeight (cut lo hi parent : ℕ) (tree : Sparse) :
    sumTo (fun edge => internalWeight cut lo hi edge.1 edge.2) parent tree =
      headWeight cut lo hi parent (cutPath cut tree) := by
  cases tree <;> rfl

theorem internal_sum_eq_path (cut lo hi : ℕ) (tree : Sparse) (ordered : tree.Ordered) :
    (∑ edge ∈ tree.edges, internalWeight cut lo hi edge.1 edge.2) =
      pathSum cut lo hi (cutPath cut tree) := by
  induction tree with
  | empty => simp [Sparse.edges, cutPath, pathSum]
  | node parent left right il ir =>
      rw [node_sum _ parent left right ordered]
      by_cases parentLeft : parent < cut
      · have same : ∀ key ∈ left.keys, side cut key = side cut parent := by
          intro key member
          have below := ordered.2.2.1 key member
          have keyLeft : ¬ cut ≤ key := by omega
          have parentNotRight : ¬ cut ≤ parent := by omega
          simp [side, keyLeft, parentNotRight]
        have sumZero := edge_sum_same cut lo hi left (side cut parent) same
        have edgeZero := edgeTo_sum_same cut lo hi parent left same
        rw [sumZero, edgeZero, ir ordered.2.1, edgeTo_sum, sumTo_eq_headWeight]
        simp only [cutPath, if_pos parentLeft, pathSum]
        ring
      · have same : ∀ key ∈ right.keys, side cut key = side cut parent := by
          intro key member
          have above := ordered.2.2.2 key member
          have keyRight : cut ≤ key := by omega
          have parentRight : cut ≤ parent := by omega
          simp [side, keyRight, parentRight]
        have sumZero := edge_sum_same cut lo hi right (side cut parent) same
        have edgeZero := edgeTo_sum_same cut lo hi parent right same
        rw [sumZero, edgeZero, il ordered.1, edgeTo_sum, sumTo_eq_headWeight]
        simp only [cutPath, if_neg parentLeft, pathSum]
        ring

/-- The active part of the manuscript's signed historical-cut lemma.
This is a theorem about actual ordered tree edges and any key interval,
not an assumed alternation certificate. -/
theorem internal_edge_sum_abs (cut lo hi : ℕ) (tree : Sparse) (ordered : tree.Ordered) :
    |∑ edge ∈ tree.edges, internalWeight cut lo hi edge.1 edge.2| ≤ 1 := by
  rw [internal_sum_eq_path cut lo hi tree ordered]
  exact internal_cut_path_abs cut lo hi tree ordered

end Greedy.IntervalCancellation
