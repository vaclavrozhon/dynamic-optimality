import Greedy.WeightedActiveCut
import ActualPhaseEvents

/-!
# Positive boundary differences in a source block's first phase

For a link from winner `v` to loser `w`, its new loser label is the
contracted rank gap. After the loser's own label drop is paid, the remaining
positive entry difference is at most the positive difference between that
new label and the winner's old label. For winners in one fixed source
block, the latter is bounded by the increase of a common-base label.
Across the two endpoint cuts these increases telescope.
-/

namespace Greedy.PositiveBoundary

open GreedyForest.ActiveTree GreedyForest.HistoricalCuts GreedyForest.Phase
open Splay.Analysis Greedy.WeightedActiveCut
open scoped BigOperators

def Outgoing (first finish : ℕ) (edge : ℕ × ℕ) : Prop :=
  first ≤ edge.1 ∧ edge.1 < finish ∧ ¬ (first ≤ edge.2 ∧ edge.2 < finish)

instance (first finish : ℕ) (edge : ℕ × ℕ) : Decidable (Outgoing first finish edge) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

def extra (rank : ℕ → ℕ) (base : ℕ) (edge : ℕ × ℕ) : ℤ :=
  max 0 ((contractedGap (rank edge.2 - rank edge.1) : ℤ) - baseLabel rank base edge.1)

theorem entry_split (loser winner updated : ℤ) :
    max 0 (loser - winner) ≤ max 0 (loser - updated) + max 0 (updated - winner) := by omega

theorem extra_le_common_base (rank : ℕ → ℕ) (base : ℕ) (edge : ℕ × ℕ)
    (floor : base ≤ rank edge.1) (order : rank edge.1 ≤ rank edge.2) :
    extra rank base edge ≤ baseLabel rank base edge.2 - baseLabel rank base edge.1 := by
  have smallerGap := contractedGap_mono (show rank edge.2 - rank edge.1 ≤ rank edge.2 - base by omega)
  have monotone := baseLabel_rank_mono rank base edge.1 edge.2 order
  have gapBound : (contractedGap (rank edge.2 - rank edge.1) : ℤ) ≤ baseLabel rank base edge.2 := by
    unfold baseLabel
    exact_mod_cast smallerGap
  unfold extra
  omega

theorem outgoing_crosses (first finish : ℕ) (edge : ℕ × ℕ) (outgoing : Outgoing first finish edge) :
    KeyCrosses first edge.1 edge.2 ∨ KeyCrosses finish edge.1 edge.2 := by
  unfold Outgoing KeyCrosses at *
  omega

theorem active_first_phase (rank : ℕ → ℕ) (tree : Sparse) (first finish base H : ℕ)
    (ordered : tree.Ordered) (heap : tree.Heap rank)
    (floor : ∀ key, first ≤ key → key < finish → base ≤ rank key)
    (ranks : ∀ key ∈ tree.keys, rank key ≤ H) :
    (∑ edge ∈ tree.edges.filter (Outgoing first finish), extra rank base edge) ≤
      2 * ((contractedGap H : ℤ) - 1) := by
  let label := baseLabel rank base
  have labels : ∀ key ∈ tree.keys, 1 ≤ label key ∧ label key ≤ (contractedGap H : ℤ) :=
    fun key member => baseLabel_bounds rank base H key (ranks key member)
  have range : (1 : ℤ) ≤ contractedGap H := by simp only [contractedGap]; omega
  have leftBound := sum_le_range rank label first tree (contractedGap H) 1 ordered heap range
    (baseLabel_rank_mono rank base) labels
  have rightBound := sum_le_range rank label finish tree (contractedGap H) 1 ordered heap range
    (baseLabel_rank_mono rank base) labels
  have pointwise : ∀ edge ∈ tree.edges,
      (if Outgoing first finish edge then extra rank base edge else 0) ≤
        weight label first edge + weight label finish edge := by
    intro edge member
    have leftNonneg := weight_nonneg rank label first tree heap (baseLabel_rank_mono rank base) edge member
    have rightNonneg := weight_nonneg rank label finish tree heap (baseLabel_rank_mono rank base) edge member
    by_cases outgoing : Outgoing first finish edge
    · rw [if_pos outgoing]
      have extraBound := extra_le_common_base rank base edge (floor _ outgoing.1 outgoing.2.1)
        (edge_rank_le rank tree heap edge member)
      rcases outgoing_crosses first finish edge outgoing with left | right
      · simp only [weight, if_pos left] at ⊢
        change extra rank base edge ≤ label edge.2 - label edge.1 + weight label finish edge
        dsimp only [label] at *
        omega
      · change extra rank base edge ≤ weight label first edge + weight label finish edge
        have rightEq : weight label finish edge = label edge.2 - label edge.1 := by simp [weight, right]
        rw [rightEq]
        dsimp only [label] at *
        omega
    · simp only [if_neg outgoing]
      omega
  rw [Finset.sum_filter]
  have sumBound := Finset.sum_le_sum pointwise
  rw [Finset.sum_add_distrib] at sumBound
  omega

/-- Including inactive leaves costs at most two more label ranges. -/
theorem fringe_first_phase {lo hi : ℕ} (rank owner : ℕ → ℕ)
    (tree : Splay.Tree.BST lo hi) (first finish base H : ℕ)
    (projection : GreedyMerge.Fringe.Projection rank owner tree)
    (localOwners : GreedyMerge.Fringe.LocalOwners rank owner lo hi)
    (floor : ∀ key, first ≤ key → key < finish → base ≤ rank key)
    (ranks : ∀ key, 2*lo ≤ key → key ≤ 2*hi → rank key ≤ H) :
    (∑ edge ∈ (GreedyMerge.Fringe.edges owner tree).toFinset.filter (Outgoing first finish),
      extra rank base edge) ≤ 4 * ((contractedGap H : ℤ) - 1) := by
  classical
  let edges := (GreedyMerge.Fringe.edges owner tree).toFinset
  let outgoing := edges.filter (Outgoing first finish)
  let inactive := outgoing.filter (fun edge => ¬ GreedyMerge.Fringe.Retained owner edge.2)
  let retained := outgoing.filter (fun edge => GreedyMerge.Fringe.Retained owner edge.2)
  have activeEq : retained = ((active owner tree).tree.edges).filter (Outgoing first finish) := by
    rw [active_edges rank owner tree projection localOwners]
    ext edge
    simp only [retained, outgoing, edges, retainedEdges, Finset.mem_filter]
    tauto
  have activeBound := active_first_phase rank (active owner tree).tree first finish base H
    (active_ordered rank owner tree projection localOwners)
    (active_heap rank owner tree projection localOwners) floor
    (fun key member => let bounds := active_bounds owner tree key member; ranks key bounds.1 bounds.2)
  rw [← activeEq] at activeBound
  have inactiveSupport : inactive ⊆ {(first,first-1), (finish-1,finish)} := by
    intro edge member
    obtain ⟨out, notRetained⟩ := Finset.mem_filter.mp member
    obtain ⟨edgeMem, condition⟩ := Finset.mem_filter.mp out
    have adjacent := inactive_edge_adjacent rank owner tree localOwners edge.1 edge.2
      (List.mem_toFinset.mp edgeMem) notRetained
    have cases : edge = (first, first-1) ∨ edge = (finish-1, finish) := by
      unfold Outgoing at condition
      rcases adjacent with left | right
      · right; apply Prod.ext <;> simp only <;> omega
      · left; apply Prod.ext <;> simp only <;> omega
    simpa only [Finset.mem_insert, Finset.mem_singleton] using cases
  have capacity : inactive.card ≤ 2 := by
    have one := Finset.card_le_card inactiveSupport
    have two := Finset.card_insert_le (first,first-1) ({(finish-1,finish)} : Finset (ℕ × ℕ))
    simp only [Finset.card_singleton] at two
    omega
  have range : (1 : ℤ) ≤ contractedGap H := by simp only [contractedGap]; omega
  have each : ∀ edge ∈ inactive, extra rank base edge ≤ (contractedGap H : ℤ) - 1 := by
    intro edge member
    have edgeMem := (Finset.mem_filter.mp (Finset.mem_filter.mp member).1).1
    have bounds := GreedyMerge.Fringe.edge_strict_rank_and_bounds rank owner tree edge.1 edge.2
      projection (List.mem_toFinset.mp edgeMem)
    have childRank := ranks edge.2 bounds.2.2.1 bounds.2.2.2.1
    have newUpper : (contractedGap (rank edge.2 - rank edge.1) : ℤ) ≤ contractedGap H := by
      exact_mod_cast contractedGap_mono (show rank edge.2 - rank edge.1 ≤ H by omega)
    have oldLower : (1 : ℤ) ≤ baseLabel rank base edge.1 := by
      simp only [baseLabel, contractedGap]; omega
    unfold extra
    omega
  have inactiveBound : (∑ edge ∈ inactive, extra rank base edge) ≤ 2 * ((contractedGap H : ℤ) - 1) := by
    calc
      _ ≤ ∑ _edge ∈ inactive, ((contractedGap H : ℤ) - 1) := Finset.sum_le_sum each
      _ = (inactive.card : ℤ) * ((contractedGap H : ℤ) - 1) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 2 * ((contractedGap H : ℤ) - 1) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast capacity) (by omega)
  have partition := Finset.sum_filter_add_sum_filter_not outgoing
    (fun edge => GreedyMerge.Fringe.Retained owner edge.2) (extra rank base)
  change (∑ edge ∈ retained, extra rank base edge) + (∑ edge ∈ inactive, extra rank base edge) = _ at partition
  change (∑ edge ∈ outgoing, extra rank base edge) ≤ _
  omega

end Greedy.PositiveBoundary
