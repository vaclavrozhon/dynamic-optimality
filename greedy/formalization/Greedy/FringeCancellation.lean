import Greedy.InternalCutSum
import ActualFringeCuts

/-! Signed historical-cut cancellation for the actual canonical fringe,
including its inactive separator leaves. -/

namespace Greedy.FringeCancellation

open Splay.Tree Splay.Tree.BST GreedyMerge.Fringe
open GreedyForest.ActiveTree GreedyForest.HistoricalCuts
open Greedy.IntervalCancellation
open scoped BigOperators

theorem inactive_sum_abs {lo hi : ℕ} (rank owner : ℕ → ℕ) (tree : BST lo hi)
    (localOwners : LocalOwners rank owner lo hi) (cut first last : ℕ) :
    |∑ edge ∈ (GreedyMerge.Fringe.edges owner tree).toFinset.filter
        (fun edge => ¬ Retained owner edge.2),
      internalWeight cut first last edge.1 edge.2| ≤ 2 := by
  classical
  let inactive := (GreedyMerge.Fringe.edges owner tree).toFinset.filter
    (fun edge => ¬ Retained owner edge.2)
  let crossing := inactive.filter (fun edge => KeyCrosses cut edge.1 edge.2)
  have supported : crossing ⊆ {(cut-1,cut), (cut,cut-1)} := by
    intro edge member
    obtain ⟨source, crosses⟩ := Finset.mem_filter.mp member
    obtain ⟨edgeMem, notRetained⟩ := Finset.mem_filter.mp source
    have adjacent := inactive_edge_adjacent rank owner tree localOwners edge.1 edge.2
      (List.mem_toFinset.mp edgeMem) notRetained
    have cases : edge = (cut-1,cut) ∨ edge = (cut,cut-1) :=
      adjacent_crossing_cases adjacent crosses
    simpa only [Finset.mem_insert, Finset.mem_singleton] using cases
  have capacity : crossing.card ≤ 2 := by
    have one := Finset.card_le_card supported
    have two := Finset.card_insert_le (cut-1,cut) ({(cut,cut-1)} : Finset (ℕ × ℕ))
    simp only [Finset.card_singleton] at two
    omega
  have restrict : (∑ edge ∈ inactive, internalWeight cut first last edge.1 edge.2) =
      ∑ edge ∈ crossing, internalWeight cut first last edge.1 edge.2 := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro edge member outside
    have notCross : ¬ KeyCrosses cut edge.1 edge.2 := by
      intro crosses
      exact outside (Finset.mem_filter.mpr ⟨member, crosses⟩)
    have same := side_eq_of_not_crossing cut edge.1 edge.2 notCross
    simp [internalWeight, same]
  change |∑ edge ∈ inactive, internalWeight cut first last edge.1 edge.2| ≤ 2
  rw [restrict]
  calc
    _ ≤ ∑ edge ∈ crossing, |internalWeight cut first last edge.1 edge.2| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _edge ∈ crossing, (1 : ℤ) :=
      Finset.sum_le_sum fun edge _ => internalWeight_abs cut first last edge.1 edge.2
    _ = (crossing.card : ℤ) := by simp
    _ ≤ 2 := by exact_mod_cast capacity

/-- The signed coefficient of one spatial cut in one consecutive source
block is at most three: one from active edges and two inactive endpoints. -/
theorem fringe_internal_sum_abs {lo hi : ℕ} (rank owner : ℕ → ℕ) (tree : BST lo hi)
    (projection : Projection rank owner tree) (localOwners : LocalOwners rank owner lo hi)
    (cut first last : ℕ) :
    |∑ edge ∈ (GreedyMerge.Fringe.edges owner tree).toFinset,
      internalWeight cut first last edge.1 edge.2| ≤ 3 := by
  classical
  have activeBound := internal_edge_sum_abs cut first last (active owner tree).tree
    (active_ordered rank owner tree projection localOwners)
  rw [active_edges rank owner tree projection localOwners] at activeBound
  have inactiveBound := inactive_sum_abs rank owner tree localOwners cut first last
  have split := Finset.sum_filter_add_sum_filter_not (GreedyMerge.Fringe.edges owner tree).toFinset
    (fun edge => Retained owner edge.2) (fun edge => internalWeight cut first last edge.1 edge.2)
  rw [← split]
  exact (abs_add_le _ _).trans (by dsimp [retainedEdges] at activeBound; omega)

end Greedy.FringeCancellation
