import Greedy.SignedLifetime
import HistoricalKeyCuts
import ForestLedger
import ActualPhaseEvents

/-!
# Historical creator coefficients in a literal consolidation

The members of one source block occupy an interval among the actual
phase records. Their stored join times are monotone in one of the two
key directions. We construct the spatial cut representing any historical
time, including reversed histories and deletion holes, and identify the
signed coefficient with the actual fringe sum. Equal-label internal
edges are retained in this sum.
-/

namespace Greedy.SignedPhase

open Splay.Tree GreedyMerge.Fringe GreedyMerge.Fringe.Schedule
open GreedyForest GreedyForest.HistoricalCuts
open Greedy.IntervalCancellation Greedy.SignedLifetime
open scoped BigOperators

def historyWeight (members : Finset ℕ) (join : ℕ → ℕ) (time : ℕ) (edge : ℕ × ℕ) : ℤ :=
  if edge.1 ∈ members ∧ edge.2 ∈ members then
    joinCoefficient (join edge.1) (join edge.2) time else 0

theorem monotone_weight (members : Finset ℕ) (join : ℕ → ℕ) (time cut first last : ℕ)
    (early : ∀ key ∈ members, join key ≤ time ↔ key < cut)
    (edge : ℕ × ℕ)
    (parent : edge.1 ∈ members ↔ first ≤ edge.1 ∧ edge.1 ≤ last)
    (child : edge.2 ∈ members ↔ first ≤ edge.2 ∧ edge.2 ≤ last) :
    historyWeight members join time edge = internalWeight cut first last edge.1 edge.2 := by
  by_cases both : edge.1 ∈ members ∧ edge.2 ∈ members
  · have pw := early edge.1 both.1
    have cw := early edge.2 both.2
    have intervals := And.intro (parent.mp both.1) (child.mp both.2)
    simp only [historyWeight, if_pos both, internalWeight,
      intervals.1.1, intervals.1.2, intervals.2.1, intervals.2.2, and_self, ↓reduceIte]
    unfold joinCoefficient side
    split_ifs <;> omega
  · have outside : ¬ (first ≤ edge.1 ∧ edge.1 ≤ last ∧ first ≤ edge.2 ∧ edge.2 ≤ last) := by
      tauto
    simp only [historyWeight, if_neg both, internalWeight, if_neg outside]

theorem antitone_weight (members : Finset ℕ) (join : ℕ → ℕ) (time cut first last : ℕ)
    (early : ∀ key ∈ members, join key ≤ time ↔ cut ≤ key)
    (edge : ℕ × ℕ)
    (parent : edge.1 ∈ members ↔ first ≤ edge.1 ∧ edge.1 ≤ last)
    (child : edge.2 ∈ members ↔ first ≤ edge.2 ∧ edge.2 ≤ last) :
    historyWeight members join time edge = - internalWeight cut first last edge.1 edge.2 := by
  by_cases both : edge.1 ∈ members ∧ edge.2 ∈ members
  · have pw := early edge.1 both.1
    have cw := early edge.2 both.2
    have intervals := And.intro (parent.mp both.1) (child.mp both.2)
    simp only [historyWeight, if_pos both, internalWeight,
      intervals.1.1, intervals.1.2, intervals.2.1, intervals.2.2, and_self, ↓reduceIte]
    unfold joinCoefficient side
    split_ifs <;> omega
  · have outside : ¬ (first ≤ edge.1 ∧ edge.1 ≤ last ∧ first ≤ edge.2 ∧ edge.2 ≤ last) := by
      tauto
    simp only [historyWeight, if_neg both, internalWeight, if_neg outside, neg_zero]

/-- The cut and its orientation are constructed from stored joins.
The source interval is only required on actual edge endpoints. -/
theorem fringe_geometry {lo hi : ℕ} (rank owner : ℕ → ℕ) (tree : BST lo hi)
    (projection : Projection rank owner tree) (localOwners : LocalOwners rank owner lo hi)
    (members : Finset ℕ) (join : ℕ → ℕ) (time first last : ℕ)
    (interval : ∀ edge ∈ (edges owner tree).toFinset,
      (edge.1 ∈ members ↔ first ≤ edge.1 ∧ edge.1 ≤ last) ∧
      (edge.2 ∈ members ↔ first ≤ edge.2 ∧ edge.2 ≤ last))
    (ordered :
      (∀ a ∈ members, ∀ b ∈ members, a ≤ b → join a ≤ join b) ∨
      (∀ a ∈ members, ∀ b ∈ members, a ≤ b → join b ≤ join a)) :
    Nonempty (PhaseGeometry (∑ edge ∈ (edges owner tree).toFinset,
      historyWeight members join time edge)) := by
  rcases ordered with mono | anti
  · obtain ⟨cut, early⟩ := monotone_join_key_cut members join time mono
    refine ⟨⟨lo, hi, rank, owner, tree, projection, localOwners, cut, first, last, false, ?_⟩⟩
    simp only [Bool.false_eq_true, ↓reduceIte, one_mul]
    exact Finset.sum_congr rfl fun edge member =>
      monotone_weight members join time cut first last early edge
        (interval edge member).1 (interval edge member).2
  · obtain ⟨cut, early⟩ := antitone_join_key_cut members join time anti
    refine ⟨⟨lo, hi, rank, owner, tree, projection, localOwners, cut, first, last, true, ?_⟩⟩
    simp only [↓reduceIte, neg_one_mul, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun edge member =>
      antitone_weight members join time cut first last early edge
        (interval edge member).1 (interval edge member).2

theorem schedule_geometry {lo hi : ℕ} (rank owner : ℕ → ℕ) (tree : BST lo hi)
    (projection : Projection rank owner tree) (localOwners : LocalOwners rank owner lo hi)
    (members : Finset ℕ) (join : ℕ → ℕ) (time first last : ℕ)
    (interval : ∀ edge ∈ (edges owner tree).toFinset,
      (edge.1 ∈ members ↔ first ≤ edge.1 ∧ edge.1 ≤ last) ∧
      (edge.2 ∈ members ↔ first ≤ edge.2 ∧ edge.2 ≤ last))
    (ordered :
      (∀ a ∈ members, ∀ b ∈ members, a ≤ b → join a ≤ join b) ∨
      (∀ a ∈ members, ∀ b ∈ members, a ≤ b → join b ≤ join a)) :
    Nonempty (PhaseGeometry (∑ edge ∈ (schedule owner tree).toFinset,
      historyWeight members join time edge)) := by
  have equal : (schedule owner tree).toFinset = (edges owner tree).toFinset := by
    ext edge
    simpa only [List.mem_toFinset] using
      (schedule_perm_edges rank owner tree projection localOwners).mem_iff (a := edge)
  rw [equal]
  exact fringe_geometry rank owner tree projection localOwners members join time first last interval ordered

theorem schedule_abs_le_three {lo hi : ℕ} (rank owner : ℕ → ℕ) (tree : BST lo hi)
    (projection : Projection rank owner tree) (localOwners : LocalOwners rank owner lo hi)
    (members : Finset ℕ) (join : ℕ → ℕ) (time first last : ℕ)
    (interval : ∀ edge ∈ (edges owner tree).toFinset,
      (edge.1 ∈ members ↔ first ≤ edge.1 ∧ edge.1 ≤ last) ∧
      (edge.2 ∈ members ↔ first ≤ edge.2 ∧ edge.2 ≤ last))
    (ordered :
      (∀ a ∈ members, ∀ b ∈ members, a ≤ b → join a ≤ join b) ∨
      (∀ a ∈ members, ∀ b ∈ members, a ≤ b → join b ≤ join a)) :
    |∑ edge ∈ (schedule owner tree).toFinset, historyWeight members join time edge| ≤ 3 := by
  obtain ⟨geometry⟩ := schedule_geometry rank owner tree projection localOwners
    members join time first last interval ordered
  exact geometry.bound

end Greedy.SignedPhase
