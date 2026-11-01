import Greedy.LabelHistory
import Greedy.CreatorCancellation

/-!
# Creator shifts against sparse vector changes

Every edge supplies its actual creator and two immutable join times.
After grouping by creator, a bound on the signed coefficient gives a
bound by total label variation, with no label-range factor.
-/

namespace Greedy.LabelHistory

open GreedyForest
open scoped BigOperators

variable {Record Edge : Type*} [Fintype Record] [Fintype Edge] [DecidableEq Record]

def variation (history : History Record) : ℤ :=
  (history.changes.map (fun change => ∑ record, |change.delta record|)).sum

theorem sparse_creator_identity (history : History Record) (creator : Edge → Record)
    (winnerJoin loserJoin : Edge → ℕ) :
    (∑ edge, (value history (loserJoin edge) (creator edge) - value history (winnerJoin edge) (creator edge))) =
      (history.changes.map (fun change => ∑ record,
        (∑ edge, if creator edge = record then joinCoefficient (winnerJoin edge) (loserJoin edge) change.time else 0) *
          change.delta record)).sum := by
  classical
  simp_rw [difference]
  change (∑ edge, (history.changes.map (fun change =>
    joinCoefficient (winnerJoin edge) (loserJoin edge) change.time * change.delta (creator edge))).sum) = _
  have exchange (changes : List (Change Record)) :
      (∑ edge, (changes.map (fun change => joinCoefficient (winnerJoin edge) (loserJoin edge) change.time *
        change.delta (creator edge))).sum) =
      (changes.map (fun change => ∑ edge, joinCoefficient (winnerJoin edge) (loserJoin edge) change.time *
        change.delta (creator edge))).sum := by
    induction changes with
    | nil => simp
    | cons change rest ih => simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib, ih]
  rw [exchange]
  apply congrArg List.sum
  apply List.map_congr_left
  intro change _
  symm
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro edge _
  simp only [ite_mul, zero_mul]
  simp

theorem sparse_creator_bound (history : History Record) (creator : Edge → Record)
    (winnerJoin loserJoin : Edge → ℕ) (capacity : ℤ)
    (bound : ∀ record time,
      |∑ edge, if creator edge = record then joinCoefficient (winnerJoin edge) (loserJoin edge) time else 0| ≤ capacity) :
    (∑ edge, (value history (loserJoin edge) (creator edge) - value history (winnerJoin edge) (creator edge))) ≤
      capacity * variation history := by
  rw [sparse_creator_identity]
  have one (change : Change Record) :
      (∑ record, (∑ edge, if creator edge = record then joinCoefficient (winnerJoin edge) (loserJoin edge) change.time else 0) *
        change.delta record) ≤ capacity * ∑ record, |change.delta record| := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro record _
    calc
      _ ≤ |(∑ edge, if creator edge = record then joinCoefficient (winnerJoin edge) (loserJoin edge) change.time else 0) *
          change.delta record| := le_abs_self _
      _ = |∑ edge, if creator edge = record then joinCoefficient (winnerJoin edge) (loserJoin edge) change.time else 0| *
          |change.delta record| := abs_mul _ _
      _ ≤ capacity * |change.delta record| := mul_le_mul_of_nonneg_right (bound record change.time) (abs_nonneg _)
  unfold variation
  induction history.changes with
  | nil => simp
  | cons change rest ih =>
      simp only [List.map_cons, List.sum_cons]
      calc
        _ ≤ capacity * (∑ record, |change.delta record|) + capacity *
            (rest.map (fun change => ∑ record, |change.delta record|)).sum := add_le_add (one change) ih
        _ = _ := by ring

end Greedy.LabelHistory
