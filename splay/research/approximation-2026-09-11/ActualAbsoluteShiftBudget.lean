import Splay.Interface.UColumnInitial
import Splay.Interface.UClockCutRootStep
import Splay.Interface.VColumnIncidence

namespace Splay.Research.ActualAbsoluteShiftBudget

open Splay.Interface
open scoped BigOperators

/-- Absolute row sums, rather than only their signed aggregate, are bounded
by the same proved unit-event column incidences. -/
theorem absolute_rows_le {α : Type*} {m multiplicity : ℕ}
    (rows : List α) (value : α → ℤ)
    (deltas : Fin m → ℤ) (charge : α → Fin m → ℤ)
    (exactRows : ∀ row ∈ rows,
      value row = temporalShift deltas (charge row))
    (unit : ∀ event, |deltas event| ≤ 1)
    (columns : ∀ event,
      (rows.map fun row => |charge row event|).sum ≤ (multiplicity : ℤ)) :
    (rows.map fun row => |value row|).sum ≤
      ((multiplicity * m : ℕ) : ℤ) := by
  have rowBound : (rows.map fun row => |value row|).sum ≤
      ∑ event, (rows.map fun row => |charge row event|).sum := by
    clear columns
    induction rows with
    | nil => simp
    | cons row rows ih =>
        have tail := ih (by
          intro later member
          exact exactRows later (by simp [member]))
        have head : |value row| ≤ ∑ event, |charge row event| := by
          rw [exactRows row (by simp)]
          unfold temporalShift
          apply (Finset.abs_sum_le_sum_abs _ _).trans
          apply Finset.sum_le_sum
          intro event _
          rw [abs_mul]
          exact mul_le_of_le_one_right (abs_nonneg _) (unit event)
        simpa [List.map_cons, Finset.sum_add_distrib] using add_le_add head tail
  apply rowBound.trans
  calc
    _ ≤ ∑ _event : Fin m, (multiplicity : ℤ) :=
      Finset.sum_le_sum fun event _ => columns event
    _ = _ := by simp; ring

theorem early_absolute_v_u {n : ℕ} {params : Parameters}
    {initial final : State n} {finalLabels : RootLabels}
    {finalLedger : EpisodeLedger n} {finalClock : EpisodeClock n}
    {finalEvents : List (ValueChangeEvent n)}
    {operations : List (Operation n)}
    {snapshots : List (TimedAnnotatedPairShiftSnapshot n)}
    (history : LifetimeHistory.TimedPairShiftHistory params initial []
      (EpisodeLedger.empty : EpisodeLedger n) (fun _ => 0) []
      operations snapshots final finalLabels finalLedger finalClock finalEvents)
    (initialState : initial.Initial params) (cutoff : ℕ) :
    ((significantTimedSnapshots cutoff snapshots).map fun timed =>
      |timed.annotated.snapshot.vShift| +
        |timed.annotated.snapshot.uShift|).sum ≤
      (((1 + params.growingLimit) * cutoff *
        totalValueChanges operations : ℕ) : ℤ) := by
  have vBound := absolute_rows_le
    (significantTimedSnapshots cutoff snapshots)
    (fun timed => timed.annotated.snapshot.vShift)
    (valueChangeDeltaVector finalEvents)
    (fun timed => timed.vTemporalCharge finalEvents)
    (by
      intro timed member
      exact history.snapshot_vShift_eq_temporalCharge timed
        (List.mem_filter.mp member).1)
    history.final_deltaUnit_of_empty
    (history.significant_vColumn_le cutoff)
  have uBound := absolute_rows_le
    (significantTimedSnapshots cutoff snapshots)
    (fun timed => timed.annotated.snapshot.uShift)
    (valueChangeDeltaVector finalEvents)
    (fun timed => timed.uTemporalCharge finalEvents)
    (by
      intro timed member
      exact history.snapshot_uShift_eq_temporalCharge timed
        (List.mem_filter.mp member).1)
    history.final_deltaUnit_of_empty
    (history.significant_uColumn_le_of_initial clockCutRootStep
      initialState cutoff)
  have eventLength : finalEvents.length = totalValueChanges operations := by
    have finalEq := history.finalEvents_eq
    simp only [List.nil_append] at finalEq
    rw [finalEq, length_valueChangeEvents]
  rw [List.sum_map_add]
  rw [eventLength] at vBound uBound
  have combined := add_le_add vBound uBound
  have rhs : ((cutoff * totalValueChanges operations : ℕ) : ℤ) +
      ((params.growingLimit * cutoff * totalValueChanges operations : ℕ) : ℤ) =
      (((1 + params.growingLimit) * cutoff * totalValueChanges operations : ℕ) : ℤ) := by
    push_cast
    ring
  rw [← rhs]
  exact combined

end Splay.Research.ActualAbsoluteShiftBudget
