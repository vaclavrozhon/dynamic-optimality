import ArbitrarySourceTail
import ActualCompressionRowBudget

namespace Splay.Research.HistoricalCompressionTail

open Splay.Interface ActualCompressionRowBudget

theorem lateCount_eq_annotated {n : ℕ} (cutoff : ℕ)
    (snapshots : List (TimedAnnotatedPairShiftSnapshot n)) :
    lateCount cutoff snapshots =
      (insignificantAnnotatedSnapshots cutoff
        (snapshots.map TimedAnnotatedPairShiftSnapshot.annotated)).length := by
  induction snapshots with
  | nil => rfl
  | cons timed snapshots ih =>
      by_cases low : timed.annotated.sourcePassCount < cutoff <;>
        simp [lateCount, insignificantAnnotatedSnapshots,
          AnnotatedPairShiftSnapshot.significantDecision, low,
          show (cutoff ≤ timed.annotated.sourcePassCount) ↔
            ¬ timed.annotated.sourcePassCount < cutoff by omega] at ih ⊢ <;> omega

/-- Arbitrary-cutoff source decay on the exact timed rows used by both
the compiler and the numerical error ledger. All annotations are lifted
from this same original chronology. -/
theorem timed_tail_bound {n : ℕ} {params : Parameters}
    {initial final : State n} {finalLabels : RootLabels}
    {finalLedger : EpisodeLedger n} {finalClock : EpisodeClock n}
    {finalEvents : List (ValueChangeEvent n)} {operations : List (Operation n)}
    {snapshots : List (TimedAnnotatedPairShiftSnapshot n)}
    (initialState : initial.Initial params)
    (history : LifetimeHistory.TimedPairShiftHistory params initial []
      (EpisodeLedger.empty : EpisodeLedger n) (fun _ => 0) []
      operations snapshots final finalLabels finalLedger finalClock finalEvents)
    (blocks : ℕ) :
    2^blocks * lateCount (ArbitrarySourceTail.threshold params blocks) snapshots ≤
      totalActivity operations+totalInserts operations := by
  let cutoff := ArbitrarySourceTail.threshold params blocks
  obtain ⟨occurrences, activity, count⟩ :=
    history.erase.lift_activityHistory_with_tail cutoff
  obtain ⟨conversions, converted⟩ := RootConversionHistory.lift activity.erase
  have bound := ArbitrarySourceTail.entry_tail_bound activity converted initialState blocks
  rw [lateCount_eq_annotated, count]
  exact bound

#print axioms timed_tail_bound

end Splay.Research.HistoricalCompressionTail
