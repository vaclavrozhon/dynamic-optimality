import Splay.Interface.ActivityBoundAssembly
import Splay.Interface.VColumnIncidence
import Splay.Interface.UColumnIncidence

namespace Splay.Interface

/--
Consequently the old combined incidence premise reduces exactly to its
remaining u-column half.
-/
theorem significantColumnIncidence_of_u
    (uIncidence : SignificantUColumnIncidenceHypothesis) :
    SignificantColumnIncidenceHypothesis := by
  intro n params initial final initialLabels finalLabels initialLedger
    finalLedger initialClock finalClock finalEvents operations
    timedSnapshots history
  exact
    ⟨significantVColumnIncidence history,
      uIncidence history⟩

/-- A u-column proof now suffices directly for the final activity theorem. -/
theorem activityBound_of_significantUColumnIncidence
    (shape : Shape)
    (uIncidence : SignificantUColumnIncidenceHypothesis) :
    ActivityBound shape :=
  activityBound_of_significantColumnIncidence shape
    (significantColumnIncidence_of_u uIncidence)

end Splay.Interface
