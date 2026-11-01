import Splay.Interface.ActivityBoundAssembly
import Splay.Interface.VColumnIncidence
import Splay.Interface.UColumnInitial
import Splay.Interface.UClockCutRootStep

namespace Splay.Interface

/--
The unconditional `v`-column theorem and the concrete-start `u` theorem
assemble into exactly the incidence API used by the activity proof.
-/
theorem initialSignificantColumnIncidence_of_u
    (uIncidence : InitialSignificantUColumnIncidenceHypothesis) :
    InitialSignificantColumnIncidenceHypothesis := by
  intro n params initial final finalLabels finalLedger finalClock
    finalEvents operations timedSnapshots initialState history
  exact
    ⟨significantVColumnIncidence history,
      uIncidence initialState history⟩

/--
A concrete-start `u`-column proof suffices for the final interface activity
bound.
-/
theorem activityBound_of_initialSignificantUColumnIncidence
    (shape : Shape)
    (uIncidence : InitialSignificantUColumnIncidenceHypothesis) :
    ActivityBound shape :=
  activityBound_of_initialSignificantColumnIncidence shape
    (initialSignificantColumnIncidence_of_u uIncidence)

/--
The sole remaining one-step root/pass-floor invariant implies the complete
interface activity theorem.
-/
theorem activityBound_of_clockCutRootStep
    (shape : Shape)
    (rootStep : ClockCutRootStepHypothesis) :
    ActivityBound shape :=
  activityBound_of_initialSignificantUColumnIncidence shape
    (initialSignificantUColumnIncidence_of_rootStep rootStep)

/--
The abstract pairing-interface activity bound, with constants uniform in the
carrier size and the value bound.
-/
theorem activityBound (shape : Shape) : ActivityBound shape :=
  activityBound_of_clockCutRootStep shape clockCutRootStep

end Splay.Interface
