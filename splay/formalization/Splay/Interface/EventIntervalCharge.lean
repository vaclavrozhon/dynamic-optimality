import Splay.Interface.TemporalCharging

namespace Splay.Interface

open scoped BigOperators

/--
The chronological delta vector associated with a concrete event list.

Keeping the vector indexed by `Fin events.length` makes it directly usable by
`temporalShift`, while `delta` itself can remain completely generic.
-/
def eventDeltaVector {α : Type*}
    (events : List α) (delta : α → ℤ) :
    Fin events.length → ℤ :=
  fun event => delta (events.get event)

/--
The incidence vector of the selected events whose chronological indices lie
in the half-open interval `[start, stop)`.
-/
def eventIntervalCharge {α : Type*}
    (events : List α) (selected : α → Bool)
    (start stop : ℕ) : TemporalCharge events.length :=
  fun event =>
    if start ≤ event.val ∧ event.val < stop ∧
        selected (events.get event)
    then 1
    else 0

/-- Sum of the deltas of the selected events in a list. -/
def selectedEventDeltaSum {α : Type*}
    (events : List α) (delta : α → ℤ)
    (selected : α → Bool) : ℤ :=
  ((events.filter selected).map delta).sum

/--
An interval charge computes exactly the selected delta sum on the
corresponding list slice.
-/
theorem temporalShift_eventIntervalCharge
    {α : Type*}
    (events : List α) (delta : α → ℤ)
    (selected : α → Bool) (start stop : ℕ)
    (start_le_stop : start ≤ stop)
    (stop_le_length : stop ≤ events.length) :
    temporalShift
        (eventDeltaVector events delta)
        (eventIntervalCharge events selected start stop) =
      selectedEventDeltaSum
        ((events.take stop).drop start) delta selected := by
  induction events generalizing start stop with
  | nil =>
      have stop_eq : stop = 0 := Nat.eq_zero_of_le_zero stop_le_length
      subst stop
      have start_eq : start = 0 := Nat.eq_zero_of_le_zero start_le_stop
      subst start
      simp [temporalShift, eventDeltaVector, eventIntervalCharge,
        selectedEventDeltaSum]
  | cons event events ih =>
      cases stop with
      | zero =>
          have start_eq : start = 0 :=
            Nat.eq_zero_of_le_zero start_le_stop
          subst start
          simp [temporalShift, eventDeltaVector, eventIntervalCharge,
            selectedEventDeltaSum]
      | succ stop =>
          have stop_le_tail : stop ≤ events.length := by
            simpa using stop_le_length
          cases start with
          | zero =>
              have tailEq :=
                ih (start := 0) (stop := stop) (Nat.zero_le _)
                  stop_le_tail
              simp [temporalShift, eventDeltaVector,
                eventIntervalCharge, selectedEventDeltaSum] at tailEq
              cases selectedEq : selected event <;>
                simp [temporalShift, eventDeltaVector,
                  eventIntervalCharge, selectedEventDeltaSum,
                  Fin.sum_univ_succ, tailEq, selectedEq]
          | succ start =>
              have start_le_tail_stop : start ≤ stop := by
                exact Nat.succ_le_succ_iff.mp start_le_stop
              have tailEq :=
                ih (start := start) (stop := stop)
                  start_le_tail_stop stop_le_tail
              simp [temporalShift, eventDeltaVector,
                eventIntervalCharge, selectedEventDeltaSum] at tailEq
              simp [temporalShift, eventDeltaVector, eventIntervalCharge,
                selectedEventDeltaSum, Fin.sum_univ_succ,
                tailEq]

end Splay.Interface
