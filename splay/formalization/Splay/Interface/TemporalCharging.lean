import Splay.Interface.ShiftAccounting
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Splay.Interface

open scoped BigOperators

/--
A temporal charge is a signed incidence vector over a finite chronological
list of unit-change events.  Coefficients `-1`, `0`, and `1` encode whether an
event lies in an oriented join-time interval.
-/
abbrev TemporalCharge (eventCount : ℕ) :=
  Fin eventCount → ℤ

/-- Dot product of one temporal incidence vector with the event deltas. -/
def temporalShift {eventCount : ℕ}
    (deltas charge : Fin eventCount → ℤ) : ℤ :=
  ∑ event, charge event * deltas event

/-- Sum of all interval shifts in a finite charge family. -/
def totalTemporalShift {eventCount : ℕ}
    (deltas : Fin eventCount → ℤ)
    (charges : List (TemporalCharge eventCount)) : ℤ :=
  (charges.map fun charge => temporalShift deltas charge).sum

private theorem totalTemporalShift_swap
    {eventCount : ℕ} (deltas : Fin eventCount → ℤ)
    (charges : List (TemporalCharge eventCount)) :
    totalTemporalShift deltas charges =
      ∑ event,
        (charges.map fun charge =>
          charge event * deltas event).sum := by
  induction charges with
  | nil =>
      simp [totalTemporalShift, temporalShift]
  | cons charge charges ih =>
      change
        temporalShift deltas charge +
            totalTemporalShift deltas charges =
          Finset.univ.sum fun event : Fin eventCount =>
            charge event * deltas event +
              (charges.map
                (fun later => later event * deltas event)).sum
      rw [ih]
      simp only [temporalShift, Finset.sum_add_distrib]

private theorem abs_weighted_column_le
    {eventCount : ℕ} (deltas : Fin eventCount → ℤ)
    (charges : List (TemporalCharge eventCount))
    (event : Fin eventCount)
    (deltaUnit : |deltas event| ≤ 1) :
    |(charges.map fun charge =>
        charge event * deltas event).sum| ≤
      (charges.map fun charge => |charge event|).sum := by
  induction charges with
  | nil =>
      simp
  | cons charge charges ih =>
      simp only [List.map_cons, List.sum_cons]
      calc
        |charge event * deltas event +
            (charges.map fun later =>
              later event * deltas event).sum| ≤
            |charge event * deltas event| +
              |(charges.map fun later =>
                later event * deltas event).sum| :=
          abs_add_le _ _
        _ ≤
            |charge event * deltas event| +
              (charges.map fun later => |later event|).sum :=
          add_le_add_right ih _
        _ ≤
            |charge event| +
              (charges.map fun later => |later event|).sum := by
          apply add_le_add_left
          rw [abs_mul]
          exact
            mul_le_of_le_one_right (abs_nonneg (charge event))
              deltaUnit

/--
Finite double-counting lemma used by both significant shift arguments.

If every event is a unit change and belongs (with either orientation) to at
most `multiplicity` charge intervals, the total signed shift is at most
`multiplicity * eventCount`.  Negative contributions are retained and only
help the upper bound.
-/
theorem totalTemporalShift_le_incidence
    {eventCount multiplicity : ℕ}
    (deltas : Fin eventCount → ℤ)
    (charges : List (TemporalCharge eventCount))
    (deltaUnit : ∀ event, |deltas event| ≤ 1)
    (incidence :
      ∀ event,
        (charges.map fun charge => |charge event|).sum ≤
          (multiplicity : ℤ)) :
    totalTemporalShift deltas charges ≤
      ((multiplicity * eventCount : ℕ) : ℤ) := by
  rw [totalTemporalShift_swap]
  calc
    (∑ event,
        (charges.map fun charge =>
          charge event * deltas event).sum) ≤
        ∑ _event : Fin eventCount, (multiplicity : ℤ) := by
      apply Finset.sum_le_sum
      intro event _member
      calc
        (charges.map fun charge =>
              charge event * deltas event).sum ≤
            |(charges.map fun charge =>
              charge event * deltas event).sum| :=
          le_abs_self _
        _ ≤
            (charges.map fun charge => |charge event|).sum :=
          abs_weighted_column_le deltas charges event
            (deltaUnit event)
        _ ≤ (multiplicity : ℤ) :=
          incidence event
    _ = ((multiplicity * eventCount : ℕ) : ℤ) := by
      simp
      ring

/--
Every Boolean classification gives an exact permutation into the selected
and rejected sublists.  Mapping this permutation is the canonical constructor
for snapshot-significance partitions.
-/
theorem List.perm_filter_append_filter_not
    {α : Type*} (predicate : α → Bool) (values : List α) :
    values.Perm
      (values.filter predicate ++
        values.filter fun value => !predicate value) := by
  induction values with
  | nil =>
      simp
  | cons value values ih =>
      cases selected : predicate value with
      | false =>
          simp only [List.filter_cons, selected, Bool.not_false,
            Bool.false_eq_true, ↓reduceIte]
          refine (List.Perm.cons value ih).trans ?_
          simpa [List.append_assoc] using
            (List.perm_append_comm
              (l₁ := [value])
              (l₂ := values.filter predicate)).append_right
                (values.filter fun item => !predicate item)
      | true =>
          simpa [selected] using List.Perm.cons value ih

end Splay.Interface
