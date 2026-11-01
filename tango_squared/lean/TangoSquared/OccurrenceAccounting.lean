import TangoSquared.PeriodicAccounting
import TangoSquared.GapRecords
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Fin

/-!
# Event occurrences at actual query times

`eventSum` is represented as the cardinality of a finite set of chronological
(time, event-tag) pairs.  A concrete payment injection into these pairs therefore
has exactly the same budget, including in windows spanning several periods.
-/

namespace TangoSquared

open Primary Witnesses

/-- The actual history immediately before an indexed query of the suffix. -/
def queryHistory (history xs : List Key) (i : Fin xs.length) : List Key :=
  history ++ xs.take i.val

/-- The event set at an actual indexed query, retaining the complete preceding history. -/
noncomputable def eventsAt (H : Nat) (qs : Finset Gadget) (history xs : List Key)
    (i : Fin xs.length) : Finset EventTag :=
  activeEvents H qs (queryHistory history xs i) xs[i]

/-- The recursive event sum equals its ordinary indexed finite sum. -/
theorem eventSum_eq_sum (H : Nat) (qs : Finset Gadget) (history xs : List Key) :
    eventSum H qs history xs = ∑ i : Fin xs.length, (eventsAt H qs history xs i).card := by
  induction xs generalizing history with
  | nil => simp [eventSum]
  | cons x xs ih =>
    simp only [eventSum, List.length_cons]
    rw [Fin.sum_univ_succ]
    rw [ih]
    simp only [eventsAt, queryHistory, Fin.val_zero, List.take_zero, List.append_nil,
      Fin.val_succ, List.take_succ_cons]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    congr 2
    simp [List.append_assoc]

/-- An event occurrence is its actual time and its entry/delayed coarse-cell tag. -/
abbrev EventOccurrence (xs : List Key) := (_ : Fin xs.length) × EventTag

/-- All actual event occurrences in the suffix. -/
noncomputable def eventOccurrences (H : Nat) (qs : Finset Gadget) (history xs : List Key) :
    Finset (EventOccurrence xs) :=
  Finset.univ.sigma (eventsAt H qs history xs)

theorem mem_eventOccurrences {H : Nat} {qs : Finset Gadget} {history xs : List Key}
    {occurrence : EventOccurrence xs} :
    occurrence ∈ eventOccurrences H qs history xs ↔
      occurrence.2 ∈ eventsAt H qs history xs occurrence.1 := by
  simp [eventOccurrences]

/-- Exact cardinality, with time multiplicity retained. -/
theorem card_eventOccurrences (H : Nat) (qs : Finset Gadget) (history xs : List Key) :
    (eventOccurrences H qs history xs).card = eventSum H qs history xs := by
  rw [eventSum_eq_sum]
  exact Finset.card_sigma _ _

/-- Any injective assignment of concrete payments to actual time-tag events is
bounded by `eventSum`. The remaining use-site obligation is occurrence matching,
not an assumed BST lower bound. -/
theorem payment_card_le_eventSum {ι : Type*} [DecidableEq ι]
    (payments : Finset ι) (H : Nat) (qs : Finset Gadget) (history xs : List Key)
    (assign : ι → EventOccurrence xs)
    (mem : ∀ i ∈ payments,
      (assign i).2 ∈ eventsAt H qs history xs (assign i).1)
    (injective : Set.InjOn assign (payments : Set ι)) :
    payments.card ≤ eventSum H qs history xs := by
  rw [← card_eventOccurrences]
  apply Finset.card_le_card_of_injOn assign
  · intro i hi
    exact mem_eventOccurrences.mpr (mem i hi)
  · exact injective

/-- A concrete entry record supplies its actual indexed event occurrence. -/
theorem entry_record_mem_eventsAt {H : Nat} {qs : Finset Gadget} {history xs : List Key}
    (i : Fin xs.length) {q : Gadget} {y : Key} (hq : q ∈ qs)
    (record : EntryEvent (queryHistory history xs i) xs[i] q y) :
    Sum.inl q ∈ eventsAt H qs history xs i :=
  entry_mem_activeEvents hq record

/-- A concrete delayed record supplies its actual indexed coarse-cell event. -/
theorem delayed_record_mem_eventsAt {H : Nat} {qs : Finset Gadget} {history xs : List Key}
    (i : Fin xs.length) {q : Gadget} {y : Key} (hq : q ∈ qs)
    (record : DelayedEvent (queryHistory history xs i) xs[i] q y)
    (leaves : OnLeaves H (queryHistory history xs i ++ [xs[i]])) :
    Sum.inr (q, q.coarse y) ∈ eventsAt H qs history xs i :=
  delayed_mem_activeEvents hq record leaves

end TangoSquared
