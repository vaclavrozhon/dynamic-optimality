import Mathlib

/-!+Chronological occurrence windows constructed from a finite journal.

A ticket's window ends at the next ticket with the same key, or at the
final snapshot. This is the construction used for membership windows:
detachment and root intervals may be included until the next membership.
The same construction bounds growing-family overlap by using
`(creator, slot)` as the key. No overlap bound is an input.

The spatial protocol still has to supply the journal and identify actual
source memberships with its latest tickets. This file proves the temporal
properties of the constructed windows, not the entire Greedy trace.
-/

namespace GreedyMerge.Journal

structure Log (Key : Type*) where
  count : ℕ
  key : Fin count → Key
  joined : Fin count → ℕ
  horizon : ℕ
  chronological : StrictMono joined
  beforeEnd : ∀ ticket, joined ticket ≤ horizon

namespace Log

variable {Key : Type*} [DecidableEq Key] (log : Log Key)

def futureTimes (ticket : Fin log.count) : Finset ℕ :=
  insert log.horizon ((Finset.univ.filter fun next =>
    ticket < next ∧ log.key next = log.key ticket).image log.joined)

theorem futureTimes_nonempty (ticket : Fin log.count) :
    (log.futureTimes ticket).Nonempty := by
  exact ⟨log.horizon, Finset.mem_insert_self _ _⟩

def ended (ticket : Fin log.count) : ℕ :=
  (log.futureTimes ticket).min' (log.futureTimes_nonempty ticket)

theorem ended_le_horizon (ticket : Fin log.count) :
    log.ended ticket ≤ log.horizon := by
  exact Finset.min'_le _ _ (Finset.mem_insert_self _ _)

theorem joined_le_ended (ticket : Fin log.count) :
    log.joined ticket ≤ log.ended ticket := by
  apply Finset.le_min'
  intro time member
  rcases Finset.mem_insert.mp member with final | later
  · simpa only [final] using log.beforeEnd ticket
  · obtain ⟨next, selected, rfl⟩ := Finset.mem_image.mp later
    exact le_of_lt (log.chronological (Finset.mem_filter.mp selected).2.1)

theorem ended_le_next {ticket next : Fin log.count}
    (later : ticket < next) (same : log.key next = log.key ticket) :
    log.ended ticket ≤ log.joined next := by
  apply Finset.min'_le
  exact Finset.mem_insert_of_mem (Finset.mem_image.mpr
    ⟨next, Finset.mem_filter.mpr ⟨Finset.mem_univ _, later, same⟩, rfl⟩)

/-- Half-open windows of equal-key tickets never overlap. -/
theorem one_active {first second : Fin log.count} {time : ℕ}
    (same : log.key first = log.key second)
    (firstStart : log.joined first ≤ time) (firstEnd : time < log.ended first)
    (secondStart : log.joined second ≤ time) (secondEnd : time < log.ended second) :
    first = second := by
  rcases lt_trichotomy first second with before | equal | after
  · have bound := log.ended_le_next before same.symm
    omega
  · exact equal
  · have bound := log.ended_le_next after same
    omega

/-- Being inside the constructed window says exactly that no later
same-key entry has yet occurred, up to the final horizon. -/
theorem active_iff_latest (ticket : Fin log.count) (time : ℕ) :
    (log.joined ticket ≤ time ∧ time < log.ended ticket) ↔
      (log.joined ticket ≤ time ∧ time < log.horizon ∧
        ∀ next, ticket < next → log.key next = log.key ticket → time < log.joined next) := by
  constructor
  · rintro ⟨started, active⟩
    refine ⟨started, lt_of_lt_of_le active (log.ended_le_horizon ticket), ?_⟩
    intro next later same
    exact lt_of_lt_of_le active (log.ended_le_next later same)
  · rintro ⟨started, final, latest⟩
    refine ⟨started, ?_⟩
    have all : time + 1 ≤ log.ended ticket := by
      apply Finset.le_min'
      intro finish member
      rcases Finset.mem_insert.mp member with atEnd | future
      · omega
      · obtain ⟨next, selected, rfl⟩ := Finset.mem_image.mp future
        have chosen := (Finset.mem_filter.mp selected).2
        exact latest next chosen.1 chosen.2
    omega

/-- Starting from an ordinary indexed list always supplies distinct
chronological tickets. Extra idle snapshots can instead use any strictly
increasing timestamp function in `Log`. -/
def ofList (keys : List Key) : Log Key where
  count := keys.length
  key := keys.get
  joined := Fin.val
  horizon := keys.length
  chronological := fun _ _ h => h
  beforeEnd := fun ticket => Nat.le_of_lt ticket.isLt

end Log

/-- With a fixed finite set of slots, the constructed windows of all
families of one creator have overlap at most the number of slots. -/
theorem creator_slot_overlap {Record Slot : Type*} [DecidableEq Record]
    [DecidableEq Slot] [Fintype Slot] (log : Log (Record × Slot))
    (creator : Record) (time : ℕ) :
    (Finset.univ.filter fun ticket =>
      (log.key ticket).1 = creator ∧ log.joined ticket ≤ time ∧
      time < log.ended ticket).card ≤ Fintype.card Slot := by
  classical
  let active := {ticket : Fin log.count //
    (log.key ticket).1 = creator ∧ log.joined ticket ≤ time ∧
    time < log.ended ticket}
  have injective : Function.Injective (fun ticket : active => (log.key ticket.val).2) := by
    intro first second sameSlot
    apply Subtype.ext
    have sameKey : log.key first.val = log.key second.val := by
      apply Prod.ext
      · exact first.property.1.trans second.property.1.symm
      · exact sameSlot
    exact log.one_active sameKey first.property.2.1 first.property.2.2
      second.property.2.1 second.property.2.2
  have bound := Fintype.card_le_of_injective _ injective
  simpa only [active, Fintype.card_subtype] using bound

end GreedyMerge.Journal

#print axioms GreedyMerge.Journal.Log.one_active
#print axioms GreedyMerge.Journal.Log.active_iff_latest
#print axioms GreedyMerge.Journal.creator_slot_overlap
