import ChronologicalJournal
import ExecutionTrace

/-!
Construct the creator-memory ledger from persistent membership tickets.
The chronological fold stores the latest ticket, rather than accepting a
numerical memory equality as an unexplained aggregate premise. An old
source membership whose next-entry window reaches the new entry is exactly
the ticket retrieved by this fold. Its immutable stored creator label then
supplies the loser-shift frame used by the finite accounting theorem.
-/

namespace GreedyMerge.Journal

open GreedyForest.Execution

variable {Record Ticket Edge : Type*} [DecidableEq Record]

def latest (record : Ticket → Record) (initial : Record → Option Ticket) :
    List Ticket → Record → Option Ticket
  | [] => initial
  | ticket :: rest => latest record (Function.update initial (record ticket) (some ticket)) rest

theorem latest_append (record : Ticket → Record) (initial : Record → Option Ticket)
    (first second : List Ticket) :
    latest record initial (first ++ second) = latest record (latest record initial first) second := by
  induction first generalizing initial with
  | nil => rfl
  | cons ticket rest ih => exact ih _

theorem latest_unchanged (record : Ticket → Record) (initial : Record → Option Ticket)
    (tickets : List Ticket) (key : Record)
    (absent : ∀ ticket ∈ tickets, record ticket ≠ key) :
    latest record initial tickets key = initial key := by
  induction tickets generalizing initial with
  | nil => rfl
  | cons ticket rest ih =>
      rw [latest, ih _ (fun t ht => absent t (List.mem_cons_of_mem _ ht))]
      exact Function.update_of_ne (Ne.symm (absent ticket (List.mem_cons_self))) _ _

theorem latest_of_last (record : Ticket → Record) (joined : Ticket → ℕ)
    (initial : Record → Option Ticket) (tickets : List Ticket) (old : Ticket)
    (member : old ∈ tickets)
    (ordered : tickets.Pairwise (fun a b => joined a < joined b))
    (maximal : ∀ ticket ∈ tickets, record ticket = record old → joined ticket ≤ joined old) :
    latest record initial tickets (record old) = some old := by
  induction tickets generalizing initial with
  | nil => simp at member
  | cons ticket rest ih =>
      rcases List.pairwise_cons.mp ordered with ⟨headBefore, tailOrdered⟩
      rcases List.mem_cons.mp member with equal | tailMember
      · subst ticket
        rw [latest, latest_unchanged]
        · simp
        · intro later hlater same
          have lower := headBefore later hlater
          have upper := maximal later (List.mem_cons_of_mem _ hlater) same
          omega
      · exact ih _ tailMember tailOrdered
          (fun later hlater => maximal later (List.mem_cons_of_mem _ hlater))

def readMemory (fallback : ℤ) (stored : Ticket → ℤ)
    (pointer : Record → Option Ticket) : Record → ℤ :=
  fun record => (pointer record).elim fallback stored

theorem readMemory_update (fallback : ℤ) (stored : Ticket → ℤ)
    (pointer : Record → Option Ticket) (record : Record) (ticket : Ticket) :
    readMemory fallback stored (Function.update pointer record (some ticket)) =
      Function.update (readMemory fallback stored pointer) record (stored ticket) := by
  funext key
  by_cases same : key = record
  · subst key; simp [readMemory]
  · simp [readMemory, Function.update_of_ne same]

theorem ledger_of_latest [Fintype Record]
    (K : ℤ) (record : Ticket → Record) (stored : Ticket → ℤ)
    (origin : Ticket → Option Edge) (shift : Edge → ℤ)
    (initial : Record → Option Ticket) (tickets : List Ticket)
    (bounded : ∀ ticket ∈ tickets, 1 ≤ stored ticket ∧ stored ticket ≤ K)
    (frame : ∀ pre ticket post, tickets = pre ++ ticket :: post →
      ∀ edge, origin ticket = some edge →
      ∃ previous, latest record initial pre (record ticket) = some previous ∧
        shift edge = stored ticket - stored previous) :
    ValidEntryLedger K shift (readMemory K stored initial)
      (tickets.map fun ticket => EntryEvent.mk (record ticket) (stored ticket) (origin ticket)) := by
  induction tickets generalizing initial with
  | nil => trivial
  | cons ticket rest ih =>
      refine ⟨bounded ticket (List.mem_cons_self), ?_, ?_⟩
      · intro edge bad
        obtain ⟨previous, lookup, difference⟩ := frame [] ticket rest rfl edge bad
        change initial (record ticket) = some previous at lookup
        simpa only [readMemory, lookup, Option.elim_some] using difference
      · rw [← readMemory_update]
        apply ih _ (fun t ht => bounded t (List.mem_cons_of_mem _ ht))
        intro pre next post decomposition edge bad
        have full : ticket :: rest = (ticket :: pre) ++ next :: post := by
          simp only [List.cons_append, decomposition]
        exact frame (ticket :: pre) next post full edge bad

/-- A persistent source ticket valid up to this entry time is the exact
latest same-record ticket in its chronological prefix. -/
theorem Log.latest_source (log : Log Record) (tickets : List (Fin log.count))
    (complete : ∀ ticket, ticket ∈ tickets)
    (ordered : tickets.Pairwise (· < ·))
    (pre : List (Fin log.count)) (entry : Fin log.count) (post : List (Fin log.count))
    (decomposition : tickets = pre ++ entry :: post)
    (source : Fin log.count) (earlier : source < entry)
    (sameRecord : log.key source = log.key entry)
    (live : log.joined entry ≤ log.ended source) :
    latest log.key (fun _ => none) pre (log.key entry) = some source := by
  rw [decomposition] at ordered
  rcases List.pairwise_append.mp ordered with ⟨preOrder, tailOrder, cross⟩
  have beforeEntry : ∀ ticket ∈ pre, ticket < entry := by
    intro ticket member
    exact cross ticket member entry (List.mem_cons_self)
  have afterEntry : ∀ ticket ∈ post, entry < ticket := (List.pairwise_cons.mp tailOrder).1
  have sourceInPre : source ∈ pre := by
    have full := complete source
    rw [decomposition, List.mem_append, List.mem_cons] at full
    rcases full with before | equal | after
    · exact before
    · subst source; exact False.elim (lt_irrefl _ earlier)
    · have h := afterEntry source after
      exact False.elim (lt_asymm earlier h)
  rw [← sameRecord]
  apply latest_of_last log.key log.joined _ pre source sourceInPre
  · exact preOrder.imp (fun h => log.chronological h)
  · intro ticket member same
    by_cases later : source < ticket
    · have next := log.ended_le_next later same
      have lower := log.chronological (beforeEntry ticket member)
      omega
    · exact log.chronological.monotone (le_of_not_gt later)

/-- The complete numeric ledger is derived from local source tickets and
their actual next-entry windows. It is not an extra trace assumption. -/
theorem Log.entry_ledger [Fintype Record] (log : Log Record)
    (K : ℤ) (stored : Fin log.count → ℤ) (origin : Fin log.count → Option Edge)
    (source : Edge → Fin log.count) (shift : Edge → ℤ)
    (bounded : ∀ ticket, 1 ≤ stored ticket ∧ stored ticket ≤ K)
    (causal : ∀ ticket edge, origin ticket = some edge → source edge < ticket)
    (same : ∀ ticket edge, origin ticket = some edge → log.key (source edge) = log.key ticket)
    (live : ∀ ticket edge, origin ticket = some edge →
      log.joined ticket ≤ log.ended (source edge))
    (difference : ∀ ticket edge, origin ticket = some edge →
      shift edge = stored ticket - stored (source edge)) :
    ValidEntryLedger K shift (fun _ => K)
      ((List.ofFn (fun ticket : Fin log.count => ticket)).map fun ticket =>
        EntryEvent.mk (log.key ticket) (stored ticket) (origin ticket)) := by
  apply ledger_of_latest K log.key stored origin shift (fun _ => none) _
    (fun ticket _ => bounded ticket)
  intro pre ticket post decomposition edge bad
  refine ⟨source edge, ?_, difference ticket edge bad⟩
  exact log.latest_source _ (fun ticket => List.mem_ofFn.mpr ⟨ticket, rfl⟩)
    (List.pairwise_ofFn.mpr (fun _ _ h => h)) pre ticket post decomposition
    (source edge) (causal ticket edge bad) (same ticket edge bad) (live ticket edge bad)

/-- Instantiate stored memory with the actual creator's label at the
immutable join snapshot. The bad-entry frame identifies the new creator
with the current winner and its timestamp with the link timestamp. Thus
the loser shift is the exact expression required by `AccountingTrace`. -/
theorem Log.creator_snapshot_ledger [Fintype Record] (log : Log Record)
    (K : ℤ) (label : Record → ℕ → ℤ) (creator : Fin log.count → Record)
    (origin : Fin log.count → Option Edge)
    (source winner : Edge → Fin log.count) (linkTime : Edge → ℕ)
    (labelBounds : ∀ record time, time ≤ log.horizon →
      1 ≤ label record time ∧ label record time ≤ K)
    (causal : ∀ ticket edge, origin ticket = some edge → source edge < ticket)
    (same : ∀ ticket edge, origin ticket = some edge → log.key (source edge) = log.key ticket)
    (live : ∀ ticket edge, origin ticket = some edge →
      log.joined ticket ≤ log.ended (source edge))
    (newCreator : ∀ ticket edge, origin ticket = some edge →
      creator ticket = log.key (winner edge))
    (newTime : ∀ ticket edge, origin ticket = some edge → log.joined ticket = linkTime edge) :
    ValidEntryLedger K
      (fun edge => label (log.key (winner edge)) (linkTime edge) -
        label (creator (source edge)) (log.joined (source edge)))
      (fun _ => K)
      ((List.ofFn (fun ticket : Fin log.count => ticket)).map fun ticket =>
        EntryEvent.mk (log.key ticket) (label (creator ticket) (log.joined ticket)) (origin ticket)) := by
  apply log.entry_ledger K _ origin source _
    (fun ticket => labelBounds _ _ (log.beforeEnd ticket)) causal same live
  intro ticket edge bad
  rw [newCreator ticket edge bad, newTime ticket edge bad]

end GreedyMerge.Journal

#print axioms GreedyMerge.Journal.Log.latest_source
#print axioms GreedyMerge.Journal.Log.entry_ledger
#print axioms GreedyMerge.Journal.Log.creator_snapshot_ledger
