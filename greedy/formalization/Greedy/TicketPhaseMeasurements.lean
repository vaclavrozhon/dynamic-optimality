import Greedy.TicketAccess

/-! Actual membership observations equal the geometric family win counts. -/

namespace Greedy.RunJournal

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical Splay.Analysis
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.HeapAllocation
open GreedyMerge.ActualLinks GreedyMerge.PathPlateau GreedyMerge.PlateauBridge
open GreedyMerge.AccessSourceAccounting GreedyMerge.Fringe GreedyMerge.Fringe.Schedule
open EntryJournal RestorationJournal
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem ticket_phase_eq {n : ℕ} (before : Execution.State n) (request : Fin n) (K : ℤ)
    (root : before.comparator.HasRoot request.val)
    (decomposition : Decomposition before.refined.tree request.val)
    (data : AccessScheduleData before.comparator before.refined.tree (Execution.afterRefinement before request).tree decomposition)
    (valid : before.Valid) (pointer : External n → MembershipPointer.Ticket) (ticket : MembershipPointer.Ticket)
    (synced : MembershipPointer.Synced pointer (prepared before request)) :
    (∑ i : Fin data.events.length,
      SourceCensus.ticketWeight (prepared before request) (Execution.source request) (MembershipPointer.atKey pointer) ticket (eventKeys (data.events.get i))) =
      (WinnerTickets.familyWins data (prepared before request) (Execution.source request) ticket.1 ticket.2 : ℤ) := by
  have views := actual_allocated_sources before.comparator before.refined.tree _ decomposition data
    (Execution.source request) rfl (Execution.root_minimum _ request root) before.blocks valid.1 K before.next valid.2.2.1
  have converted := convertRoot_eq_convertHeap before.comparator.externalDepth (Execution.source request) before.next before.blocks
  change convertRoot before.comparator.externalDepth (Execution.source request) _ _ before.blocks = prepared before request at converted
  dsimp only at views
  rw [converted] at views
  obtain ⟨leftView⟩ := views.1
  obtain ⟨rightView⟩ := views.2
  have inventory := convertHeap_inventory before.comparator.externalDepth
    (fun owner _ => decide (owner = Execution.source request)) before.next before.blocks valid.2.2.1
  have ids (side : Bool) := inventory_shrinking_nodup (prepared before request) _ inventory (Execution.source request) side
  have ready := CreatorPhase.prepared_ready before request valid
  have upper := data.right.lower_le_upper
  have leftEq := SourceCensus.ticket_side_sum
    (canonicalParent (Snapshot.ofTree before.comparator) before.refined.tree)
    (prepared before request) (Execution.source request) true ready.sound ready.valid
    leftView (ids true) data.owner data.projection.2.1
    (fun q lower bound => data.localOwners q lower (by omega)) pointer synced ticket
  have rightEq := SourceCensus.ticket_side_sum
    (canonicalParent (Snapshot.ofTree before.comparator) before.refined.tree)
    (prepared before request) (Execution.source request) false ready.sound ready.valid
    rightView (ids false) data.owner data.projection.2.2
    (fun q lower bound => data.localOwners q (by omega) bound) pointer synced ticket
  have geometry := AccessTrace.geometry data (Execution.source request) rfl (Execution.root_minimum _ request root)
  rw [AtomicAccess.sum_two_sides data (Execution.source request) geometry,
    WinnerTickets.familyWins]
  push_cast
  rw [SourceCensus.sum_pieces]
  simp only [WinnerTickets.part, if_true, Bool.false_eq_true, if_false]
  exact (congrArg₂ (· + ·) leftEq rightEq).symm


end Greedy.RunJournal

namespace Greedy.TicketJournal

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.HeapAllocation
open GreedyMerge.ActualLinks GreedyMerge.PathPlateau GreedyMerge.AccessSourceAccounting
open scoped BigOperators

theorem access_remaining {n : ℕ} (before : Execution.State n) (request : Fin n) (K : ℤ)
    (root : before.comparator.HasRoot request.val)
    (decomposition : Decomposition before.refined.tree request.val)
    (data : AccessScheduleData before.comparator before.refined.tree (Execution.afterRefinement before request).tree decomposition)
    (valid : before.Valid) (pointer : External n → Ticket) (synced : MembershipPointer.Synced pointer before.blocks)
    (ticket : Ticket) :
    WinnerCredit.remaining (access before request K decomposition data pointer) ticket =
      WinnerTickets.familyWins data (RunJournal.prepared before request) (Execution.source request) ticket.1 ticket.2 := by
  classical
  have prepared := MembershipStamps.convertHeap_property before.comparator.externalDepth
    (fun owner _ => decide (owner = Execution.source request)) before.next before.blocks synced
  have measured := RunJournal.ticket_phase_eq before request K root decomposition data valid pointer ticket prepared
  have erasedCounts := links_remaining before.comparator.externalDepth K (Execution.source request)
    (fun event => decide (event.2.val < (Execution.source request).val))
    (AccessTrace.kind (RunJournal.prepared before request) (Execution.source request)) pointer before.clock
    (RunJournal.prepared before request) data.events ticket
  change WinnerCredit.remaining (access before request K decomposition data pointer) ticket = _ at erasedCounts
  rw [erasedCounts]
  apply Int.natCast_inj.mp
  rw [← measured, AtomicAccess.indexed_sum data.events
    (fun event => SourceCensus.ticketWeight (RunJournal.prepared before request) (Execution.source request)
      (MembershipPointer.atKey pointer) ticket (eventKeys event))]
  rw [Nat.cast_list_sum, List.map_map]
  congr 1
  apply List.map_congr_left
  intro event _
  have matching := SourceCensus.sameBlock_keys (RunJournal.prepared before request) (Execution.source request) event
  dsimp only [Function.comp_def, SourceCensus.ticketWeight, eventKeys] at ⊢ matching
  rw [MembershipPointer.atKey_record]
  by_cases same : AccessTrace.SameBlock (RunJournal.prepared before request) (Execution.source request) event
  · simp only [AccessTrace.kind, if_pos same, matching.mp same, true_and]
    split_ifs <;> rfl
  · simp only [AccessTrace.kind, if_neg same, reduceCtorEq, false_and, if_false,
      mt matching.mpr same, Nat.cast_zero]

end Greedy.TicketJournal
