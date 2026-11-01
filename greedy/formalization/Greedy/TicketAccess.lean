import Greedy.TicketLinkRun
import Greedy.WinnerPointerCensus
import Greedy.AccessPhaseSum
import Greedy.AccessMeasurements

/-! Membership annotations agree with every link of an actual geometric access. -/

namespace Greedy.TicketJournal

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.ActualLinks
open GreedyMerge.HeapAllocation EntryJournal RestorationJournal
open GreedyMerge.AccessSourceAccounting GreedyMerge.PathPlateau

noncomputable def access {n : ℕ} (before : Execution.State n) (request : Fin n) (K : ℤ)
    (decomposition : Decomposition before.refined.tree request.val)
    (data : AccessScheduleData before.comparator before.refined.tree (Execution.afterRefinement before request).tree decomposition)
    (oldTicket : External n → Ticket) : List (Action n) :=
  links before.comparator.externalDepth K (Execution.source request)
    (fun event => decide (event.2.val < (Execution.source request).val))
    (AccessTrace.kind (RunJournal.prepared before request) (Execution.source request)) oldTicket
    before.clock (RunJournal.prepared before request) data.events

theorem access_erases {n : ℕ} (before : Execution.State n) (request : Fin n) (K : ℤ)
    (decomposition : Decomposition before.refined.tree request.val)
    (data : AccessScheduleData before.comparator before.refined.tree (Execution.afterRefinement before request).tree decomposition)
    (oldTicket : External n → Ticket) :
    WinnerCredit.erase (access before request K decomposition data oldTicket) = RunJournal.access before request decomposition data :=
  links_erases ..

theorem access_paired {n : ℕ} (before : Execution.State n) (request : Fin n) (K : ℤ)
    (decomposition : Decomposition before.refined.tree request.val)
    (data : AccessScheduleData before.comparator before.refined.tree (Execution.afterRefinement before request).tree decomposition)
    (oldTicket : External n → Ticket) :
    WinnerCredit.Paired (access before request K decomposition data oldTicket) := links_paired ..

theorem access_correct {n : ℕ} (before : Execution.State n) (request : Fin n) (K : ℤ)
    (root : before.comparator.HasRoot request.val)
    (decomposition : Decomposition before.refined.tree request.val)
    (data : AccessScheduleData before.comparator before.refined.tree
      (Execution.afterRefinement before request).tree decomposition)
    (valid : before.Valid) (state : State n)
    (agree : state.account.label = labels before.comparator K before.blocks)
    (synced : MembershipPointer.Synced state.ticket before.blocks) :
    WinnerCredit.Legal state (access before request K decomposition data state.ticket) ∧
    MembershipPointer.Synced (WinnerCredit.run state (access before request K decomposition data state.ticket)).ticket
      (Execution.afterAccess before request K decomposition data).blocks := by
  let source := Execution.source request
  let selected := fun (owner : External n) (_ : Bool) => decide (owner = source)
  let prepared := RunJournal.prepared before request
  have pointer : MembershipPointer.Synced state.ticket prepared :=
    MembershipStamps.convertHeap_property before.comparator.externalDepth selected before.next before.blocks synced
  have ready := CreatorPhase.prepared_ready before request valid
  have geometry := AccessTrace.geometry data source rfl (Execution.root_minimum _ request root)
  have converted := convertRoot_eq_convertHeap before.comparator.externalDepth source before.next before.blocks
  change convertRoot before.comparator.externalDepth source (rootNames source before.next)
    (rootNames source before.next) before.blocks = prepared at converted
  have empty : ∀ side, growerEntries (prepared source side).grower = [] := by
    intro side
    rw [← converted]
    exact convertRoot_empty _ _ _ _ _ side
  let sideOf := fun event : External n × External n => decide (event.2.val < source.val)
  apply links_correct (canonicalParent (Snapshot.ofTree before.comparator) before.refined.tree)
    before.comparator.externalDepth K source sideOf before.clock prepared data.events
    (AccessTrace.roots data) (AccessTrace.survivors data) geometry.run geometry.unique
  · intro record member
    exact hasChild_parent _ _ source record ((geometry.children _).mpr member)
  · intro record member
    exact hasChild_ne_owner _ _ source record ((geometry.children _).mpr member)
  · exact ready.sound
  · intro record owner parent
    exact ready.complete record owner parent (by simp)
  · exact ready.persistent
  · exact empty
  · intros; rfl
  · exact orderedPrefixes_of_canonical (Snapshot.ofTree before.comparator) before.refined.tree source sideOf prepared
      ready.sound ready.valid ready.persistent empty before.comparator.externalDepth data.events
      (AccessTrace.roots data) (AccessTrace.survivors data) geometry.run geometry.children _ before.clock geometry.arrivals
  · intros; rfl
  · intro record
    rw [agree, ← RunJournal.prepared_labels before request K]
    rfl
  · exact pointer

end Greedy.TicketJournal
