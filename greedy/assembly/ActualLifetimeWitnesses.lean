import ConcreteDepartureLifetime
import ActualLinkClasses
import MappedConsolidation

/-!
Extract lifetime source witnesses from actual indexed schedule endpoints
and immutable source Entry records. Distinct winner/loser tickets follow
from the executed strict link and the block's actual history order.
-/
namespace GreedyMerge.HistoryProcess

open OrderedBlocks FrozenHistory GreedyForest
open GreedyMerge.Primitives (Entry)

theorem HistMonotone.joined_injective {orientation : Bool} {members : List Entry}
    (history : HistMonotone orientation members) :
    Set.InjOn Entry.joined {entry | entry∈members} := by
  have pair : members.Pairwise (fun first second => first.joined≠second.joined) := by
    apply history.imp
    intro first second ordered
    cases orientation with
    | false => exact Nat.ne_of_gt ordered
    | true => exact Nat.ne_of_lt ordered
  have unique : (members.map Entry.joined).Nodup := by
    simpa only [List.nodup_iff_pairwise_ne,List.pairwise_map] using pair
  exact List.inj_on_of_nodup_map unique

theorem entry_join_mem {block : Frozen} {entry : Entry} (member : entry∈block.members) :
    entry.joined∈joins block :=
  List.mem_toFinset.mpr (List.mem_map.mpr ⟨entry,member,rfl⟩)

/-- An actual indexed internal link supplies both historical tickets and
proves they are distinct; this is the positive winner-stage witness
consumed by winnerLifetime_of_completed. -/
theorem SourceConsolidation.winner_ticket_witness {before after : List Frozen} {source : Frozen}
    (phase : SourceConsolidation before after source)
    (orientation : Bool) (history : HistMonotone orientation source.members)
    (event : Fin phase.events.length) (winner loser : Entry)
    (winnerMember : winner∈source.members) (loserMember : loser∈source.members)
    (winnerKey : phase.record (phase.events.get event).1=winner.key)
    (loserKey : phase.record (phase.events.get event).2=loser.key) :
    winner.joined∈joins source ∧ ∃ other∈joins source, winner.joined≠other := by
  have endpoints := phase.links.event_members (phase.events.get event) (List.get_mem _ _)
  have differentAtoms : (phase.events.get event).1 ≠ (phase.events.get event).2 := by
    have bound := GreedyMerge.MappedConsolidation.run_event_rank_lt phase.links
      (phase.events.get event) (List.get_mem _ _)
    exact fun equal => by simpa only [equal,lt_self_iff_false] using bound
  have differentEntries : winner≠loser := by
    intro equal
    apply differentAtoms
    exact phase.recordInjective endpoints.1 endpoints.2
      (winnerKey.trans ((congrArg Entry.key equal).trans loserKey.symm))
  exact ⟨entry_join_mem winnerMember,loser.joined,entry_join_mem loserMember,
    fun equal => differentEntries (HistMonotone.joined_injective history winnerMember loserMember equal)⟩

/-- Time-crossing uses the exact elementary cut t+1: entries at t are
on the earlier side, matching the accounting update interval. -/
theorem source_cut_ticket_witness (source : Frozen) (first second : Entry) (time : ℕ)
    (firstMember : first∈source.members) (secondMember : second∈source.members)
    (crosses : HistoricalCuts.TimeCrosses time first.joined second.joined) :
    ∃ earlier∈joins source, ∃ later∈joins source, earlier<time+1 ∧ time+1≤later := by
  have firstJoin := entry_join_mem firstMember
  have secondJoin := entry_join_mem secondMember
  unfold HistoricalCuts.TimeCrosses at crosses
  by_cases order : first.joined ≤ second.joined
  · refine ⟨first.joined,firstJoin,second.joined,secondJoin,?_,?_⟩ <;>
      simp only [min_eq_left order,max_eq_right order] at crosses <;> omega
  · have reversed : second.joined≤first.joined := by omega
    refine ⟨second.joined,secondJoin,first.joined,firstJoin,?_,?_⟩ <;>
      simp only [min_eq_right reversed,max_eq_left reversed] at crosses <;> omega

/-- Actual indexed loser records satisfy the injection and deletion-list
provenance required by the shrinking-instance lifetime constructor. -/
theorem InstanceConsolidation.indexed_loser_injective {before after : Option Frozen}
    (phase : InstanceConsolidation before after) :
    Function.Injective (fun event : Fin phase.events.length =>
      phase.record (phase.events.get event).2) := by
  intro first second equal
  apply Phase.actual_loser_injective phase.links phase.uniqueRoots
  exact phase.recordInjective
    (phase.links.event_members (phase.events.get first) (List.get_mem _ _)).2
    (phase.links.event_members (phase.events.get second) (List.get_mem _ _)).2 equal

theorem InstanceConsolidation.indexed_loser_departing {before after : Option Frozen}
    (phase : InstanceConsolidation before after) (event : Fin phase.events.length) :
    phase.record (phase.events.get event).2∈phase.departing :=
  List.mem_map.mpr ⟨phase.events.get event,List.get_mem _ _,rfl⟩

end GreedyMerge.HistoryProcess

#print axioms GreedyMerge.HistoryProcess.SourceConsolidation.winner_ticket_witness
#print axioms GreedyMerge.HistoryProcess.source_cut_ticket_witness
#print axioms GreedyMerge.HistoryProcess.InstanceConsolidation.indexed_loser_injective
