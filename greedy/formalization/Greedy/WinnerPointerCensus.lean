import Greedy.CreatorMemorySide
import Greedy.MembershipPointer
import Greedy.RunWinnerTickets

/-! Literal membership pointers count the already bounded geometric wins. -/

namespace Greedy.MembershipPointer

open Splay.Rank GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.ActualLinks

noncomputable def atKey {n : ℕ} (pointer : External n → Ticket) (key : ℕ) : Ticket :=
  if bound : key < 2*n+1 then pointer ⟨key, bound⟩ else (0,0)

@[simp] theorem atKey_record {n : ℕ} (pointer : External n → Ticket) (record : External n) :
    atKey pointer record.val = pointer record := by simp [atKey, record.isLt]

theorem frozen_ticket {n : ℕ} (parent : Parents n) (states : States n)
    (sound : SoundFor parent states) (ordered : Ordered states)
    (pointer : External n → Ticket) (synced : Synced pointer states)
    (owner : External n) (side : Bool) (block : Frozen) (member : block ∈ (states owner side).shrinking)
    (key : ℕ) (contains : key ∈ GreedyMerge.ActualBlockPartition.blockKeys block) :
    atKey pointer key = (block.family, GreedyMerge.AccessSourceAccounting.storedJoin (states owner side) key) := by
  obtain ⟨entry, entryMem, keyEq⟩ := List.mem_map.mp contains
  have actual := ClosedFamilies.frozen_entry_mem _ block member entry entryMem
  obtain ⟨record, recordKey, _⟩ := sound owner side entry actual
  rw [← keyEq, GreedyMerge.AccessSourceAccounting.storedJoin_of_frozen _ owner.val side (ordered owner side) block member entry entryMem]
  rw [← recordKey, atKey_record]
  exact synced owner side entry block.family (MembershipStamps.tagged_frozen _ block member entry entryMem) record recordKey

end Greedy.MembershipPointer

namespace Greedy.SourceCensus

open Splay.Tree Splay.Tree.BST Splay.Rank
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.ActualBlockPartition
open GreedyMerge.HeapAllocation GreedyMerge.ActualLinks
open GreedyMerge.Fringe GreedyMerge.Fringe.Schedule GreedyMerge.AccessSourceAccounting
open GreedyMerge.FrozenHistory
open GreedyForest.Phase
open scoped BigOperators
attribute [local instance] Classical.propDecidable

noncomputable def ticketWeight {n : ℕ} (states : HeapSides n) (source : External n)
    (pointer : ℕ → MembershipPointer.Ticket) (ticket : MembershipPointer.Ticket) (edge : ℕ × ℕ) : ℤ :=
  if SameBlockKeys states source edge ∧ pointer edge.1 = ticket then 1 else 0

theorem ticket_side_sum {n lo hi : ℕ} {rank : ℕ → ℕ} {initial : ℕ → ℤ} {record : ℕ → ℕ}
    {tree : BST lo hi} (parent : Parents n) (states : HeapSides n) (source : External n) (side : Bool)
    (sound : SoundFor parent states) (ordered : Ordered states)
    (view : SideView rank initial record tree (states source side))
    (ids : ((states source side).shrinking.map Frozen.id).Nodup)
    (owner : ℕ → ℕ) (projection : Projection (rank ∘ record) owner tree)
    (localOwners : LocalOwners (rank ∘ record) owner lo hi)
    (pointer : External n → MembershipPointer.Ticket) (synced : MembershipPointer.Synced pointer states)
    (ticket : MembershipPointer.Ticket) :
    (∑ block ∈ (states source side).shrinking.toFinset,
      if block.family = ticket.1 then ((WinnerTickets.wins (states source side) block record owner tree ticket.2).card : ℤ) else 0) =
      ∑ i : Fin (schedule owner tree).length,
        ticketWeight states source (MembershipPointer.atKey pointer) ticket
          (record ((schedule owner tree).get i).1, record ((schedule owner tree).get i).2) := by
  classical
  have actualRun := schedule_run (rank ∘ record) owner tree projection localOwners
  have unique := run_events_nodup actualRun (atoms_nodup tree)
  rw [AtomicAccess.indexed_toFinset _ unique
    (fun edge => ticketWeight states source (MembershipPointer.atKey pointer) ticket (record edge.1, record edge.2))]
  have each (block : Frozen) (member : block ∈ (states source side).shrinking.toFinset) :
      (if block.family = ticket.1 then ((WinnerTickets.wins (states source side) block record owner tree ticket.2).card : ℤ) else 0) =
        ∑ edge ∈ (schedule owner tree).toFinset,
          if record edge.1 ∈ blockKeys block ∧ record edge.2 ∈ blockKeys block then
            (if MembershipPointer.atKey pointer (record edge.1) = ticket then (1 : ℤ) else 0) else 0 := by
    rw [show ((WinnerTickets.wins (states source side) block record owner tree ticket.2).card : ℤ) =
      ∑ _edge ∈ WinnerTickets.wins (states source side) block record owner tree ticket.2, (1 : ℤ) by simp]
    simp only [WinnerTickets.wins, Finset.sum_filter]
    trans ∑ edge ∈ (schedule owner tree).toFinset,
      if block.family = ticket.1 then
        (if record edge.1 ∈ blockKeys block ∧ record edge.2 ∈ blockKeys block ∧
          storedJoin (states source side) (record edge.1) = ticket.2 then (1 : ℤ) else 0) else 0
    · by_cases named : block.family = ticket.1 <;> simp [named]
    apply Finset.sum_congr rfl
    intro edge _
    by_cases both : record edge.1 ∈ blockKeys block ∧ record edge.2 ∈ blockKeys block
    · have named := MembershipPointer.frozen_ticket parent states sound ordered pointer synced source side block
        (List.mem_toFinset.mp member) _ both.1
      rw [if_pos both, named]
      rcases ticket with ⟨family, joined⟩
      simp only [Prod.mk.injEq]
      by_cases familyEq : block.family = family <;> by_cases joinedEq : storedJoin (states source side) (record edge.1) = joined <;>
        simp [both, familyEq, joinedEq]
    · simp [both]; tauto
  rw [Finset.sum_congr rfl each, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro edge edgeMem
  rw [sum_internal_value states source side (ordered source) view ids edge.2
    (actualRun.event_members edge (List.mem_toFinset.mp edgeMem)).2 (record edge.1)]
  unfold ticketWeight
  split_ifs <;> simp_all

end Greedy.SourceCensus
