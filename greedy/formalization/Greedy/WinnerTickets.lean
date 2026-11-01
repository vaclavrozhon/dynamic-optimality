import Greedy.ClosedMembership
import Greedy.FamilyPhaseSum
import ActualLifetimeWitnesses

/-! Actual internal wins are indexed by immutable membership join tickets. -/

namespace Greedy.WinnerTickets

open Splay.Tree GreedyMerge.Fringe GreedyMerge.Fringe.Schedule
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.ActualBlockPartition
open GreedyMerge.AccessSourceAccounting GreedyMerge.FrozenHistory

noncomputable def wins {lo hi : ℕ} (state : SideState) (block : Frozen) (record owner : ℕ → ℕ)
    (tree : BST lo hi) (joined : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact (schedule owner tree).toFinset.filter (fun edge => record edge.1 ∈ blockKeys block ∧
    record edge.2 ∈ blockKeys block ∧ storedJoin state (record edge.1) = joined)

theorem witnesses {lo hi : ℕ} (state : SideState) (block : Frozen) (record owner : ℕ → ℕ)
    (tree : BST lo hi) (joined source : ℕ) (side : Bool) (valid : Valid source side state)
    (blockMem : block ∈ state.shrinking) (edge : ℕ × ℕ) (member : edge ∈ wins state block record owner tree joined) :
    ∃ winner loser, winner ∈ block.members ∧ loser ∈ block.members ∧
      winner.key = record edge.1 ∧ loser.key = record edge.2 ∧ winner.joined = joined := by
  obtain ⟨_edgeMem, winnerMem, loserMem, time⟩ := Finset.mem_filter.mp member
  obtain ⟨winner, winnerMem, winnerKey⟩ := List.mem_map.mp winnerMem
  obtain ⟨loser, loserMem, loserKey⟩ := List.mem_map.mp loserMem
  refine ⟨winner, loser, winnerMem, loserMem, winnerKey, loserKey, ?_⟩
  rw [← winnerKey, storedJoin_of_frozen state source side valid block blockMem winner winnerMem] at time
  exact time

theorem count_le_four {lo hi : ℕ} (rank owner : ℕ → ℕ) (tree : BST lo hi)
    (projection : Projection rank owner tree) (localOwners : LocalOwners rank owner lo hi)
    (state : SideState) (block : Frozen) (record : ℕ → ℕ) (joined source : ℕ) (side : Bool)
    (valid : Valid source side state) (blockMem : block ∈ state.shrinking)
    (history : ∃ orientation, HistMonotone orientation block.members)
    (injective : Set.InjOn record {key | key ∈ atoms tree}) :
    (wins state block record owner tree joined).card ≤ 4 := by
  classical
  by_cases empty : (wins state block record owner tree joined).Nonempty
  · obtain ⟨first, firstMem⟩ := empty
    obtain ⟨winner, _loser, winnerMem, _loserMem, winnerKey, _loserKey, winnerTime⟩ :=
      witnesses state block record owner tree joined source side valid blockMem first firstMem
    obtain ⟨orientation, ordered⟩ := history
    have run := schedule_run rank owner tree projection localOwners
    have firstSource := (run.event_members first (List.mem_toFinset.mp (Finset.mem_filter.mp firstMem).1)).1
    have subset : wins state block record owner tree joined ⊆
        (schedule owner tree).toFinset.filter (fun edge => edge.1 = first.1) := by
      intro edge member
      obtain ⟨other, _, otherMem, _, otherKey, _, otherTime⟩ :=
        witnesses state block record owner tree joined source side valid blockMem edge member
      have same := GreedyMerge.HistoryProcess.HistMonotone.joined_injective ordered otherMem winnerMem
        (otherTime.trans winnerTime.symm)
      have eventMem := (Finset.mem_filter.mp member).1
      have endpoint := (run.event_members edge (List.mem_toFinset.mp eventMem)).1
      refine Finset.mem_filter.mpr ⟨eventMem, injective endpoint firstSource ?_⟩
      exact otherKey.symm.trans ((congrArg Entry.key same).trans winnerKey)
    calc
      _ ≤ ((schedule owner tree).toFinset.filter (fun edge => edge.1 = first.1)).card := Finset.card_le_card subset
      _ = ((schedule owner tree).filter (fun edge => edge.1 == first.1)).toFinset.card := by simp only [List.toFinset_filter, beq_iff_eq]
      _ ≤ ((schedule owner tree).filter (fun edge => edge.1 == first.1)).length := List.toFinset_card_le _
      _ ≤ 4 := by
        rw [← List.countP_eq_length_filter]
        exact schedule_winner_count_le_four rank owner tree first.1 projection localOwners
  · have zero : wins state block record owner tree joined = ∅ := Finset.not_nonempty_iff_eq_empty.mp empty
    simp [zero]

theorem isolated_no_wins {lo hi : ℕ} (rank owner : ℕ → ℕ) (tree : BST lo hi)
    (projection : Projection rank owner tree) (localOwners : LocalOwners rank owner lo hi)
    (state : SideState) (block : Frozen) (record : ℕ → ℕ) (joined source : ℕ) (side : Bool)
    (valid : Valid source side state) (blockMem : block ∈ state.shrinking)
    (history : ∃ orientation, HistMonotone orientation block.members)
    (injective : Set.InjOn record {key | key ∈ atoms tree}) (isolated : ClosedFamilies.Isolated joined block) :
    wins state block record owner tree joined = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro edge member
  obtain ⟨winner, loser, winnerMem, loserMem, winnerKey, loserKey, winnerTime⟩ :=
    witnesses state block record owner tree joined source side valid blockMem edge member
  have winnerJoin : joined ∈ joins block := winnerTime ▸ GreedyMerge.HistoryProcess.entry_join_mem winnerMem
  have loserTime : loser.joined = joined := Finset.mem_singleton.mp (isolated winnerJoin (GreedyMerge.HistoryProcess.entry_join_mem loserMem))
  obtain ⟨orientation, ordered⟩ := history
  have same := GreedyMerge.HistoryProcess.HistMonotone.joined_injective ordered winnerMem loserMem (winnerTime.trans loserTime.symm)
  have run := schedule_run rank owner tree projection localOwners
  have eventMem := List.mem_toFinset.mp (Finset.mem_filter.mp member).1
  have endpoints := run.event_members edge eventMem
  have sameAtom := injective endpoints.1 endpoints.2 (winnerKey.symm.trans ((congrArg Entry.key same).trans loserKey))
  have strict := GreedyMerge.MappedConsolidation.run_event_rank_lt run edge eventMem
  rw [sameAtom] at strict
  exact (Nat.lt_irrefl _) strict

end Greedy.WinnerTickets
