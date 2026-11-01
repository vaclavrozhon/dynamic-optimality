import Greedy.LiteralPhaseSum
import Greedy.HistoricalSnapshots
import Greedy.SparseCreatorSum

/-! Read creator snapshots from literal entries and telescope their shifts. -/

namespace Greedy.LabelSnapshots

open Splay.Rank GreedyForest
open scoped BigOperators

theorem atKey_difference {n : ℕ} (history : LabelHistory.History (External n)) (first last key : ℕ) :
    atKey history last key - atKey history first key =
      (history.changes.map (fun change => ∑ record : External n,
        if key = record.val then joinCoefficient first last change.time * change.delta record else 0)).sum := by
  classical
  by_cases bounded : key < 2*n+1
  · have condition (record : External n) : key = record.val ↔ record = ⟨key, bounded⟩ := by
      constructor
      · intro equal; exact Fin.ext equal.symm
      · intro equal; exact (congrArg Fin.val equal).symm
    simp_rw [condition]
    simp only [atKey, dif_pos bounded, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    exact LabelHistory.difference history ⟨key, bounded⟩ first last
  · have different (record : External n) : key ≠ record.val := by
      intro same
      exact bounded (same ▸ record.isLt)
    simp [atKey, bounded, different]

end Greedy.LabelSnapshots

namespace Greedy.CreatorPhase

open Splay.Tree Splay.Rank GreedyMerge.OrderedBlocks GreedyMerge.Primitives
open GreedyMerge.ActualBlockPartition GreedyMerge.AccessSourceAccounting GreedyForest
open scoped BigOperators

noncomputable def storedCreatorLabel (state : SideState) (key : ℕ) : ℤ := by
  classical
  exact if present : ∃ entry ∈ entries state, entry.key = key then present.choose.creatorLabel else 0

theorem storedCreatorLabel_of_frozen (state : SideState) (source : ℕ) (side : Bool)
    (valid : Valid source side state) (block : Frozen) (member : block ∈ state.shrinking)
    (entry : Entry) (entryMem : entry ∈ block.members) : storedCreatorLabel state entry.key = entry.creatorLabel := by
  have actual := ClosedFamilies.frozen_entry_mem state block member entry entryMem
  have present : ∃ other ∈ entries state, other.key = entry.key := ⟨entry, actual, rfl⟩
  simp only [storedCreatorLabel, dif_pos present]
  have same := List.inj_on_of_nodup_map (ClosedFamilies.valid_keys_unique valid) present.choose_spec.1 actual present.choose_spec.2
  exact congrArg Entry.creatorLabel same

noncomputable def shiftWeight (state : SideState) (block : Frozen) (record : ℕ → ℕ) (edge : ℕ × ℕ) : ℤ :=
  if record edge.1 ∈ blockKeys block ∧ record edge.2 ∈ blockKeys block then
    storedCreatorLabel state (record edge.2) - storedCreatorLabel state (record edge.1) else 0

theorem shiftWeight_telescope {n : ℕ} (history : LabelHistory.History (External n))
    (state : SideState) (block : Frozen) (record : ℕ → ℕ) (source : ℕ) (side : Bool)
    (valid : Valid source side state) (member : block ∈ state.shrinking)
    (snapshots : ∀ entry ∈ block.members, LabelSnapshots.Snapshot history block.creator entry) (edge : ℕ × ℕ) :
    shiftWeight state block record edge = (history.changes.map (fun change => ∑ creator : External n,
      if block.creator = creator.val then weight state block record change.time edge * change.delta creator else 0)).sum := by
  by_cases both : record edge.1 ∈ blockKeys block ∧ record edge.2 ∈ blockKeys block
  · obtain ⟨winner, winnerMem, winnerKey⟩ := List.mem_map.mp both.1
    obtain ⟨loser, loserMem, loserKey⟩ := List.mem_map.mp both.2
    simp only [shiftWeight, weight, if_pos both]
    rw [← winnerKey, ← loserKey,
      storedCreatorLabel_of_frozen state source side valid block member winner winnerMem,
      storedCreatorLabel_of_frozen state source side valid block member loser loserMem,
      (snapshots winner winnerMem).2, (snapshots loser loserMem).2]
    simp_rw [storedJoin_of_frozen state source side valid block member winner winnerMem,
      storedJoin_of_frozen state source side valid block member loser loserMem]
    exact LabelSnapshots.atKey_difference history winner.joined loser.joined block.creator
  · simp [shiftWeight, weight, both]

end Greedy.CreatorPhase
