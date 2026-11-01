import Greedy.HistoricalSources
import Greedy.GrowthOverlap
import ForestLedger

/-!
# Nonzero stored creator coefficients lie in actual growth windows

The stored source fragments are covered by the final historical book.
For a nonzero pair coefficient this yields the actual creator and a
positive-length growth window. Constant-time families contribute zero.
-/

namespace Greedy.GrowthJournal

open Splay.Rank GreedyMerge.OrderedBlocks GreedyMerge.Primitives
open GreedyMerge.GrowthBook GreedyMerge.GrowthWindows GreedyForest

theorem OneTime.coefficient_zero {block : Frozen} (constant : OneTime block)
    (winner loser : Entry) (winnerMem : winner ∈ block.members) (loserMem : loser ∈ block.members) (time : ℕ) :
    joinCoefficient winner.joined loser.joined time = 0 := by
  rw [constant winner winnerMem loser loserMem]
  simp [joinCoefficient]

theorem InBatch.between {n : ℕ} {books : HeapBooks n} {block : Frozen}
    (covered : InBatch books block) :
    ∃ creator side, creator.val = block.creator ∧ ∀ entry ∈ block.members,
      growthStart block.family (journal (books creator side)) ≤ entry.joined ∧
        entry.joined ≤ growthEnd block.family (journal (books creator side)) := by
  obtain ⟨creator, side, correct, times⟩ := covered
  exact ⟨creator, side, correct, fun entry member => member_between _ _ (times entry member)⟩

theorem Covered.nonzero_active {n : ℕ} {books : HeapBooks n} {block : Frozen}
    (covered : Covered books block) (winner loser : Entry)
    (winnerMem : winner ∈ block.members) (loserMem : loser ∈ block.members) (time : ℕ)
    (nonzero : joinCoefficient winner.joined loser.joined time ≠ 0) :
    ∃ creator side, creator.val = block.creator ∧
      growthStart block.family (journal (books creator side)) ≤ time ∧
        time < growthEnd block.family (journal (books creator side)) := by
  rcases covered with batch | constant
  · obtain ⟨creator, side, correct, between⟩ := batch.between
    refine ⟨creator, side, correct, ?_⟩
    by_contra inactive
    exact nonzero (joinCoefficient_zero_outside_growth _ _ _ _ _
      (between winner winnerMem) (between loser loserMem) inactive)
  · exact False.elim (nonzero (constant.coefficient_zero winner loser winnerMem loserMem time))

/-- Every nonzero coefficient of a stored source pair names one of the
at-most-two active grower families of its actual creator in the final book. -/
theorem Covered.nonzero_name {n clock next : ℕ} {states : HeapSides n} {books : HeapBooks n}
    (good : HeapGood clock next states books) {block : Frozen} (covered : Covered books block)
    (winner loser : Entry) (winnerMem : winner ∈ block.members) (loserMem : loser ∈ block.members) (time : ℕ)
    (nonzero : joinCoefficient winner.joined loser.joined time ≠ 0) :
    ∃ creator, creator.val = block.creator ∧ block.family ∈ activeNames books creator time (Finset.range next) := by
  classical
  obtain ⟨creator, side, correct, started, active⟩ := covered.nonzero_active winner loser winnerMem loserMem time nonzero
  have extrema := active_extrema (collect block.family (journal (books creator side))) time started active
  obtain ⟨batch, batchMem, family, _⟩ := (collect_member block.family _ _).mp extrema.1
  have below : block.family < next := (good creator side).below block.family (List.mem_map.mpr ⟨batch, batchMem, family⟩)
  exact ⟨creator, correct, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr below, side, started, active⟩⟩

end Greedy.GrowthJournal
